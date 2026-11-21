// Sokoban solver: push-optimal per room (rooms are independent: a box pushed
// into the hallway can never come back, so the level optimum is the sum of the
// room optima). Each room is solved with push-A* + min-assignment heuristic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// up, down, left, right
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const LETTER = ['u', 'd', 'l', 'r'];
// Expansion budget per room, counted in work (never the wall clock), so two
// runs always agree.
const EXPANSIONS = 1_000_000;

type Push = { from: number; dir: number };

function solve(text: string): string {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const open: boolean[] = [];
  const isGoal: boolean[] = [];
  let allBoxes: number[] = [];
  let player = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) {
      const ch = row[x] ?? '#';
      const i = y * w + x;
      open[i] = ch !== '#';
      isGoal[i] = '.*+'.includes(ch);
      if ('$*'.includes(ch)) allBoxes.push(i);
      if ('@+'.includes(ch)) player = i;
    }
  });
  const py = Math.floor(player / w);
  const at = (x: number, y: number): number => y * w + x;
  const inside = (x: number, y: number): boolean => x >= 0 && y >= 0 && x < w && y < h;

  // Rooms: connected components of open cells off the hallway row.
  const seen = new Set<number>();
  const rooms: number[][] = [];
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = at(x, y);
      if (y === py || !open[i] || seen.has(i)) continue;
      const cells: number[] = [];
      const q = [i];
      seen.add(i);
      while (q.length > 0) {
        const c = q.pop()!;
        cells.push(c);
        for (let d = 0; d < 4; d++) {
          const nx = (c % w) + DX[d]!;
          const ny = Math.floor(c / w) + DY[d]!;
          if (ny === py || !inside(nx, ny)) continue;
          const n = at(nx, ny);
          if (open[n] && !seen.has(n)) {
            seen.add(n);
            q.push(n);
          }
        }
      }
      rooms.push(cells);
    }
  }

  // BFS walk on a floor set (boolean array), blocked by `blocked` cells.
  // Returns the move string from `from` to `to`, or null if unreachable.
  const walk = (from: number, to: number, floor: boolean[], blocked: Set<number>): string | null => {
    if (from === to) return '';
    const prev = new Map<number, number>();
    const prevDir = new Map<number, number>();
    const q = [from];
    prev.set(from, -1);
    for (let head = 0; head < q.length; head++) {
      const c = q[head]!;
      for (let d = 0; d < 4; d++) {
        const nx = (c % w) + DX[d]!;
        const ny = Math.floor(c / w) + DY[d]!;
        if (!inside(nx, ny)) continue;
        const n = at(nx, ny);
        if (!floor[n] || blocked.has(n) || prev.has(n)) continue;
        prev.set(n, c);
        prevDir.set(n, d);
        if (n === to) {
          let moves = '';
          let cur = n;
          while (cur !== from) {
            moves = LETTER[prevDir.get(cur)!]! + moves;
            cur = prev.get(cur)!;
          }
          return moves;
        }
        q.push(n);
      }
    }
    return null;
  };

  // Flood fill from `from` over `floor` minus `blocked`; returns the set.
  const reach = (from: number, floor: boolean[], blocked: Set<number>): Set<number> => {
    const out = new Set<number>([from]);
    const q = [from];
    for (let head = 0; head < q.length; head++) {
      const c = q[head]!;
      for (let d = 0; d < 4; d++) {
        const nx = (c % w) + DX[d]!;
        const ny = Math.floor(c / w) + DY[d]!;
        if (!inside(nx, ny)) continue;
        const n = at(nx, ny);
        if (floor[n] && !blocked.has(n) && !out.has(n)) {
          out.add(n);
          q.push(n);
        }
      }
    }
    return out;
  };

  // Solve one room with push-A*. `entry` is the hallway cell in front of the
  // door; the player starts there and may stand on it. Boxes may only move
  // inside the room. Returns the push list, or null.
  const solveRoom = (cells: number[], boxes0: number[], entry: number, door: number, needExit: boolean): Push[] | null => {
    const inRoom = new Set(cells);
    const floor: boolean[] = [];
    for (const c of cells) floor[c] = true;
    floor[entry] = true;
    const goals = cells.filter((c) => isGoal[c]);
    const blocked = (c: number): boolean => !floor[c];
    // All-pairs BFS distances over room cells (no boxes): the heuristic base.
    const dist = new Map<number, Map<number, number>>();
    for (const s of cells) {
      const d = new Map<number, number>([[s, 0]]);
      const q = [s];
      for (let head = 0; head < q.length; head++) {
        const c = q[head]!;
        for (let k = 0; k < 4; k++) {
          const nx = (c % w) + DX[k]!;
          const ny = Math.floor(c / w) + DY[k]!;
          if (!inside(nx, ny)) continue;
          const n = at(nx, ny);
          if (inRoom.has(n) && !d.has(n)) {
            d.set(n, d.get(c)! + 1);
            q.push(n);
          }
        }
      }
      dist.set(s, d);
    }
    // Min-assignment heuristic over all box->goal permutations (<= 4! = 24).
    const heuristic = (bs: number[]): number => {
      let best = Infinity;
      const used = new Array<boolean>(goals.length).fill(false);
      const go = (i: number, acc: number): void => {
        if (acc >= best) return;
        if (i === bs.length) {
          best = acc;
          return;
        }
        for (let j = 0; j < goals.length; j++) {
          if (used[j]) continue;
          const d = dist.get(bs[i]!)!.get(goals[j]!);
          if (d === undefined) continue;
          used[j] = true;
          go(i + 1, acc + d);
          used[j] = false;
        }
      };
      go(0, 0);
      return best;
    };
    // Sound deadlock checks: a box that can never move again.
    const deadlocked = (bs: number[]): boolean => {
      const set = new Set(bs);
      for (const b of bs) {
        if (isGoal[b]) continue;
        const x = b % w;
        const y = Math.floor(b / w);
        // Corner: two perpendicular neighbours blocked.
        const up = !inside(x, y - 1) || blocked(at(x, y - 1));
        const down = !inside(x, y + 1) || blocked(at(x, y + 1));
        const left = !inside(x - 1, y) || blocked(at(x - 1, y));
        const right = !inside(x + 1, y) || blocked(at(x + 1, y));
        if ((up || down) && (left || right)) return true;
        // 2x2 block of boxes/walls with no goal inside.
        for (const [ox, oy] of [[0, 0], [-1, 0], [0, -1], [-1, -1]] as const) {
          const sq = [at(x + ox, y + oy), at(x + ox + 1, y + oy), at(x + ox, y + oy + 1), at(x + ox + 1, y + oy + 1)];
          if (sq.some((c) => isGoal[c])) continue;
          if (sq.every((c) => set.has(c) || !inside(c % w, Math.floor(c / w)) || blocked(c))) return true;
        }
      }
      return false;
    };
    const canon = (p: number, bs: number[]): number => {
      let m = Infinity;
      for (const c of reach(p, floor, new Set(bs))) if (c < m) m = c;
      return m;
    };
    const keyOf = (p: number, bs: number[]): string => String.fromCharCode(p, ...bs);
    const startBoxes = [...boxes0].sort((a, b) => a - b);
    const startPlayer = canon(entry, startBoxes);
    // A* nodes.
    const nBoxes: number[][] = [startBoxes];
    const nPlayer: number[] = [startPlayer];
    const nG: number[] = [0];
    const nParent: number[] = [-1];
    const nPush: Push[] = [{ from: -1, dir: -1 }];
    const best = new Map<string, number>([[keyOf(startPlayer, startBoxes), 0]]);
    // Heap of [f, seq, node]; smaller f first, then earlier seq.
    const heap: [number, number, number][] = [];
    let seq = 0;
    const heapLess = (a: [number, number, number], b: [number, number, number]): boolean =>
      a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
    const heapPush = (e: [number, number, number]): void => {
      let i = heap.length;
      heap.push(e);
      while (i > 0) {
        const p = (i - 1) >> 1;
        if (!heapLess(heap[i]!, heap[p]!)) break;
        [heap[i], heap[p]] = [heap[p]!, heap[i]!];
        i = p;
      }
    };
    const heapPop = (): [number, number, number] => {
      const top = heap[0]!;
      const last = heap.pop()!;
      if (heap.length > 0) {
        heap[0] = last;
        for (let i = 0; ; ) {
          let c = 2 * i + 1;
          if (c >= heap.length) break;
          if (c + 1 < heap.length && heapLess(heap[c + 1]!, heap[c]!)) c++;
          if (!heapLess(heap[c]!, heap[i]!)) break;
          [heap[i], heap[c]] = [heap[c]!, heap[i]!];
          i = c;
        }
      }
      return top;
    };
    const h0 = heuristic(startBoxes);
    if (h0 === Infinity || deadlocked(startBoxes)) return null;
    heapPush([h0, seq++, 0]);
    let expanded = 0;
    while (heap.length > 0 && expanded < EXPANSIONS) {
      const [, , s] = heapPop();
      const bs = nBoxes[s]!;
      const p = nPlayer[s]!;
      const g = nG[s]!;
      if (best.get(keyOf(p, bs)) !== g) continue;
      if (bs.every((b) => isGoal[b])) {
        if (!needExit || reach(p, floor, new Set(bs)).has(door)) {
          const pushes: Push[] = [];
          for (let t = s; t > 0; t = nParent[t]!) pushes.push(nPush[t]!);
          pushes.reverse();
          return pushes;
        }
      }
      expanded++;
      const region = reach(p, floor, new Set(bs));
      const boxSet = new Set(bs);
      for (let bi = 0; bi < bs.length; bi++) {
        const b = bs[bi]!;
        for (let d = 0; d < 4; d++) {
          const nx = (b % w) + DX[d]!;
          const ny = Math.floor(b / w) + DY[d]!;
          if (!inside(nx, ny)) continue;
          const t = at(nx, ny);
          const pusher = at((b % w) - DX[d]!, Math.floor(b / w) - DY[d]!);
          if (!floor[t] || boxSet.has(t) || !region.has(pusher)) continue;
          const nb = bs.slice();
          nb[bi] = t;
          nb.sort((a, b2) => a - b2);
          if (deadlocked(nb)) continue;
          const h = heuristic(nb);
          if (h === Infinity) continue;
          const np = canon(b, nb);
          const k = keyOf(np, nb);
          if (best.has(k)) continue;
          const idx = nBoxes.length;
          nBoxes.push(nb);
          nPlayer.push(np);
          nG.push(g + 1);
          nParent.push(s);
          nPush.push({ from: b, dir: d });
          best.set(k, g + 1);
          heapPush([g + 1 + h, seq++, idx]);
        }
      }
    }
    return null;
  };

  // Solve rooms in scan order; a room that cannot be solved with an exit is
  // deferred to the end (solved without needing an exit).
  let moves = '';
  let curPlayer = player;
  const deferred: number[][] = [];
  const doRoom = (cells: number[], needExit: boolean): boolean => {
    const boxes0 = cells.filter((c) => allBoxes.includes(c));
    const doors = cells.filter((c) => {
      const x = c % w;
      const y = Math.floor(c / w);
      for (let d = 0; d < 4; d++) {
        const nx = x + DX[d]!;
        const ny = y + DY[d]!;
        if (ny === py && inside(nx, ny) && open[at(nx, ny)]) return true;
      }
      return false;
    });
    if (doors.length === 0) return false;
    const door = doors[0]!;
    const entry = at(door % w, py);
    const pushes = solveRoom(cells, boxes0, entry, door, needExit);
    if (pushes === null) return false;
    // Replay the pushes into walks + push letters.
    const roomFloor: boolean[] = [];
    for (const c of cells) roomFloor[c] = true;
    roomFloor[entry] = true;
    // Walk from the current player to this room's entry first.
    const w0 = walk(curPlayer, entry, open, new Set(allBoxes));
    if (w0 === null) return false;
    moves += w0;
    curPlayer = entry;
    let curBoxes = [...boxes0].sort((a, b) => a - b);
    for (const { from, dir } of pushes) {
      const pusher = at((from % w) - DX[dir]!, Math.floor(from / w) - DY[dir]!);
      const wk = walk(curPlayer, pusher, roomFloor, new Set(curBoxes));
      if (wk === null) return false;
      moves += wk + LETTER[dir]!;
      const t = at((from % w) + DX[dir]!, Math.floor(from / w) + DY[dir]!);
      curBoxes = curBoxes.map((b) => (b === from ? t : b)).sort((a, b) => a - b);
      curPlayer = from;
      allBoxes = allBoxes.map((b) => (b === from ? t : b));
    }
    return true;
  };
  for (const cells of rooms) {
    if (!doRoom(cells, true)) deferred.push(cells);
  }
  for (const cells of deferred) {
    if (!doRoom(cells, false)) return '';
  }
  return moves;
}

for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
