import{mkdirSync,readdirSync,readFileSync,writeFileSync}from'node:fs';
import{join}from'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const D=[[0,-1],[0,1],[-1,0],[1,0]],L='udlr';
function solve(t){
 const R=t.split('\n').filter(r=>r),H=R.length,W=Math.max(...R.map(r=>r.length));
 const F=[],Y=[];let B=[],P=0;
 R.forEach((r,y)=>{for(let x=0;x<W;x++){let c=r[x]||'#',i=y*W+x;F[i]=c!='#';Y[i]='.*+'.includes(c);if('$*'.includes(c))B.push(i);if('@+'.includes(c))P=i}});
 const py=P/W|0,ib=(x,y)=>x>=0&&y>=0&&x<W&&y<H;
 const bfs=(s,fl,bl)=>{const m=new Map([[s,-1]]),q=[s];for(let h=0;h<q.length;h++){let c=q[h];for(let k=0;k<4;k++){let x=c%W+D[k][0],y=(c/W|0)+D[k][1];if(ib(x,y)){let n=y*W+x;if(fl[n]&&!bl.has(n)&&!m.has(n)){m.set(n,c);q.push(n)}}}}return m};
 const walk=(a,b,fl,bl)=>{if(a===b)return'';const m=bfs(a,fl,bl);if(!m.has(b))return null;let s='',c=b;while(c!==a){let p=m.get(c),dx=c%W-p%W,dy=(c/W|0)-(p/W|0);s=(dy<0?'u':dy>0?'d':dx<0?'l':'r')+s;c=p}return s};
 const seen=new Set(),rooms=[];
 for(let y=0;y<H;y++)for(let x=0;x<W;x++){let i=y*W+x;if(y===py||!F[i]||seen.has(i))continue;let cs=[],q=[i];seen.add(i);while(q.length){let c=q.pop();cs.push(c);for(let k=0;k<4;k++){let nx=c%W+D[k][0],ny=(c/W|0)+D[k][1];if(ny!==py&&ib(nx,ny)){let n=ny*W+nx;if(F[n]&&!seen.has(n)){seen.add(n);q.push(n)}}}}rooms.push(cs)}
 const room=(cs,b0,e,dr,nx)=>{
  const rs=new Set(cs),fl=[];for(const c of cs)fl[c]=1;fl[e]=1;
  const gl=cs.filter(c=>Y[c]);
  const ds=[];for(const s of cs){const d=new Array(W*H).fill(1/0);d[s]=0;const q=[s];for(let h=0;h<q.length;h++){let c=q[h];for(let k=0;k<4;k++){let x=c%W+D[k][0],y=(c/W|0)+D[k][1];if(ib(x,y)){let n=y*W+x;if(rs.has(n)&&d[n]>d[c]+1){d[n]=d[c]+1;q.push(n)}}}}ds[s]=d}
  const heur=bs=>{let b=1/0;const r=(i,a,u)=>{if(a>=b)return;if(i===bs.length){b=a;return}for(let j=0;j<gl.length;j++)if(!(u>>j&1)){let d=ds[bs[i]][gl[j]];if(d<1/0)r(i+1,a+d,u|1<<j)}};r(0,0,0);return b};
  const dl=bs=>{const s=new Set(bs);for(const b of bs){if(Y[b])continue;let x=b%W,y=b/W|0;
   let U=!ib(x,y-1)||!fl[(y-1)*W+x],N=!ib(x,y+1)||!fl[(y+1)*W+x],Lf=!ib(x-1,y)||!fl[y*W+x-1],Rt=!ib(x+1,y)||!fl[y*W+x+1];
   if((U||N)&&(Lf||Rt))return 1;
   for(const[ox,oy]of[[-1,-1],[0,-1],[-1,0],[0,0]]){let bad=0;for(let a=0;a<4;a++){let cx=x+ox+(a&1),cy=y+oy+(a>>1);if(ib(cx,cy)){let c=cy*W+cx;if(Y[c]||(fl[c]&&!s.has(c)))bad=1}}if(!bad)return 1}}
  return 0};
  const key=(p,bs)=>String.fromCharCode(p,...bs);
  const can=(p,bs)=>{let m=1/0;for(const c of bfs(p,fl,new Set(bs)).keys())if(c<m)m=c;return m};
  let bs=[...b0].sort((a,b)=>a-b);
  const NB=[bs],NP=[can(e,bs)],NG=[0],PA=[-1],PU=[[0,0]],be=new Map([[key(NP[0],bs),0]]),Hp=[];
  const push=e=>{let i=Hp.length;Hp.push(e);while(i){let p=i-1>>1;if(Hp[p][0]<=e[0])break;Hp[i]=Hp[p];i=p}Hp[i]=e};
  const pop=()=>{let t=Hp[0],l=Hp.pop();if(Hp.length){let i=0;for(;;){let c=2*i+1;if(c>=Hp.length)break;if(c+1<Hp.length&&Hp[c+1][0]<Hp[c][0])c++;if(Hp[c][0]>=l[0])break;Hp[i]=Hp[c];i=c}Hp[i]=l}return t};
  if(heur(bs)===1/0||dl(bs))return null;
  push([heur(bs),0]);
  let xp=0;
  while(Hp.length&&xp<1e6){
   let[,s]=pop();bs=NB[s];let p=NP[s],g=NG[s];
   if(be.get(key(p,bs))!==g)continue;
   if(bs.every(b=>Y[b])){if(!nx||bfs(p,fl,new Set(bs)).has(dr)){let ps=[];for(let n=s;n>0;n=PA[n])ps.push(PU[n]);return ps.reverse()}}
   xp++;
   let rg=bfs(p,fl,new Set(bs)),st=new Set(bs);
   for(let bi=0;bi<bs.length;bi++){let b=bs[bi];
    for(let k=0;k<4;k++){let x=b%W+D[k][0],y=(b/W|0)+D[k][1];if(!ib(x,y))continue;let n=y*W+x,ph=(b/W|0)*W+b%W-D[k][1]*W-D[k][0];
     if(!fl[n]||st.has(n)||!rg.has(ph))continue;
     let nb=bs.slice();nb[bi]=n;nb.sort((a,c)=>a-c);
     if(dl(nb))continue;let h=heur(nb);if(h===1/0)continue;
     let np=can(b,nb),kk=key(np,nb),o=be.get(kk);
     if(o!==undefined&&o<=g+1)continue;
     let idx=NB.length;NB.push(nb);NP.push(np);NG.push(g+1);PA.push(s);PU.push([b,k]);be.set(kk,g+1);push([g+1+h,idx])}}}
  return null};
 let mv='',cp=P,AB=B,def=[];
 const doRoom=(cs,nx)=>{
  let b0=cs.filter(c=>AB.includes(c));
  let drs=cs.filter(c=>{let x=c%W,y=c/W|0;for(let k=0;k<4;k++){let nx2=x+D[k][0],ny=y+D[k][1];if(ny===py&&ib(nx2,ny)&&F[ny*W+nx2])return 1}return 0});
  if(!drs.length)return 0;
  let dr=drs[0],e=(py)*W+dr%W;
  let ps=room(cs,b0,e,dr,nx);
  if(!ps)return 0;
  let fl=[];for(const c of cs)fl[c]=1;fl[e]=1;
  let w0=walk(cp,e,F,new Set(AB));if(w0===null)return 0;
  mv+=w0;cp=e;
  let cb=[...b0].sort((a,b)=>a-b);
  for(let[fr,k]of ps){let ph=(fr/W|0)*W+fr%W-D[k][1]*W-D[k][0];
   let wk=walk(cp,ph,fl,new Set(cb));if(wk===null)return 0;
   mv+=wk+L[k];let n=(fr/W|0)*W+fr%W+D[k][1]*W+D[k][0];
   cb=cb.map(b=>b===fr?n:b).sort((a,b)=>a-b);cp=fr;AB=AB.map(b=>b===fr?n:b)}
  return 1};
 for(const cs of rooms)if(!doRoom(cs,1))def.push(cs);
 for(const cs of def)if(!doRoom(cs,0))return '';
 return mv}
for(const id of readdirSync(I).sort()){
 const mv=solve(readFileSync(join(I,id,'level.txt'),'utf8'));
 mkdirSync(join(O,id),{recursive:true});
 writeFileSync(join(O,id,'solution.txt'),mv+'\n')}
