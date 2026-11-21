import{mkdirSync,readdirSync,readFileSync,writeFileSync}from'node:fs';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output',X=[0,0,-1,1],Y=[-1,1,0,0];
function solve(t){
const L=t.split('\n'),W=Math.max(...L.map(r=>r.length)),H=L.length,F=[],G=[];
let B=[],P=0,x=0,y=0;
for(const c of t){if(c==='\n'){x=0;y++;continue}if(c!=='#'){let i=y*W+x;F[i]=1;G[i]='.+*'.includes(c);if('$*'.includes(c))B.push(i);if('@+'.includes(c))P=i}x++}
const py=P/W|0,ib=(a,b)=>a>=0&&b>=0&&a<W&&b<H;
const bfs=(s,f,b)=>{const m=new Map([[s,[-1,0,0]]]),q=[s];for(let h=0;h<q.length;h++){let c=q[h],v=m.get(c);for(let k=0;k<4;k++){let a=c%W+X[k],d=(c/W|0)+Y[k];if(ib(a,d)){let n=d*W+a;if(f[n]&&!b.has(n)&&!m.has(n)){m.set(n,[c,k,v[2]+1]);q.push(n)}}}}return m};
const wlk=(a,b,f,l)=>{if(a===b)return'';const m=bfs(a,f,l);if(!m.has(b))return null;let s='',c=b;while(c!==a){let v=m.get(c);s='udlr'[v[1]]+s;c=v[0]}return s};
const bl=new Set();for(let a=0;a<W;a++)bl.add(py*W+a);
const sn=new Set(),rm=[];
for(let i=0;i<F.length;i++){if((i/W|0)===py||!F[i]||sn.has(i))continue;let cs=[...bfs(i,F,bl).keys()];cs.forEach(c=>sn.add(c));rm.push(cs)}
const room=(cs,b0,e,dr,nx)=>{
const rs=new Set(cs),fl=[];for(const c of cs)fl[c]=1;fl[e]=1;
const gl=cs.filter(c=>G[c]),ds=gl.map(g=>bfs(g,fl,new Set()));
const hr=bs=>{let b=1/0;const r=(i,a,u)=>{if(a>=b)return;if(i===bs.length){b=a;return}for(let j=0;j<gl.length;j++)if(!(u>>j&1)){let v=ds[j].get(bs[i]);if(v)r(i+1,a+v[2],u|1<<j)}};r(0,0,0);return b};
const dl=bs=>{const s=new Set(bs);for(const b of bs){if(G[b])continue;let x=b%W,y=b/W|0;
let U=!ib(x,y-1)||!fl[(y-1)*W+x],N=!ib(x,y+1)||!fl[(y+1)*W+x],L=!ib(x-1,y)||!fl[y*W+x-1],T=!ib(x+1,y)||!fl[y*W+x+1];
if((U||N)&&(L||T))return 1;
for(const[ox,oy]of[[-1,-1],[0,-1],[-1,0],[0,0]]){let z=0;for(let a=0;a<4;a++){let cx=x+ox+(a&1),cy=y+oy+(a>>1);if(ib(cx,cy)){let c=cy*W+cx;if(G[c]||(fl[c]&&!s.has(c)))z=1}}if(!z)return 1}}
return 0};
const ky=(p,bs)=>String.fromCharCode(p,...bs);
const cn=(p,bs)=>{let m=1/0;for(const c of bfs(p,fl,new Set(bs)).keys())if(c<m)m=c;return m};
let bs=[...b0].sort((a,b)=>a-b),s,xp=0,n=0;
const A=[bs],J=[cn(e,bs)],U=[0],V=[-1],Z=[0],be=new Map([[ky(J[0],bs),0]]),Bk=[];let mf=0;
const ph=(f,i)=>{(Bk[f]??=[]).push(i);if(f<mf)mf=f;n++};
const pp=()=>{while(mf<Bk.length&&!(Bk[mf]||[]).length)mf++;if(mf>=Bk.length)return -1;n--;return Bk[mf].pop()};
if(hr(bs)===1/0||dl(bs))return null;
ph(hr(bs),0);
while(n&&xp<1e6&&(s=pp())>=0){
bs=A[s];let p=J[s],g=U[s];
if(be.get(ky(p,bs))!==g)continue;
if(bs.every(b=>G[b])){if(!nx||bfs(p,fl,new Set(bs)).has(dr)){let ps=[];for(let q=s;q>0;q=V[q])ps.push(Z[q]);return ps.reverse()}}
xp++;
let rg=bfs(p,fl,new Set(bs)),st=new Set(bs);
for(let bi=0;bi<bs.length;bi++){let b=bs[bi];
for(let k=0;k<4;k++){let x=b%W+X[k],y=(b/W|0)+Y[k];if(!ib(x,y))continue;let o=y*W+x,q=b-Y[k]*W-X[k];
if(!fl[o]||st.has(o)||!rg.has(q))continue;
let nb=bs.slice();nb[bi]=o;nb.sort((a,c)=>a-c);
if(dl(nb))continue;let h=hr(nb);if(h===1/0)continue;
let np=cn(b,nb),kk=ky(np,nb),w=be.get(kk);
if(w!==undefined&&w<=g+1)continue;
let z=A.length;A.push(nb);J.push(np);U.push(g+1);V.push(s);Z.push(b*4+k);be.set(kk,g+1);ph(g+1+h,z)}}}
return null};
let m='',c=P,d=[];
const go=(cs,nx)=>{
let b0=cs.filter(c=>B.includes(c));
let dr=cs.find(c=>{let x=c%W,y=c/W|0;for(let k=0;k<4;k++){let a=x+X[k],b=y+Y[k];if(b===py&&ib(a,b)&&F[b*W+a])return 1}return 0});
if(dr===undefined)return 0;
let e=py*W+dr%W,ps=room(cs,b0,e,dr,nx);
if(!ps)return 0;
let fl=[];for(const c of cs)fl[c]=1;fl[e]=1;
let w0=wlk(c,e,F,new Set(B));if(w0===null)return 0;
m+=w0;c=e;
let cb=[...b0].sort((a,b)=>a-b);
for(const z of ps){let fr=z>>2,k=z&3,q=fr-Y[k]*W-X[k];
let wk=wlk(c,q,fl,new Set(cb));if(wk===null)return 0;
m+=wk+'udlr'[k];let o=fr+Y[k]*W+X[k];
cb=cb.map(b=>b===fr?o:b).sort((a,b)=>a-b);c=fr;B=B.map(b=>b===fr?o:b)}
return 1};
for(const cs of rm)if(!go(cs,1))d.push(cs);
for(const cs of d)if(!go(cs,0))return '';
return m}
for(const id of readdirSync(I).sort()){const s=solve(readFileSync(I+'/'+id+'/level.txt','utf8'));mkdirSync(O+'/'+id,{recursive:true});writeFileSync(O+'/'+id+'/solution.txt',s+'\n')}
