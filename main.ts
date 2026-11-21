import {mkdirSync,readdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const D=[[0,-1,'u','U'],[0,1,'d','D'],[-1,0,'l','L'],[1,0,'r','R']];
const CAP=200000,CAP2=600000;
function parse(t){const r=t.split('\n').filter(x=>x.length),h=r.length,w=Math.max(...r.map(x=>x.length)),wall=new Uint8Array(w*h).fill(1),goals=[],boxes=[];let player=-1;r.forEach((row,y)=>{for(let x=0;x<row.length;x++){const i=y*w+x,c=row[x];if(c==='#')continue;wall[i]=0;if('.*+'.includes(c))goals.push(i);if('$*'.includes(c))boxes.push(i);if('@+'.includes(c))player=i;}});for(let y=0;y<h;y++)for(let x=0;x<w;x++)if(!x||!y||x===w-1||y===h-1)wall[y*w+x]=1;return{w,h,wall,goals,boxes:boxes.sort((a,b)=>a-b),player};}
function liveSq(wall,w,goals){const n=wall.length,lv=new Uint8Array(n),q=[...goals];for(const g of goals)lv[g]=1;for(let i=0;i<q.length;i++){const x=q[i];for(let k=0;k<4;k++){const d=D[k][1]*w+D[k][0],y=x-d;if(!wall[y]&&!wall[y-d]&&!lv[y]){lv[y]=1;q.push(y);}}}return lv;}
function perms(n){if(n<2)return[[0]];const r=[];for(const p of perms(n-1))for(let i=0;i<n;i++){const q=p.slice();q.splice(i,0,n-1);r.push(q);}return r;}
function astar(L,cap){
 const{w,wall,goals,boxes,player}=L,size=wall.length,nb=boxes.length;
 const goal=new Uint8Array(size);for(const g of goals)goal[g]=1;
 const lv=liveSq(wall,w,goals);
 if(boxes.some(b=>!lv[b]))return null;
 const dg=goals.map(g=>{const d=new Int32Array(size).fill(-1);d[g]=0;const q=[g];for(let i=0;i<q.length;i++){const p=q[i];for(let k=0;k<4;k++){const n2=p+D[k][1]*w+D[k][0];if(!wall[n2]&&d[n2]<0){d[n2]=d[p]+1;q.push(n2);}}}return d;});
 const pm=nb<=5?perms(nb):null;
 const heur=bs=>{if(!pm){let s=0;for(const b of bs){let m=1e9;for(let g=0;g<goals.length;g++){const v=dg[g][b];if(v>=0&&v<m)m=v;}if(m>=1e9)return 1e9;s+=m;}return s;}let m=1e9;for(const p of pm){let s=0;for(let i=0;i<nb;i++){const v=dg[p[i]][bs[i]];if(v<0){s=1e9;break;}s+=v;}if(s<m)m=s;}return m;};
 const occ=new Uint8Array(size),rg=new Int32Array(size),st=new Int32Array(size);let tk=0,cur=0;
 const flood=from=>{cur=++tk;let low=from,n=0;st[n++]=from;rg[from]=cur;while(n>0){const p=st[--n];if(p<low)low=p;for(let k=0;k<4;k++){const q=p+(k===0?-w:k===1?w:k===2?-1:1);if(!wall[q]&&!occ[q]&&rg[q]!==cur){rg[q]=cur;st[n++]=q;}}}return low;};
 const frozen=t=>{for(const a of[t,t-1,t-w,t-w-1]){const b=a+1,c=a+w,d=c+1;if(!(wall[a]||occ[a])||!(wall[b]||occ[b])||!(wall[c]||occ[c])||!(wall[d]||occ[d]))continue;if((occ[a]&&!goal[a])||(occ[b]&&!goal[b])||(occ[c]&&!goal[c])||(occ[d]&&!goal[d]))return true;}return false;};
 const walk=(from,to,bx)=>{if(from===to)return'';const oc=new Uint8Array(size);for(const b of bx)oc[b]=1;const prev=new Int32Array(size).fill(-1),how=new Array(size),q=[from];prev[from]=from;for(let i=0;i<q.length;i++){const p=q[i];if(p===to)break;for(let k=0;k<4;k++){const n2=p+D[k][1]*w+D[k][0];if(wall[n2]||oc[n2]||prev[n2]>=0)continue;prev[n2]=p;how[n2]=D[k][2];q.push(n2);}}if(prev[to]<0)throw new Error('walk');let s='';for(let p=to;p!==from;p=prev[p])s=how[p]+s;return s;};
 const lt=(a,b)=>a[0]<b[0]||(a[0]===b[0]&&(a[1]<b[1]||(a[1]===b[1]&&a[2]<b[2])));
 const hp=[];
 const hpush=e=>{let i=hp.length;hp.push(e);while(i>0){const p=(i-1)>>1;if(!lt(hp[i],hp[p]))break;const t=hp[i];hp[i]=hp[p];hp[p]=t;i=p;}};
 const hpop=()=>{const top=hp[0],last=hp.pop();if(hp.length){hp[0]=last;for(let i=0;;){let c=2*i+1;if(c>=hp.length)break;if(c+1<hp.length&&lt(hp[c+1],hp[c]))c++;if(!lt(hp[c],hp[i]))break;const t=hp[i];hp[i]=hp[c];hp[c]=t;i=c;}}return top;};
 const bxs=[boxes.slice()],pls=[player],par=[-1],psh=[null],gs=[0];
 const seen=new Map();
 const h0=heur(boxes);if(h0>=1e9)return null;
 let seq=0;
 seen.set(flood(player)+':'+boxes.join(','),0);
 hpush([h0,h0,seq++,0]);
 let exp=0;
 while(hp.length){
  const top=hpop(),s=top[3],g=gs[s];
  const bs=bxs[s];
  if(bs.every(b=>goal[b])){
   const path=[];for(let x=s;x>0;x=par[x])path.push(x);path.reverse();
   let moves='',pl=player,bx=boxes.slice();
   for(const x of path){const[from,to,k]=psh[x],d=D[k][1]*w+D[k][0];moves+=walk(pl,from-d,bx);moves+=D[k][3];pl=from;const bi=bx.indexOf(from);bx[bi]=to;bx.sort((a,b)=>a-b);}
   return{pushes:path.length,moves};
  }
  if(++exp>cap)return null;
  for(const b of bs)occ[b]=1;
  flood(pls[s]);
  const stamp=cur,cands=[];
  for(let bi=0;bi<nb;bi++){const b=bs[bi];
   for(let k=0;k<4;k++){const d=D[k][1]*w+D[k][0],t=b+d;
    if(rg[b-d]!==stamp||wall[t]||occ[t]||!lv[t])continue;
    occ[b]=0;occ[t]=1;const fr=frozen(t);occ[b]=1;occ[t]=0;
    if(!fr)cands.push([bi,t,k]);}}
  for(const b of bs)occ[b]=0;
  for(const[bi,t,k]of cands){
   const nb2=bs.slice();nb2[bi]=t;nb2.sort((a,b)=>a-b);
   for(const b of bs)occ[b]=1;occ[bs[bi]]=0;occ[t]=1;
   const low2=flood(bs[bi]);
   for(const b of bs)occ[b]=0;occ[t]=0;
   const key=low2+':'+nb2.join(','),g2=g+1,sv=seen.get(key);
   if(sv!==undefined&&sv<=g2)continue;
   const h2=heur(nb2);if(h2>=1e9)continue;
   seen.set(key,g2);
   const ni=bxs.length;bxs.push(nb2);pls.push(bs[bi]);par.push(s);psh.push([bs[bi],t,k]);gs.push(g2);
   hpush([g2+h2,h2,seq++,ni]);
  }
 }
 return null;
}
function rooms(L){
 const{w,wall,goals,boxes,player}=L,lv=liveSq(wall,w,goals),row=Math.floor(player/w);
 const cut=new Uint8Array(wall.length);
 for(let i=row*w;i<(row+1)*w;i++)if(!wall[i]&&!lv[i])cut[i]=1;
 if(boxes.some(b=>cut[b]))return null;
 const part=new Int32Array(wall.length).fill(-1),rs=[];
 for(let s=0;s<wall.length;s++){
  if(wall[s]||cut[s]||part[s]>=0)continue;
  const sq=[s];part[s]=rs.length;
  for(let i=0;i<sq.length;i++)for(let k=0;k<4;k++){const q=sq[i]+D[k][1]*w+D[k][0];if(!wall[q]&&!cut[q]&&part[q]<0){part[q]=rs.length;sq.push(q);}}
  rs.push({sq,boxes:[],goals:[],done:false});
 }
 for(const b of boxes)rs[part[b]].boxes.push(b);
 for(const g of goals)if(part[g]>=0)rs[part[g]].goals.push(g);
 if(goals.some(g=>part[g]<0)||rs.some(r=>r.boxes.length!==r.goals.length))return null;
 return rs.filter(r=>r.boxes.length>0);
}
function endOf(w,from,moves){let p=from;for(const ch of moves){const c=ch.toLowerCase();p+=c==='u'?-w:c==='d'?w:c==='l'?-1:1;}return p;}
function solveLevel(t){
 const L=parse(t),rs=rooms(L);
 if(!rs){const s=astar(L,CAP)||astar(L,CAP2);return s?s.moves:'';}
 let player=L.player,moves='';
 for(const r of rs){
  const wall=L.wall.slice();
  for(const o of rs)if(o!==r)for(const b of(o.done?o.goals:o.boxes))wall[b]=1;
  const sub={w:L.w,h:L.h,wall,goals:r.goals,boxes:r.boxes.slice(),player};
  let s=astar(sub,CAP);if(!s)s=astar(sub,CAP2);
  if(!s)return'';
  moves+=s.moves;player=endOf(L.w,player,s.moves);r.done=true;
 }
 return moves;
}
for(const id of readdirSync(I).sort()){
 const moves=solveLevel(readFileSync(join(I,id,'level.txt'),'utf8'));
 mkdirSync(join(O,id),{recursive:true});
 writeFileSync(join(O,id,'solution.txt'),moves+'\n');
}
