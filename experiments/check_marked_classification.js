// Independent exhaustive marked-center classification check.
// Node.js, no dependencies. The same audit function was executed before commit.
function audit() {
  const connect=(a,i,j)=>{a[i]|=1<<j;a[j]|=1<<i;};
  const reach=(a,i)=>{let r=a[i]|(1<<i);for(let j=0;j<a.length;j++)if(a[i]&(1<<j))r|=a[j];return r;};
  const ecc=(a,i)=>((a[i]|(1<<i))===(1<<a.length)-1?1:reach(a,i)===(1<<a.length)-1?2:3);
  function* graphs(n){const edges=[];for(let i=2;i<n;i++)for(let j=i+1;j<n;j++)edges.push([i,j]);for(let m=0;m<3**(n-2);m++){let a=Array(n).fill(0);connect(a,0,1);let z=m;for(let i=2;i<n;i++){const t=z%3+1;z=Math.floor(z/3);if(t&1)connect(a,0,i);if(t&2)connect(a,1,i);}for(let b=0;b<2**edges.length;b++){const g=a.slice();edges.forEach(([i,j],k)=>{if(b&(1<<k))connect(g,i,j);});yield g;}}}
  function partition(a){const n=a.length,all=(1<<n)-1;for(let A=1;A<all;A+=2){if(A&2)continue;const B=all^A;let ok=true;for(let i=0;i<n&&ok;i++){let cl=a[i]|(1<<i);if(!(cl&A)||!(cl&B)){ok=false;break;}let far=all^reach(a,i);if(far&((A&(1<<i))?B:A))ok=false;}if(ok)return true;}return false;}
  function extension(a,k){const n=a.length,N=n+k,edges=[];for(let i=n;i<N;i++)for(let j=2;j<i;j++)edges.push([i,j]);for(let m=0;m<3**k;m++){const base=a.concat(Array(k).fill(0));let z=m;for(let i=n;i<N;i++){const t=z%3+1;z=Math.floor(z/3);if(t&1)connect(base,0,i);if(t&2)connect(base,1,i);}for(let mask=0;mask<2**edges.length;mask++){const b=base.slice();edges.forEach(([i,j],l)=>{if(mask&(1<<l))connect(b,i,j);});const ec=b.map((_,i)=>ecc(b,i));const r=Math.min(...ec);if(ec.every((e,i)=>i<n?e===r:e>r))return true;}}return false;}
  const rows=[];for(let n=2;n<=5;n++){const row={n,markedGraphs:0,selfCentered:0,two:0,four:0,threeChecked:0,threeRealizable:0};for(const a of graphs(n)){row.markedGraphs++;const es=a.map((_,i)=>ecc(a,i));if(es.every(x=>x===es[0])){row.selfCentered++;continue;}const p=partition(a),e2=extension(a,2);if(p!==e2)throw Error("partition disagreement "+JSON.stringify(a));row[p?"two":"four"]++;if(n<=4){const e3=extension(a,3);row.threeChecked++;if(e3)row.threeRealizable++;if(e3&&!e2)throw Error("three-only disagreement "+JSON.stringify(a));}}rows.push(row);}return rows;
}
console.log(JSON.stringify(audit(), null, 2));
