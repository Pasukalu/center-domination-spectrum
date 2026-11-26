// Finite simple graphs; exact integer counts, independent of the Lean code.
export function fan(m,t=0){
  if(!Number.isInteger(m)||m<2||m>12) throw new RangeError('m must be 2..12');
  const pairs=[];for(let i=1;i<m;i++)for(let j=i+1;j<m;j++)pairs.push([i,j]);
  if(!Number.isInteger(t)||t<0||t>pairs.length)throw new RangeError('invalid extra edge count');
  const edges=[[0,m]];for(let i=1;i<m;i++)edges.push([0,i],[i,m+1]);
  return {n:m+2,edges:[...edges,...pairs.slice(0,t)],labels:['u',...Array.from({length:m-1},(_,i)=>'s'+(i+1)),'p','q']};
}
export function analyze(n,edges){
  if(!Number.isInteger(n)||n<2||n>14)throw new RangeError('n must be 2..14');
  const adj=Array(n).fill(0),d=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?0:Infinity));
  for(const [u,v] of edges){
    if(!Number.isInteger(u)||!Number.isInteger(v)||u<0||v<0||u>=n||v>=n||u===v)throw new RangeError('invalid edge');
    adj[u]|=1<<v;adj[v]|=1<<u;d[u][v]=d[v][u]=1;
  }
  for(let k=0;k<n;k++)for(let i=0;i<n;i++)for(let j=0;j<n;j++)d[i][j]=Math.min(d[i][j],d[i][k]+d[k][j]);
  const connected=d[0].every(Number.isFinite);
  if(!connected)return {connected:false};
  const ecc=d.map(row=>Math.max(...row)),radius=Math.min(...ecc),diameter=Math.max(...ecc);
  const center=ecc.flatMap((e,i)=>e===radius?[i]:[]);let sum=0,pairs=0,centerEdges=0;
  for(let i=0;i<center.length;i++)for(let j=i+1;j<center.length;j++){const x=d[center[i]][center[j]];sum+=x;pairs++;if(x===1)centerEdges++;}
  const full=(1<<n)-1;let gamma=n,dominating=[];
  for(let mask=1;mask<=full;mask++){let count=0,cover=0;for(let i=0;i<n;i++)if(mask&(1<<i)){count++;cover|=adj[i];}
    if(cover===full&&count<=gamma){gamma=count;dominating=Array.from({length:n},(_,i)=>i).filter(i=>mask&(1<<i));}
  }
  let c4=false;
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){const common=adj[i]&adj[j];if(common&&(common&(common-1)))c4=true;}
  const denominator=pairs||1;
  return {connected:true,ecc,radius,diameter,center,sum,pairs,denominator,mean:sum/denominator,centerEdges,gamma,dominating,c4,
    strict:sum<gamma*denominator,ceiling:sum<=(gamma-1)*denominator};
}
export function fraction(a,b){let x=a,y=b;while(y){[x,y]=[y,x%y];}return b/x===1?String(a/x):a/x+'/'+b/x;}
