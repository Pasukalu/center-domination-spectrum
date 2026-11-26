import assert from 'node:assert/strict';
import {fan,analyze,fraction} from '../docs/graph.mjs';
let fanCases=0,connected=0,disconnected=0,partial=0;
for(let m=2;m<=12;m++)for(let t=0;t<=(m-1)*(m-2)/2;t++){
 const g=fan(m,t),a=analyze(g.n,g.edges),M=m*(m-1)/2;
 assert.equal(a.connected,true);assert.equal(a.gamma,2);assert.equal(a.center.length,m);
 assert.deepEqual(a.center,Array.from({length:m},(_,i)=>i));assert.equal(a.centerEdges,m-1+t);
 assert.equal(a.sum,2*M-(m-1+t));assert.equal(a.pairs,M);assert.equal(a.radius,2);assert.equal(a.diameter,3);
 fanCases++;
}
for(let n=2;n<=5;n++){
 const e=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)e.push([i,j]);
 for(let mask=0;mask<2**e.length;mask++){
  const a=analyze(n,e.filter((_,i)=>mask&(1<<i)));
  if(!a.connected){disconnected++;continue;}connected++;assert.equal(a.strict,true);
  if(a.gamma%2===1||(a.gamma===2&&!a.c4)){partial++;assert.equal(a.ceiling,true);}
 }
}
assert.equal(fraction(0,1),'0');assert.equal(fraction(12,10),'6/5');assert.equal(fraction(3,3),'1');
assert.deepEqual(analyze(3,[[0,1]]),{connected:false});
assert.equal(analyze(3,[[0,1],[1,2]]).mean,0);
assert.throws(()=>analyze(3,[[0,0]]));assert.throws(()=>fan(3,2));
console.log({fanCases,connected,disconnected,partial});