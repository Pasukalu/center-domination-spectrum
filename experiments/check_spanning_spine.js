// Constructive certificate check for Lemma 2.1 (no external dependencies).
function checkSpines() {
  "use strict";
  const assert = (b, why) => { if (!b) throw Error(why); };
  const vertices = n => Array.from({length:n}, (_,i)=>i);
  function ecc(g) {
    const n=g.length;
    return vertices(n).map(root=>{
      const d=Array(n).fill(-1),q=[root];d[root]=0;
      for(let i=0;i<q.length;i++)for(const v of g[q[i]])if(d[v]<0){d[v]=d[q[i]]+1;q.push(v);}
      return q.length===n?Math.max(...d):Infinity;
    });
  }
  function certificate(g,D) {
    const n=g.length,k=D.length,dSet=new Set(D),part=Array(n).fill(-1);
    let c=0;
    for(const x of D)if(part[x]<0){
      const q=[x];part[x]=c;
      for(let i=0;i<q.length;i++)for(const y of g[q[i]])if(dSet.has(y)&&part[y]<0){part[y]=c;q.push(y);}
      assert(q.length>=2,"singleton D component");c++;
    }
    for(let x=0;x<n;x++)if(part[x]<0){
      const y=g[x].find(v=>dSet.has(v));assert(y!==undefined,"not totally dominated");
      part[x]=part[y];
    }
    const quotient=Array.from({length:c},()=>[]);
    for(let x=0;x<n;x++)for(const y of g[x])if(part[x]!==part[y])quotient[part[x]].push([part[y],x,y]);
    const K=new Set(D),seen=new Set([0]),q=[0];
    for(let i=0;i<q.length;i++)for(const [j,x,y] of quotient[q[i]])if(!seen.has(j)){
      seen.add(j);q.push(j);K.add(x);K.add(y);
    }
    assert(seen.size===c,"disconnected quotient");
    assert(2*c<=k&&K.size<=k+2*(c-1),"spine count");
    const tree=Array.from({length:n},()=>[]);
    const edge=(x,y)=>{assert(g[x].includes(y)&&!tree[x].includes(y),"invalid tree edge");tree[x].push(y);tree[y].push(x);};
    const reached=new Set([D[0]]),queue=[D[0]];
    for(let i=0;i<queue.length;i++)for(const y of g[queue[i]])if(K.has(y)&&!reached.has(y)){
      reached.add(y);queue.push(y);edge(queue[i],y);
    }
    assert(reached.size===K.size,"disconnected spine");
    for(let x=0;x<n;x++)if(!K.has(x)){
      const y=g[x].find(v=>K.has(v));assert(y!==undefined,"spine not dominating");edge(x,y);
    }
    // Verify the witness independently, using distances in the actual tree.
    const et=ecc(tree),dia=Math.max(...et),rad=Math.min(...et);
    assert(tree.reduce((s,a)=>s+a.length,0)===2*(n-1)&&Number.isFinite(dia),"not spanning tree");
    assert(dia<=K.size+1&&dia<=k+2*c-1&&dia<=2*k-1,"diameter bound");
    assert(rad===Math.ceil(dia/2),"tree midpoint radius");
    assert(k%2===0||rad<=k-1,"odd bound");
    if(rad===k){
      const centers=vertices(n).filter(x=>et[x]===k);
      assert(centers.length===2&&tree[centers[0]].includes(centers[1]),"missing central edge");
    }
    return {tight:dia===2*k-1,midpoint:rad===k};
  }
  const result=[];
  for(let n=2;n<=6;n++){
    const pairs=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)pairs.push([i,j]);
    const subsets=Array.from({length:(1<<n)-1},(_,i)=>vertices(n).filter(v=>((i+1)>>v)&1)).sort((a,b)=>a.length-b.length);
    const row={n,graphs:0,sets:0,tight:0,midpoint:0,scope:n<=5?"all total dominating sets":"all minimum total dominating sets"};
    for(let mask=0;mask<(1<<pairs.length);mask++){
      const g=Array.from({length:n},()=>[]);for(let i=0;i<pairs.length;i++)if((mask>>i)&1){const [x,y]=pairs[i];g[x].push(y);g[y].push(x);}
      const eg=ecc(g);if(!Number.isFinite(eg[0]))continue;
      row.graphs++;
      let min=Infinity;
      for(const D of subsets){
        if(n===6&&D.length>min)break;
        if(!g.every(adj=>adj.some(x=>D.includes(x))))continue;
        min=Math.min(min,D.length);const c=certificate(g,D);row.sets++;row.tight+=Number(c.tight);row.midpoint+=Number(c.midpoint);
        assert(Math.min(...eg)<=D.length,"ambient radius bound");
      }
    }
    result.push(row);
  }
  assert(result.map(x=>x.graphs).join(",")==="1,4,38,728,26704","connected graph count");
  return result;
}
const results = checkSpines();
const expected = [
  {
    "n": 2,
    "graphs": 1,
    "sets": 1,
    "tight": 0,
    "midpoint": 0,
    "scope": "all total dominating sets"
  },
  {
    "n": 3,
    "graphs": 4,
    "sets": 13,
    "tight": 0,
    "midpoint": 0,
    "scope": "all total dominating sets"
  },
  {
    "n": 4,
    "graphs": 38,
    "sets": 258,
    "tight": 48,
    "midpoint": 48,
    "scope": "all total dominating sets"
  },
  {
    "n": 5,
    "graphs": 728,
    "sets": 9793,
    "tight": 1440,
    "midpoint": 1440,
    "scope": "all total dominating sets"
  },
  {
    "n": 6,
    "graphs": 26704,
    "sets": 90300,
    "tight": 61440,
    "midpoint": 61440,
    "scope": "all minimum total dominating sets"
  }
];
if (JSON.stringify(results) !== JSON.stringify(expected)) throw Error('unexpected result counts');
console.log(JSON.stringify(results, null, 2));
