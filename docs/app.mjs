import {fan,analyze,fraction} from './graph.mjs';
const $=id=>document.getElementById(id);
let zh=false,mode='fan',customN=5,customEdges=[[0,1],[1,2],[2,3],[3,4]];
const tr=(en,cn)=>zh?cn:en;
const svg=(tag,attrs)=>{const el=document.createElementNS('http://www.w3.org/2000/svg',tag);for(const [key,v] of Object.entries(attrs))el.setAttribute(key,v);return el;};
function render(){
 const isFan=mode==='fan',m=Number($('m').value),max=(m-1)*(m-2)/2;
 $('t').max=max;if(Number($('t').value)>max)$('t').value=max;
 const t=Number($('t').value);$('mValue').textContent=m;$('tValue').textContent=t;$('sizeValue').textContent=customN;
 $('fanControls').hidden=!isFan;$('customControls').hidden=isFan;
 $('fanMode').setAttribute('aria-pressed',String(isFan));$('customMode').setAttribute('aria-pressed',String(!isFan));
 const g=isFan?fan(m,t):{n:customN,edges:customEdges,labels:Array.from({length:customN},(_,i)=>String(i+1))};
 const a=analyze(g.n,g.edges),root=$('graph');root.replaceChildren();
 const pos=isFan?[[150,210],...Array.from({length:m-1},(_,i)=>[280,45+(m===2?165:330*i/(m-2))]),[45,210],[470,210]]:Array.from({length:g.n},(_,i)=>[280+190*Math.cos(2*Math.PI*i/g.n-Math.PI/2),210+160*Math.sin(2*Math.PI*i/g.n-Math.PI/2)]);
 for(const [u,v] of g.edges)root.append(svg('line',{x1:pos[u][0],y1:pos[u][1],x2:pos[v][0],y2:pos[v][1],stroke:isFan&&u>0&&v<m?'#87e6b9':'#738aa6','stroke-width':2}));
 for(let i=0;i<g.n;i++){const [x,y]=pos[i],central=a.connected&&a.center.includes(i);root.append(svg('circle',{cx:x,cy:y,r:15,fill:central?'#8ad8ff':'#8a9bb2',stroke:'#13263e','stroke-width':2}));const label=svg('text',{x,y:y+4,'text-anchor':'middle','font-size':12,fill:'#0b1220','font-weight':700});label.textContent=g.labels[i];root.append(label);}
 root.setAttribute('aria-label',tr('Graph: ','图：')+g.n+tr(' vertices, ',' 个顶点，')+g.edges.length+tr(' edges',' 条边'));
 $('formula').textContent='2 − '+(m-1+t)+' / '+(m*(m-1)/2)+' = '+fraction(2*(m*(m-1)/2)-(m-1+t),m*(m-1)/2);
 const stats=$('stats');stats.replaceChildren();
 if(a.connected){
  for(const [label,value] of [[tr('Center size','中心顶点数'),a.center.length],[tr('Mean center distance','平均中心距离'),fraction(a.sum,a.denominator)],[tr('Radius / diameter','半径 / 直径'),a.radius+' / '+a.diameter],[tr('Total domination number','全支配数'),a.gamma],[tr('Center edges','中心边数'),a.centerEdges],[tr('4-cycle','四环'),a.c4?tr('Present','存在'):tr('Absent','不存在')]]){
   const div=document.createElement('div'),span=document.createElement('span'),strong=document.createElement('strong');span.textContent=label;strong.textContent=value;div.append(span,strong);stats.append(div);
  }
  $('result').textContent=tr('No. 268 inequality: ','第 268 号不等式：')+(a.strict?tr('holds for this graph.','此图满足。'):tr('fails for this graph.','此图不满足。'))+' '+tr('Ceiling inequality: ','上取整不等式：')+(a.ceiling?tr('holds for this graph.','此图满足。'):tr('fails for this graph (not necessarily a counterexample to no. 269).','此图不满足（不一定是第 269 号的反例）。'));
 }else $('result').textContent=tr('Disconnected graph — add edges to calculate finite distances and center.','图不连通——添加边后计算有限距离和中心。');
}
function edgeGrid(){const root=$('edges');root.replaceChildren();for(let i=0;i<customN;i++)for(let j=i+1;j<customN;j++){
 const b=document.createElement('button'),active=customEdges.some(([u,v])=>u===i&&v===j);b.textContent=(i+1)+'–'+(j+1);b.setAttribute('aria-pressed',String(active));b.onclick=()=>{if(active)customEdges=customEdges.filter(([u,v])=>u!==i||v!==j);else customEdges.push([i,j]);edgeGrid();render();[...root.children].find(x=>x.textContent===b.textContent)?.focus();};root.append(b);
}}
function translate(){document.documentElement.lang=zh?'zh-CN':'en';document.querySelectorAll('[data-en]').forEach(el=>{el.textContent=zh?el.dataset.zh:el.dataset.en;});$('lang').textContent=zh?'English':'中文';render();}
$('lang').onclick=()=>{zh=!zh;translate();};$('fanMode').onclick=()=>{mode='fan';render();};$('customMode').onclick=()=>{mode='custom';edgeGrid();render();};$('m').oninput=()=>{$('t').value=0;render();};$('t').oninput=render;$('size').oninput=()=>{customN=Number($('size').value);customEdges=customEdges.filter(([u,v])=>u<customN&&v<customN);edgeGrid();render();};$('clear').onclick=()=>{customEdges=[];edgeGrid();render();};$('path').onclick=()=>{customEdges=Array.from({length:customN-1},(_,i)=>[i,i+1]);edgeGrid();render();};edgeGrid();render();