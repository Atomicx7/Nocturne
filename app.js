/* Nocturne — piano tiles engine
   Classic ivory board, black tiles. Multi-band onset detection + tempo snap. */
const $ = s => document.querySelector(s);
const $$ = s => [...document.querySelectorAll(s)];

const canvas = $('#gameCanvas');
const ctx = canvas.getContext('2d');
const gameFrame = $('#gameFrame');
const overlay = $('#overlay');
const overlayKicker = $('#overlayKicker');
const overlayTitle = $('#overlayTitle');
const overlayDesc = $('#overlayDesc');
const countdownEl = $('#countdown');
const fileInput = $('#fileInput');
const dropzone = $('#dropzone');
const fileNameEl = $('#fileName');
const urlInput = $('#urlInput');
const audioEl = $('#audioEl');
const mastSong = $('#mastSong');
const detectLabel = $('#detectLabel');
const customBadge = $('#customBadge');

const hudScore = $('#hudScore'), hudCombo = $('#hudCombo'), hudAcc = $('#hudAcc'), hudGrade = $('#hudGrade');
const hpFill = $('#hpFill');
const statBest = $('#statBest'), statPerfect = $('#statPerfect'), statGood = $('#statGood'), statMiss = $('#statMiss');
const progBar = $('#progBar'), progText = $('#progText');

const difficultySel = $('#difficulty');
const speedSlider = $('#speedSlider'), speedVal = $('#speedVal');
const widthSlider = $('#widthSlider'), widthVal = $('#widthVal');
const holdNotesChk = $('#holdNotes');
const pianoChk = $('#autoPlayDemo');
const offsetSlider = $('#offsetSlider'), offsetVal = $('#offsetVal');
const keyHintsChk = $('#keyHints');
// deterministic PRNG (lane presentation only — timing always comes from audio)
function srand(seed){
  let a = seed >>> 0;
  return function(){
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

let audioCtx;
function getAudioCtx(){
  if(!audioCtx) audioCtx = new (window.AudioContext||window.webkitAudioContext)();
  if(audioCtx.state==='suspended') audioCtx.resume();
  return audioCtx;
}

const PRESETS = [
  {id:'twinkle', title:'Twinkle Little Star', artist:'Traditional · 100 BPM', bpm:100, duration:40},
  {id:'canon', title:'Canon in D', artist:'Pachelbel · 84 BPM', bpm:84, duration:46},
  {id:'moonlight', title:'Moonlight Sonata', artist:'Beethoven · 72 BPM', bpm:72, duration:48},
  {id:'rush', title:'Rush Hour', artist:'Etude · 138 BPM', bpm:138, duration:34},
  {id:'dream', title:'Endless Dream', artist:'Etude · 122 BPM', bpm:122, duration:38},
];

let currentPreset = PRESETS[0];
let currentMode = 'classic';
let customAudioBuffer = null;
let customObjectUrl = null;
let customName = null;
let detectedBpm = null;
let tiles = [];
let activeTiles = [];
let particles = [];
let feedbacks = [];
let ripples = [];
let isPlaying = false, isPaused = false, startTime = 0, pauseOffset = 0;
let score=0, combo=0, bestCombo=0, perfect=0, great=0, good=0, miss=0, hp=100;
// custom-song rhythm analysis cache (analyze once, build per difficulty)
let analysisCache = null, analysisFor = null, chartMeta = null;
let keyActive = [false,false,false,false];
let holdState = [false,false,false,false];
let keyFlash = [0,0,0,0];    // piano-key illumination 0..1 (decays in draw)
let laneFlash = [0,0,0,0];   // miss feedback per lane 0..1 (decays in draw)
let dust = [];               // ambient stage motes (normalized coords)
let songDuration = 0;
for(let i=0;i<34;i++) dust.push({x:Math.random(), y:Math.random(), s:0.6+Math.random()*1.6, v:0.010+Math.random()*0.022, a:0.04+Math.random()*0.09});

const LANE_MIDI = [60, 64, 67, 72];

/* ---------- piano tap tone (dry, felt-like) ---------- */
function playPianoTone(midi, dur=0.3, vol=0.4){
  if(!pianoChk.checked) return;
  try{
    const ac = getAudioCtx();
    const t = ac.currentTime;
    const mk = (type, f, g0)=>{
      const o = ac.createOscillator(), g = ac.createGain();
      o.type = type; o.frequency.value = f;
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(Math.max(0.001,g0), t+0.008);
      g.gain.exponentialRampToValueAtTime(0.0001, t+dur);
      o.connect(g).connect(ac.destination);
      o.start(t); o.stop(t+dur+0.05);
    };
    const f = 440*Math.pow(2,(midi-69)/12);
    mk('triangle', f, vol);
    mk('sine', f*2, vol*0.25);
  }catch(e){}
}

/* ---------- song list ---------- */
function renderSongs(){
  const list = $('#songList');
  list.innerHTML = '';
  PRESETS.forEach((p, i)=>{
    const div = document.createElement('div');
    div.className = 'song' + (p.id===currentPreset.id && !customAudioBuffer ? ' active' : '');
    div.innerHTML = `<span class="song-num">${String(i+1).padStart(2,'0')}</span>
      <div class="song-meta"><b>${p.title}</b><span>${p.artist}</span></div>
      <span class="song-bpm">${p.bpm}</span>`;
    div.onclick = ()=>{
      customAudioBuffer = null; customName = null; detectedBpm = null;
      if(customObjectUrl && !customObjectUrl.startsWith('http')) URL.revokeObjectURL(customObjectUrl);
      customObjectUrl = null;
      try{ audioEl.pause(); audioEl.removeAttribute('src'); audioEl.load(); }catch(e){}
      currentPreset = p;
      fileNameEl.textContent = 'No file yet';
      customBadge.style.display = 'none';
      buildTilesForCurrent();
      renderSongs();
    };
    list.appendChild(div);
  });
  const label = customAudioBuffer ? (customName + ' — custom') : (currentPreset.title + ' — ' + currentPreset.bpm + ' BPM');
  mastSong.textContent = label;
}

/* ---------- preset tiles: quantized, musical ---------- */
function generatePresetTiles(preset){
  const diff = difficultySel.value;
  const beat = 60/preset.bpm;
  const div = {easy:1, normal:2, hard:2, insane:4}[diff] || 2; // subdivisions per beat
  const step = beat/div;
  const skip = {easy:0.45, normal:0.22, hard:0.12, insane:0.06}[diff] ?? 0.22;
  const out = [];
  // deterministic per preset+difficulty: same song, same chart
  let hs = 7;
  for (const ch of preset.id + diff) hs = (Math.imul(hs, 31) + ch.charCodeAt(0)) | 0;
  const rng = srand(hs);
  const seqs = {
    twinkle:[0,0,2,2,3,3,2,1,1,0,0,1,1,0],
    canon:[0,1,2,3,2,1,0,2,1,3,0,1],
    moonlight:[0,2,1,3,2,0,3,1],
    rush:[0,1,2,3,2,1,3,0],
    dream:[0,1,2,3,3,2,1,0],
  };
  const seq = seqs[preset.id] || seqs.twinkle;
  let lane = 0, idx = 0;
  for(let t = 1.0; t < preset.duration - 0.5; t += step){
    idx++;
    if(rng() < skip) continue;
    // stepwise lane motion (plays like a melody, not dice)
    const target = seq[idx % seq.length];
    lane = rng() < 0.72
      ? target
      : Math.max(0, Math.min(3, lane + (rng()<0.5?-1:1)));
    if(out.length && out[out.length-1].lane === lane && out[out.length-1].time > t-0.14 && rng()<0.7){
      lane = (lane + 1 + Math.floor(rng()*2)) % 4;
    }
    const human = (rng()-0.5)*0.012; // ±12ms humanization
    const isHold = holdNotesChk.checked && diff!=='easy' && rng() < 0.07 && (t < preset.duration-2);
    if(isHold){
      const d = beat*(1+Math.floor(rng()*2));
      out.push({time:t+human, lane, type:'hold', duration:Math.min(d, 1.4), midi:LANE_MIDI[lane]});
      // skip the covered steps
      t += d - step;
    } else {
      out.push({time:t+human, lane, type:'tap', midi:LANE_MIDI[lane]});
      // downbeat-driven chords (deterministic, pattern-based — never spam):
      // downbeats bloom into doubles, strong downbeats into triples on insane
      const beatIdx = Math.round((t-1.0)/beat);
      const extra = [];
      if(diff!=='easy' && beatIdx%4===0){
        let dl = seq[(idx+2)%seq.length];
        if(dl===lane) dl = (dl+2)%4;
        extra.push(dl);
        if(diff==='insane' && rng()<0.3){
          const tl = (dl+1+Math.floor(rng()*2))%4;
          if(tl!==lane && tl!==dl) extra.push(tl);
        }
      } else if((diff==='hard'||diff==='insane') && beatIdx%2===1 && rng()<0.15){
        extra.push([0,1,2,3].filter(l=>l!==lane)[Math.floor(rng()*3)]);
      }
      for(const l2 of extra){
        out.push({time:t+human, lane:l2, type:'tap', midi:LANE_MIDI[l2]});
      }
    }
  }
  out.sort((a,b)=>a.time-b.time);
  return out;
}

/* Rhythm analysis lives in audio-analysis.js: Hann STFT -> multi-band log
   spectral flux -> adaptive threshold -> autocorrelation tempo -> beat phase
   search -> 1/4-beat quantization -> strength selection -> seeded lanes ->
   validation. Analysis runs once per import; difficulty only re-selects. */

/* ---------- build ---------- */
async function buildTilesForCurrent(){
  const row = $('#analyzeRow');
  row.style.display = 'flex';
  const setP = (f, txt)=>{
    $('#analyzeBar').style.width = Math.round(f*100)+'%';
    if(txt) $('#analyzeText').textContent = txt;
  };
  setP(0.05, 'Preparing…');
  await new Promise(r=>setTimeout(r, 60));
  if(customAudioBuffer){
    const NA = window.NocturneAnalysis;
    const offMs = parseInt(offsetSlider.value || '0', 10);
    // heavy analysis runs ONCE per import; difficulty/offset/holds only re-select
    if(analysisFor !== customAudioBuffer || !analysisCache){
      setP(0.08, 'Analyzing music…');
      try{
        const ch = customAudioBuffer.numberOfChannels, len = customAudioBuffer.length;
        const mono = new Float32Array(len);
        for(let c=0;c<ch;c++){
          const d = customAudioBuffer.getChannelData(c);
          for(let i=0;i<len;i++) mono[i] += d[i]/ch;
        }
        analysisCache = await NA.analyzeSong(mono, customAudioBuffer.sampleRate, customAudioBuffer.duration,
          f=>setP(0.08+f*0.7, f<0.35?'Onset envelope…':f<0.55?'Tempo…':'Beat grid…'));
        analysisFor = customAudioBuffer;
      }catch(err){
        console.error(err);
        fileNameEl.textContent = 'Analysis failed — try another file.';
        row.style.display='none';
        return;
      }
    }
    setP(0.82, 'Generating chart…');
    await new Promise(r=>setTimeout(r, 30));
    const res = NA.buildChart(analysisCache, {
      difficulty: difficultySel.value,
      allowHolds: holdNotesChk.checked,
      offsetMs: offMs
    });
    tiles = res.tiles;
    chartMeta = res.meta;
    songDuration = customAudioBuffer.duration;
    if(res.validation.warnings.length) console.warn('[chart]', res.validation.warnings);
    if(!res.validation.valid) console.error('[chart]', res.validation.errors);
    const conf = Math.round(res.confidence*100);
    detectLabel.textContent = `${res.bpm} BPM · ${res.tiles.length} notes`;
    customBadge.style.display = 'block';
    customBadge.textContent = `Custom track · ${res.bpm} BPM · ${res.stats.rawOnsets} onsets → ${res.stats.acceptedEvents} events → ${res.tiles.length} tiles`;
    overlayKicker.textContent = 'Custom track · analysed';
    overlayTitle.textContent = customName || 'Your song';
    overlayDesc.textContent = `${res.bpm} BPM · ${res.tiles.length} notes. Press play.`;
    mastSong.textContent = (customName||'Custom') + ` — ${res.bpm} BPM`;
    drawDebugView();
    setP(1, 'Ready to play');
  } else {
    tiles = generatePresetTiles(currentPreset);
    songDuration = currentPreset.duration;
    detectedBpm = currentPreset.bpm;
    detectLabel.textContent = `${currentPreset.bpm} BPM · ${tiles.length} notes`;
    overlayKicker.textContent = 'Ready';
    overlayTitle.textContent = currentPreset.title;
    overlayDesc.textContent = `${currentPreset.artist}. Press play.`;
    mastSong.textContent = `${currentPreset.title} — ${currentPreset.bpm} BPM`;
    setP(1, 'Ready');
  }
  setTimeout(()=>{ row.style.display='none'; }, 500);
  pauseOffset = 0;
  resetGameState();
  progBar.style.width = '0%';
  progText.textContent = `0 / ${Math.floor(songDuration)} seconds`;
  draw(0);
}
function formatTime(s){ const m=Math.floor(s/60); const sec=Math.floor(s%60).toString().padStart(2,'0'); return `${m}:${sec}`; }

/* ---------- state ---------- */
function resetGameState(){
  score=0; combo=0; bestCombo=0; perfect=0; great=0; good=0; miss=0; hp=100;
  keyActive=[false,false,false,false]; holdState=[false,false,false,false];
  keyFlash=[0,0,0,0]; laneFlash=[0,0,0,0];
  particles=[]; feedbacks=[]; ripples=[];
  if(hudGrade) hudGrade.textContent='';
  activeTiles = tiles.map(t=>({...t, hit:false, missed:false, holding:false}));
  updateHud();
  hpFill.style.width='100%';
}
let audioSource=null, presetStartPerf=null;
function stopAudio(){
  if(audioSource){ try{audioSource.stop();}catch(e){} audioSource=null; }
  try{ audioEl.pause(); }catch(e){}
}
function getCurrentTime(){
  if(!isPlaying || isPaused) return pauseOffset;
  if(customAudioBuffer){
    return getAudioCtx().currentTime - startTime;
  }
  return (performance.now()-presetStartPerf)/1000;
}
function startAudio(){
  stopAudio();
  const ac = getAudioCtx();
  if(customAudioBuffer){
    audioSource = ac.createBufferSource();
    audioSource.buffer = customAudioBuffer;
    audioSource.connect(ac.destination);
    startTime = ac.currentTime - pauseOffset + 0.02;
    try{ audioSource.start(0, Math.max(0,pauseOffset)); }catch(e){ audioSource.start(0); }
    audioSource.onended = ()=>{ if(isPlaying && !isPaused) endGame(false); };
  } else {
    presetStartPerf = performance.now() - pauseOffset*1000;
  }
}

/* ---------- 3D stage projection (pure math, no DOM) ----------
   Lanes converge toward a vanishing point above the board; at keyTop the
   lane pitch exactly matches the four physical piano keys, so every tile
   terminates precisely above its own key. */
function stageGeom(W,H){
  const keyH = H*0.20, keyTop = H-keyH;
  const vpY = -H*0.32;
  const spread = y => {
    let t = (y-vpY)/(keyTop-vpY);
    t = Math.min(1, Math.max(0, t));
    return 0.40 + 0.60*t;
  };
  return {
    W, H, keyH, keyTop, vpY, spread,
    center: (lane,y) => W/2 + (lane-1.5)*(W/4)*spread(y),
    half: y => (W/8)*spread(y)
  };
}
function laneAtX(W,H,x,y){
  const g = stageGeom(W,H);
  const yy = Math.min(y, g.keyTop); // on/below the keys: full key pitch
  // lane L spans pitch-offsets [L-2, L-1) from center → +2.0 (not 1.5:
  // that skews every touch half a lane left)
  const fx = (x - W/2)/((W/4)*g.spread(yy)) + 2.0;
  return Math.min(3, Math.max(0, Math.floor(fx)));
}
/* ---------- input ---------- */
function clientToLane(clientX, clientY){
  const rect = canvas.getBoundingClientRect();
  const sx = rect.width>0 ? canvas.width/rect.width : 1;
  const sy = rect.height>0 ? canvas.height/rect.height : 1;
  return laneAtX(canvas.width, canvas.height, (clientX-rect.left)*sx, (clientY-rect.top)*sy);
}
function tryHit(lane){
  if(!isPlaying || isPaused) return;
  const now = getCurrentTime();
  const PERFECT_W = 0.05, GREAT_W = 0.09, GOOD_W = 0.14;
  let best=null, bestD=1e9;
  for(const t of activeTiles){
    if(t.lane!==lane || t.hit || t.missed) continue;
    if(t.type==='hold' && t.holding) continue;
    const d = Math.abs(t.time-now);
    if(d<bestD && d<=GOOD_W+0.02){ best=t; bestD=d; }
  }
  if(!best){
    laneFlash[lane]=Math.max(laneFlash[lane],0.7);
    if(hudGrade){ hudGrade.textContent='MISS'; hudGrade.style.color='#ff6b7a'; }
    if(currentMode==='arcade'){ hp=Math.max(0,hp-6); combo=0; updateHud(); spawnFeedback(lane,'MISS','#ff6b7a'); if(hp<=0) endGame(true); }
    else if(currentMode==='classic'){ combo=0; updateHud(); }
    return;
  }
  handleHit(best, bestD<=PERFECT_W ? 'perfect' : bestD<=GREAT_W ? 'great' : 'good');
}
const isDark = ()=>document.documentElement.dataset.theme!=='light';
function handleHit(tile, grade){
  tile.hit = true;
  if(tile.type==='hold'){ tile.holding=true; holdState[tile.lane]=true; }
  score += (grade==='perfect'?120:grade==='great'?100:65) + Math.floor(combo*3);
  combo++; if(combo>bestCombo) bestCombo=combo;
  if(grade==='perfect') perfect++; else if(grade==='great') great++; else good++;
  keyFlash[tile.lane]=1; // the piano key ignites as the tile lands in it
  spawnParticles(tile.lane, grade);
  const g = stageGeom(canvas.width, canvas.height);
  ripples.push({x:g.center(tile.lane, g.keyTop), y:g.keyTop, t:0, life:0.4,
    col: grade==='perfect' ? '#f0d9a8' : 'rgba(240,217,168,.65)'});
  const fcol = grade==='perfect' ? '#f0d9a8' : grade==='great' ? '#cfd8ea' : '#8f887a';
  spawnFeedback(tile.lane, grade.toUpperCase(), fcol);
  if(hudGrade){
    hudGrade.textContent = grade.toUpperCase();
    hudGrade.style.color = grade==='perfect' ? '#f0d9a8' : grade==='great' ? '#cfd8ea' : '#8f887a';
  }
  if(Math.random()<0.3) spawnFeedback(tile.lane, Math.random()<0.5?'♪':'♫', '#d8b46a');
  // score pop on perfects, combo pulse each 25
  try{
    if(grade==='perfect') hudScore.animate([{transform:'scale(1.22)'},{transform:'scale(1)'}],{duration:160,easing:'ease-out'});
    if(combo%25===0) hudCombo.animate([{transform:'scale(1.35)'},{transform:'scale(1)'}],{duration:200,easing:'ease-out'});
  }catch(_){}
  playPianoTone(tile.midi, 0.32, grade==='perfect'?0.42:grade==='great'?0.36:0.3);
  if(currentMode==='arcade') hp=Math.min(100,hp+1.2);
  updateHud();
}
function releaseHold(lane){
  holdState[lane]=false;
  const now = getCurrentTime();
  for(const t of activeTiles){
    if(t.lane!==lane || t.type!=='hold' || !t.holding || !t.hit) continue;
    const tail = t.time+(t.duration||0.5);
    if(now >= tail-0.18){
      score += 80 + Math.floor(t.duration*40);
      spawnFeedback(lane,'HELD','#1f9d55');
      playPianoTone(t.midi+7, 0.16, 0.24);
    } else {
      combo=0; miss++;
      if(currentMode==='classic'){ t.holding=false; endGame(true); return; }
      if(currentMode==='arcade'){ hp=Math.max(0,hp-12); if(hp<=0){ t.holding=false; endGame(true); return; } }
      spawnFeedback(lane,'EARLY','#e14b6a');
    }
    t.holding=false;
    updateHud();
    break;
  }
}

/* ---------- fx ---------- */
function spawnParticles(lane, grade){
  const g = stageGeom(canvas.width, canvas.height);
  const x=g.center(lane, g.keyTop), y=g.keyTop-6;
  const cols = grade==='perfect' ? ['#f0d9a8','#d8b46a','#fff6e0'] : ['#d8b46a','#8f887a','#f0d9a8'];
  for(let i=0;i<9;i++) particles.push({x, y, vx:(Math.random()-0.5)*260, vy:-Math.random()*300-50,
    life:0.35+Math.random()*0.3, t:0, col:cols[i%3], s:1.6+Math.random()*2.2});
}
function spawnFeedback(lane, text, col){
  const g = stageGeom(canvas.width, canvas.height);
  feedbacks.push({x:g.center(lane, g.keyTop), y:g.keyTop-g.H*0.075, text, col, life:0.6, t:0});
}
function accuracy(){
  const total = perfect+great+good+miss;
  return total ? (perfect+great*0.8+good*0.55)/total*100 : 100;
}
function updateHud(){
  hudScore.textContent = score.toLocaleString('en-US');
  hudCombo.textContent = combo;
  hudAcc.textContent = accuracy().toFixed(1)+'%';
  statBest.textContent = bestCombo;
  statPerfect.textContent = perfect;
  const sg = $('#statGreat'); if(sg) sg.textContent = great;
  statGood.textContent = good; statMiss.textContent = miss;
  hpFill.style.width = hp+'%';
}

/* ---------- render: ivory board, ebony tiles ---------- */
function resizeCanvas(){
  const dpr = Math.max(1, Math.min(2, window.devicePixelRatio||1));
  const r = canvas.getBoundingClientRect();
  if(r.width>0){ canvas.width = Math.round(r.width*dpr); canvas.height = Math.round(r.height*dpr); }
}
let lastFrame = 0;
function draw(now=0){
  const w = canvas.width, h = canvas.height;
  const rect = canvas.getBoundingClientRect();
  const dpr = rect.width>0 ? w/rect.width : 1;
  const dt = Math.min(0.05, (now-lastFrame)/1000 || 0.016); lastFrame = now;
  for(let i=0;i<4;i++){ keyFlash[i]=Math.max(0,keyFlash[i]-dt*2.4); laneFlash[i]=Math.max(0,laneFlash[i]-dt*2.0); }
  for(const m of dust){ m.y-=m.v*dt; if(m.y<-0.02){ m.y=1.02; m.x=Math.random(); } }
  const g = stageGeom(w,h);
  ctx.clearRect(0,0,w,h);

  // near-black room + warm volumetric glow falling from above
  const bg = ctx.createLinearGradient(0,0,0,h);
  bg.addColorStop(0,'#101013'); bg.addColorStop(0.6,'#080807'); bg.addColorStop(1,'#060606');
  ctx.fillStyle=bg; ctx.fillRect(0,0,w,h);
  const glow = ctx.createRadialGradient(w/2,h*0.05,10, w/2,h*0.05,w*0.6);
  glow.addColorStop(0,'rgba(216,180,106,.14)'); glow.addColorStop(1,'rgba(216,180,106,0)');
  ctx.fillStyle=glow; ctx.fillRect(0,0,w,g.keyTop);
  // horizon haze where the lanes dissolve into light
  const haze = ctx.createRadialGradient(w/2,h*0.10,4, w/2,h*0.10,w*0.30);
  haze.addColorStop(0,'rgba(240,217,168,.12)'); haze.addColorStop(1,'rgba(240,217,168,0)');
  ctx.fillStyle=haze; ctx.fillRect(0,0,w,h*0.3);

  // lane columns breathing in perspective
  for(let i=0;i<4;i++){
    if(i%2===0){
      ctx.fillStyle='rgba(255,255,255,.016)';
      laneQuad(g,i,0,g.keyTop); ctx.fill();
    }
  }
  // projected lane separators — brighter as they reach the keys
  ctx.lineWidth=1*dpr;
  for(let i=1;i<4;i++){
    const xt=w/2+(i-1.5)*(w/4)*0.40, xb=w/4*i;
    ctx.strokeStyle='rgba(240,217,168,.13)';
    ctx.beginPath(); ctx.moveTo(xt,0); ctx.lineTo(xb,g.keyTop); ctx.stroke();
    ctx.strokeStyle='rgba(240,217,168,.30)';
    ctx.beginPath(); ctx.moveTo((xt+xb)/2,g.keyTop/2); ctx.lineTo(xb,g.keyTop); ctx.stroke();
  }
  // pressed-lane wash + miss flash
  for(let i=0;i<4;i++){
    if(keyActive[i]){ ctx.fillStyle='rgba(216,180,106,.10)'; laneQuad(g,i,0,g.keyTop); ctx.fill(); }
    if(laneFlash[i]>0){ ctx.fillStyle=`rgba(255,80,95,${0.20*laneFlash[i]})`; laneQuad(g,i,0,g.keyTop); ctx.fill(); }
  }
  // soft diagonal light beams
  ctx.fillStyle='rgba(240,217,168,.035)';
  quad(w*0.08,0,w*0.30,0,w*0.16,g.keyTop,w*0.02,g.keyTop); ctx.fill();
  quad(w*0.92,0,w*0.70,0,w*0.84,g.keyTop,w*0.98,g.keyTop); ctx.fill();
  // drifting dust motes
  for(const m of dust){
    ctx.globalAlpha=m.a; ctx.fillStyle='#f0d9a8';
    ctx.fillRect(m.x*w, m.y*g.keyTop, m.s*dpr, m.s*dpr);
  }
  ctx.globalAlpha=1;

  // glossy black piano body the keys sit in
  const rimY = g.keyTop-9*dpr;
  const body=ctx.createLinearGradient(0,rimY,0,h);
  body.addColorStop(0,'#1e1e22'); body.addColorStop(0.2,'#0b0b0d'); body.addColorStop(1,'#000000');
  ctx.fillStyle=body; ctx.fillRect(0,rimY,w,h-rimY);
  ctx.fillStyle='rgba(240,217,168,.22)'; ctx.fillRect(0,rimY,w,1.5*dpr);

  // four playable ivory keys — exactly one quarter of the piano each
  const showHints = !keyHintsChk || keyHintsChk.checked;
  const letters=['D','F','J','K'];
  for(let i=0;i<4;i++){
    const kx0=w/4*i+2.5*dpr, kx1=w/4*(i+1)-2.5*dpr;
    const press = keyActive[i] ? 5*dpr : 0;
    const ky0=g.keyTop+3*dpr+press, ky1=h-4*dpr+press;
    const kf=ctx.createLinearGradient(0,ky0,0,ky1);
    kf.addColorStop(0,'#fffdf4'); kf.addColorStop(0.7,'#f1e7cf'); kf.addColorStop(1,'#d6c69c');
    ctx.fillStyle=kf; rr(kx0,ky0,kx1-kx0,ky1-ky0,5*dpr); ctx.fill();
    ctx.fillStyle='rgba(60,45,20,.20)';
    ctx.fillRect(kx0,ky0,2*dpr,ky1-ky0); ctx.fillRect(kx1-2*dpr,ky0,2*dpr,ky1-ky0);
    ctx.fillStyle='rgba(120,95,50,.22)';
    rr(kx0,ky1-g.keyH*0.30,kx1-kx0,g.keyH*0.30,5*dpr); ctx.fill();
    const glowA = Math.max(keyActive[i]?0.55:0, keyFlash[i]);
    if(glowA>0){
      ctx.save(); ctx.globalAlpha=Math.min(1,glowA);
      ctx.shadowColor='rgba(240,200,120,.95)'; ctx.shadowBlur=24*dpr;
      const kg=ctx.createLinearGradient(0,ky0,0,ky1);
      kg.addColorStop(0,'#fff3d0'); kg.addColorStop(1,'#e8b64c');
      ctx.fillStyle=kg; rr(kx0,ky0,kx1-kx0,ky1-ky0,5*dpr); ctx.fill();
      ctx.restore();
    }
    if(showHints){
      ctx.fillStyle = (keyActive[i]||keyFlash[i]>0.25) ? '#3a2c10' : '#5a513f';
      ctx.font=`800 ${15*dpr}px Sora, Inter, sans-serif`; ctx.textAlign='center';
      ctx.fillText(letters[i], (kx0+kx1)/2, ky1-g.keyH*0.11);
    }
  }

  const cur = getCurrentTime();
  const speedMul = parseFloat(speedSlider.value);
  const basePps = {easy:400, normal:540, hard:720, insane:920}[difficultySel.value] || 540;
  const pps = basePps*speedMul*dpr;
  const gap = Math.max(2*dpr, w*0.006);

  // luminous glass tiles ride their lane's projection down into its key
  for(const t of activeTiles){
    if((t.hit && t.type==='tap') || t.missed) continue;
    const yH = g.keyTop - (t.time-cur)*pps;
    const lh = t.type==='hold' ? (t.duration||0.5)*pps : Math.max(64*dpr, pps*0.15);
    const yT = yH-lh;
    if(yH < -160*dpr || yT > h+80*dpr) continue;
    const hx0=g.center(t.lane,yH)-g.half(yH)+gap, hx1=g.center(t.lane,yH)+g.half(yH)-gap;
    const tx0=g.center(t.lane,yT)-g.half(yT)+gap, tx1=g.center(t.lane,yT)+g.half(yT)-gap;
    // contact shadow for 3D depth
    ctx.fillStyle='rgba(0,0,0,.45)';
    quad(hx0+4*dpr,yH+7*dpr,hx1+4*dpr,yH+7*dpr,tx1+4*dpr,yT+7*dpr,tx0+4*dpr,yT+7*dpr); ctx.fill();
    const toHit = t.time-cur;
    ctx.save();
    if(!t.hit && toHit>0 && toHit<0.25){
      ctx.shadowColor='rgba(240,200,120,.9)'; ctx.shadowBlur=18*dpr*(1-toHit/0.25);
    }
    const tg=ctx.createLinearGradient(0,yT,0,yH);
    if(t.type==='hold'){
      tg.addColorStop(0,'rgba(206,170,120,.55)'); tg.addColorStop(1,'rgba(255,244,214,.94)');
    } else {
      tg.addColorStop(0,'rgba(188,158,108,.88)'); tg.addColorStop(0.45,'rgba(240,220,175,.96)'); tg.addColorStop(1,'#fff8e2');
    }
    ctx.fillStyle=tg;
    quad(hx0,yH,hx1,yH,tx1,yT,tx0,yT); ctx.fill();
    ctx.restore();
    ctx.strokeStyle = t.type==='hold' ? 'rgba(255,240,200,.9)' : 'rgba(216,180,106,.75)';
    ctx.lineWidth = 1.5*dpr;
    quad(hx0,yH,hx1,yH,tx1,yT,tx0,yT); ctx.stroke();
    // bright strike edge where the tile will meet its key
    ctx.strokeStyle='rgba(255,255,255,.9)'; ctx.lineWidth=2.5*dpr;
    ctx.beginPath(); ctx.moveTo(hx0+3*dpr,yH-3*dpr); ctx.lineTo(hx1-3*dpr,yH-3*dpr); ctx.stroke();
    // diagonal glass shine
    ctx.fillStyle='rgba(255,255,255,.10)';
    quad(hx0,yH,hx0+(hx1-hx0)*0.34,yH,tx0+(tx1-tx0)*0.22,yT,tx0,yT); ctx.fill();
    if(t.type==='hold'){
      ctx.strokeStyle='rgba(255,250,230,.85)';
      ctx.lineWidth=Math.max(2*dpr,(hx1-hx0)*0.10);
      ctx.beginPath();
      ctx.moveTo((hx0+hx1)/2,yH-8*dpr); ctx.lineTo((tx0+tx1)/2,yT+8*dpr);
      ctx.stroke();
    }
  }
  for(let i=particles.length-1;i>=0;i--){
    const p=particles[i]; p.t+=dt; p.x+=p.vx*dt; p.y+=p.vy*dt; p.vy+=560*dt;
    if(p.t>=p.life){ particles.splice(i,1); continue; }
    ctx.globalAlpha = 1-p.t/p.life; ctx.fillStyle=p.col;
    const ps=(p.s||2.2)*dpr;
    ctx.fillRect(p.x*dpr, p.y*dpr, ps, ps); ctx.globalAlpha=1;
  }
  for(let i=feedbacks.length-1;i>=0;i--){
    const f=feedbacks[i]; f.t+=dt; f.y-=46*dt;
    if(f.t>=f.life){ feedbacks.splice(i,1); continue; }
    ctx.globalAlpha = 1-f.t/f.life;
    ctx.font = `800 ${15*dpr}px Sora, Inter, sans-serif`; ctx.textAlign='center';
    ctx.lineWidth=4*dpr; ctx.strokeStyle='rgba(0,0,0,.65)';
    ctx.strokeText(f.text, f.x*dpr, f.y*dpr);
    ctx.fillStyle=f.col; ctx.fillText(f.text, f.x*dpr, f.y*dpr);
    ctx.globalAlpha=1;
  }
  // impact rings blooming across the struck key
  for(let i=ripples.length-1;i>=0;i--){
    const r=ripples[i]; r.t+=dt;
    if(r.t>=r.life){ ripples.splice(i,1); continue; }
    const k = r.t/r.life;
    ctx.globalAlpha = (1-k)*0.7; ctx.strokeStyle=r.col; ctx.lineWidth=2*dpr;
    ctx.beginPath(); ctx.ellipse(r.x*dpr, r.y, (10+k*46)*dpr, (4+k*13)*dpr, 0, 0, Math.PI*2); ctx.stroke();
    ctx.globalAlpha=1;
  }
}
function rr(x,y,w,h,r){
  r=Math.min(r,h/2,w/2);
  ctx.beginPath();
  ctx.moveTo(x+r,y); ctx.arcTo(x+w,y,x+w,y+h,r); ctx.arcTo(x+w,y+h,x,y+h,r);
  ctx.arcTo(x,y+h,x,y,r); ctx.arcTo(x,y,x+w,y,r); ctx.closePath();
}
function quad(x0,y0,x1,y1,x2,y2,x3,y3){
  ctx.beginPath();
  ctx.moveTo(x0,y0); ctx.lineTo(x1,y1); ctx.lineTo(x2,y2); ctx.lineTo(x3,y3);
  ctx.closePath();
}
function laneQuad(g,lane,y0,y1){
  quad(g.center(lane,y0)-g.half(y0),y0, g.center(lane,y0)+g.half(y0),y0,
       g.center(lane,y1)+g.half(y1),y1, g.center(lane,y1)-g.half(y1),y1);
}

/* ---------- loop ---------- */
let loopRaf=null;
function loop(){
  loopRaf = requestAnimationFrame(loop);
  const cur = getCurrentTime();
  if(songDuration>0){
    progBar.style.width = (Math.min(1,Math.max(0,cur/songDuration))*100)+'%';
    progText.textContent = `${Math.floor(Math.max(0,cur))} / ${Math.floor(songDuration)} seconds`;
    if(cur >= songDuration-0.05 && isPlaying){ endGame(false); return; }
  }
  for(const t of activeTiles){
    if(t.hit || t.missed) continue;
    if(t.type==='hold' && t.holding){
      if(cur >= t.time+(t.duration||0.5)){
        t.holding=false; score+=70; combo++; if(combo>bestCombo)bestCombo=combo;
        perfect++; updateHud(); spawnFeedback(t.lane,'HELD','#1f9d55');
      }
      continue;
    }
    if(cur > t.time+0.16){
      t.missed=true; miss++; combo=0; laneFlash[t.lane]=Math.max(laneFlash[t.lane],0.8); updateHud();
      if(hudGrade){ hudGrade.textContent='MISS'; hudGrade.style.color='#ff6b7a'; }
      if(currentMode==='classic'){ spawnFeedback(t.lane,'MISS','#ff6b7a'); endGame(true); return; }
      if(currentMode==='arcade'){ hp=Math.max(0,hp-13); spawnFeedback(t.lane,'MISS','#ff6b7a'); if(hp<=0){ endGame(true); return; } }
      else spawnFeedback(t.lane,'MISS','#c9a0a6');
    }
  }
  // preset room tone: soft melody bed
  if(!customAudioBuffer && isPlaying){
    for(const t of activeTiles){
      if(t._played) continue;
      if(Math.abs(t.time-cur)<0.02 && !t.hit && !t.missed){ playPianoTone(t.midi, 0.4, 0.1); t._played=true; }
    }
  }
  draw(performance.now());
}

function showOverlay(k, title, desc){
  overlayKicker.textContent=k; overlayTitle.textContent=title; overlayDesc.textContent=desc;
  overlay.classList.remove('hidden');
}
function hideOverlay(){ overlay.classList.add('hidden'); }

function endGame(failed){
  isPlaying=false; isPaused=false;
  stopAudio();
  if(loopRaf) cancelAnimationFrame(loopRaf);
  const acc = accuracy();
  let rank='D';
  if(acc>=98&&miss===0) rank='S+'; else if(acc>=95) rank='S';
  else if(acc>=88) rank='A'; else if(acc>=75) rank='B'; else if(acc>=60) rank='C';
  $('#resScore').textContent=score.toLocaleString('en-US'); $('#resCombo').textContent=bestCombo;
  $('#resAcc').textContent=acc.toFixed(1)+'%'; $('#resRank').textContent=rank;
  $('#resultKicker').textContent = failed?'Ended early':'Finished';
  $('#resultTitle').textContent = failed?'Out of tune':'A clean performance';
  $('#resultSub').textContent = failed
    ? (currentMode==='classic'?'One miss ends a Classic run. Arcade forgives; Zen never judges.':`HP empty · rank ${rank}`)
    : `${customName||currentPreset.title} · rank ${rank} · ${acc}%`;
  try{ $('#resultDialog').showModal(); }catch(e){}
  showOverlay(failed?'Out of tune':'Finished', customName||currentPreset.title, failed?'Restart and take it from the top.':'Lovely. Play again or choose another piece.');
  $('#btnPlay').style.display='inline-block'; $('#btnPause').style.display='none';
}

/* ---------- transport ---------- */
$('#btnPlay').onclick = startGame;
$('#overlayPlay').onclick = startGame;
$('#btnPause').onclick = ()=>{
  if(!isPlaying) return;
  if(isPaused){
    isPaused=false; $('#btnPause').textContent='Pause';
    if(customAudioBuffer) startAudio(); else presetStartPerf = performance.now()-pauseOffset*1000;
  } else {
    pauseOffset=getCurrentTime(); isPaused=true; $('#btnPause').textContent='Resume'; stopAudio();
  }
};
$('#btnRestart').onclick = ()=>{ pauseOffset=0; isPaused=false; stopAudio(); if(loopRaf)cancelAnimationFrame(loopRaf); isPlaying=false; resetGameState(); progBar.style.width='0%'; progText.textContent=`0 / ${Math.floor(songDuration)} seconds`; $('#btnPlay').style.display='inline-block'; $('#btnPause').style.display='none'; showOverlay('Ready', customName||currentPreset.title, 'Press play.'); draw(0); };
$('#btnRetry').onclick = ()=>{ try{$('#resultDialog').close();}catch(e){} pauseOffset=0; startGame(); };

async function startGame(){
  if(tiles.length===0) await buildTilesForCurrent();
  if(isPlaying && !isPaused) return;
  hideOverlay();
  await doCountdown();
  isPlaying=true; isPaused=false;
  $('#btnPlay').style.display='none'; $('#btnPause').style.display='inline-block'; $('#btnPause').textContent='Pause';
  getAudioCtx();
  if(pauseOffset===0) resetGameState();
  else activeTiles.forEach(t=>{ if(t.time>pauseOffset) t._played=false; });
  startAudio();
  if(loopRaf) cancelAnimationFrame(loopRaf);
  loop();
}
function doCountdown(){
  return new Promise(res=>{
    let n=3; countdownEl.textContent=n; countdownEl.classList.add('show');
    const iv=setInterval(()=>{
      n--;
      if(n>0) countdownEl.textContent=n;
      else if(n===0) countdownEl.textContent='·';
      else { clearInterval(iv); countdownEl.classList.remove('show'); res(); }
    }, 400);
  });
}

/* ---------- files ---------- */
dropzone.addEventListener('click', ()=>fileInput.click());
dropzone.addEventListener('dragover', e=>{e.preventDefault(); dropzone.classList.add('drag');});
dropzone.addEventListener('dragleave', ()=>dropzone.classList.remove('drag'));
dropzone.addEventListener('drop', e=>{ e.preventDefault(); dropzone.classList.remove('drag'); const f=e.dataTransfer.files[0]; if(f) handleFile(f); });
fileInput.addEventListener('change', ()=>{ const f=fileInput.files[0]; if(f) handleFile(f); });
$('#btnLoadUrl').onclick = async ()=>{
  const url = urlInput.value.trim(); if(!url) return;
  fileNameEl.textContent = 'Fetching…';
  try{
    const res = await fetch(url); const buf = await res.arrayBuffer();
    const decoded = await getAudioCtx().decodeAudioData(buf.slice(0));
    setCustomBuffer(decoded, url.split('/').pop().split('?')[0] || 'URL track', url);
  }catch(e){ fileNameEl.textContent = 'Could not load URL — needs a direct audio link.'; }
};
function setCustomBuffer(decoded, name, objUrl){
  customAudioBuffer = decoded; customName = name;
  analysisCache = null; analysisFor = null; chartMeta = null; // force fresh analysis
  if(customObjectUrl && !String(customObjectUrl).startsWith('http')){ try{URL.revokeObjectURL(customObjectUrl);}catch(e){} }
  customObjectUrl = objUrl;
  try{ audioEl.src = objUrl; }catch(e){}
  fileNameEl.textContent = `${name} · ${formatTime(decoded.duration)}`;
  buildTilesForCurrent().then(renderSongs);
}
async function handleFile(file){
  fileNameEl.textContent = 'Decoding '+file.name+'…';
  $('#analyzeRow').style.display='flex';
  try{
    const buf = await file.arrayBuffer();
    const decoded = await getAudioCtx().decodeAudioData(buf);
    const url = URL.createObjectURL(file);
    setCustomBuffer(decoded, file.name, url);
  }catch(e){
    fileNameEl.textContent = 'Could not decode — try MP3 / WAV / OGG.';
    $('#analyzeRow').style.display='none';
  }
}

/* ---------- input: keyboard + unified pointer ---------- */
const keyMap = {'d':0,'f':1,'j':2,'k':3,'1':0,'2':1,'3':2,'4':3,
  'arrowleft':0,'arrowdown':1,'arrowup':2,'arrowright':3};
function inField(t){ return t && (t.tagName==='INPUT'||t.tagName==='SELECT'||t.tagName==='TEXTAREA'); }
window.addEventListener('keydown', e=>{
  if(e.repeat || inField(e.target)) return;
  const k = e.key.toLowerCase();
  if(k in keyMap){ e.preventDefault(); const l=keyMap[k]; if(!keyActive[l]){ keyActive[l]=true; tryHit(l); } }
  else if((k===' '||k==='enter') && window.__introDone){ e.preventDefault(); if(isPlaying) $('#btnPause').click(); else startGame(); }
  else if(k.startsWith('arrow')) e.preventDefault();
});
window.addEventListener('keyup', e=>{
  if(inField(e.target)) return;
  const k = e.key.toLowerCase();
  if(k in keyMap){ const l=keyMap[k]; keyActive[l]=false; releaseHold(l); }
});
// one pointer pipeline for mouse + touch + pen; multi-touch tracked per pointerId
const activePtrs = new Map();
canvas.addEventListener('pointerdown', e=>{
  e.preventDefault();
  try{ canvas.setPointerCapture(e.pointerId); }catch(_){}
  const l = clientToLane(e.clientX, e.clientY);
  activePtrs.set(e.pointerId, l);
  keyActive[l]=true; tryHit(l);
});
function endPointer(e){
  if(!activePtrs.has(e.pointerId)) return;
  const l = activePtrs.get(e.pointerId);
  activePtrs.delete(e.pointerId);
  let still = false;
  activePtrs.forEach(v=>{ if(v===l) still=true; });
  if(!still){ releaseHold(l); keyActive[l]=false; }
}
canvas.addEventListener('pointerup', endPointer);
canvas.addEventListener('pointercancel', endPointer);
canvas.addEventListener('contextmenu', e=>e.preventDefault());

/* ---------- panel wiring ---------- */
$$('#modeSeg .seg-btn').forEach(b=> b.onclick=()=>{
  $$('#modeSeg .seg-btn').forEach(x=>x.classList.remove('active')); b.classList.add('active');
  currentMode=b.dataset.mode;
});
$$('#diffSeg .seg-btn').forEach(b=> b.onclick=()=>{
  $$('#diffSeg .seg-btn').forEach(x=>x.classList.remove('active')); b.classList.add('active');
  difficultySel.value=b.dataset.diff;
  buildTilesForCurrent();
});
widthSlider.addEventListener('input', ()=>{
  widthVal.textContent = widthSlider.value+'px';
  gameFrame.style.width = widthSlider.value+'px';
  // height stays CSS-driven (clamped to the viewport on PC) — canvas stretches
  resizeCanvas(); draw(0);
});
speedSlider.addEventListener('input', ()=> speedVal.textContent = parseFloat(speedSlider.value).toFixed(2).replace(/0$/,'')+'×');
holdNotesChk.addEventListener('change', ()=>buildTilesForCurrent());
offsetSlider.addEventListener('input', ()=>{
  const v = parseInt(offsetSlider.value,10);
  offsetVal.textContent = (v>=0?'+':'')+v+'ms';
});
offsetSlider.addEventListener('change', ()=>{ if(customAudioBuffer) buildTilesForCurrent(); });
const btnTheme = $('#btnTheme');
function paintThemeBtn(){ if(btnTheme) btnTheme.textContent = isDark() ? '☾' : '☀'; }
if(btnTheme) btnTheme.onclick = ()=>{
  const next = isDark() ? 'light' : 'dark';
  document.documentElement.dataset.theme = next;
  try{ localStorage.setItem('nocturne-theme', next); }catch(e){}
  paintThemeBtn(); draw(0); drawDebugView();
};
paintThemeBtn();
// header + panel upload shortcuts open the file picker
const openPicker = ()=>{ try{ fileInput.click(); }catch(e){} };
if($('#btnUpload')) $('#btnUpload').onclick = openPicker;
if($('#btnUpload2')) $('#btnUpload2').onclick = openPicker;
// key-hint letters on the 3D keys
if(keyHintsChk) keyHintsChk.addEventListener('change', ()=>draw(0));
// mobile drawers
const songsPanel = $('#songsPanel'), studioPanel = $('#studioPanel');
if($('#btnSongs')) $('#btnSongs').onclick = ()=>{
  songsPanel.classList.toggle('open'); studioPanel.classList.remove('open');
};
if($('#btnStudio')) $('#btnStudio').onclick = ()=>{
  studioPanel.classList.toggle('open'); songsPanel.classList.remove('open');
};
$('#btnHow').onclick = ()=>{ try{$('#howDialog').showModal();}catch(e){} };
$('#btnShare').onclick = ()=>{
  const text = `Nocturne — ${score} pts · ${bestCombo} combo on ${customName||currentPreset.title}`;
  if(navigator.share) navigator.share({title:'Nocturne', text}).catch(()=>{});
  else if(navigator.clipboard) navigator.clipboard.writeText(text).then(()=>{ mastSong.textContent='Score copied — paste it anywhere'; setTimeout(renderSongs, 1500); });
};

/* ---------- analysis debug view (waveform · beats · onsets · tiles) ---------- */
function drawDebugView(){
  const cv = $('#debugCanvas');
  if(!cv || !analysisCache || !customAudioBuffer) return;
  const dpr = Math.max(1, Math.min(2, window.devicePixelRatio||1));
  const W = Math.max(260, cv.clientWidth || 280), H = 120;
  cv.width = W*dpr; cv.height = H*dpr;
  const g = cv.getContext('2d'); g.scale(dpr, dpr);
  const dark = isDark();
  g.fillStyle = dark ? '#1c1913' : '#f7f3ea'; g.fillRect(0,0,W,H);
  const dur = analysisCache.duration;
  const X = t => (t/dur)*W;
  // waveform (channel 0, min/max columns)
  const data = customAudioBuffer.getChannelData(0);
  g.fillStyle = dark ? '#5c5546' : '#a89d83';
  const cols = Math.floor(W);
  for(let x=0;x<cols;x++){
    const a = Math.floor(x/cols*data.length), b = Math.floor((x+1)/cols*data.length);
    let mn=1, mx=-1;
    for(let i=a;i<b;i+=Math.max(1,Math.floor((b-a)/24))){ const v=data[i]; if(v<mn)mn=v; if(v>mx)mx=v; }
    const y1 = H*0.5 - mx*H*0.42, y2 = H*0.5 - mn*H*0.42;
    g.fillRect(x, y1, 1, Math.max(1, y2-y1));
  }
  // beats
  g.strokeStyle = '#c9a227'; g.lineWidth = 1;
  (analysisCache.beats||[]).forEach((t,i)=>{
    if(i%4===0){ g.globalAlpha=0.9; } else g.globalAlpha=0.35;
    g.beginPath(); g.moveTo(X(t),0); g.lineTo(X(t),H); g.stroke();
  });
  g.globalAlpha=1;
  // onsets (candidates)
  g.fillStyle = '#4d8a5e';
  analysisCache.candidates.forEach(c=>{ g.fillRect(X(c.time)-1, H-26, 2, 10); });
  // final tiles
  g.fillStyle = dark ? '#ece5d3' : '#171512';
  tiles.forEach(t=>{ g.beginPath(); g.arc(X(t.time), 12, 3, 0, Math.PI*2); g.fill(); });
  const s = $('#debugStats');
  if(s && chartMeta){
    s.textContent = `${chartMeta.bpm} BPM · grid ${chartMeta.beatOffset.toFixed(2)}s · conf ${Math.round(chartMeta.confidence*100)}% · v${chartMeta.analysisVersion}`;
  }
}

/* ---------- init ---------- */
renderSongs();
buildTilesForCurrent();
window.addEventListener('resize', ()=>{ resizeCanvas(); draw(0); });
if(typeof ResizeObserver !== 'undefined'){
  new ResizeObserver(()=>{ resizeCanvas(); draw(0); }).observe(gameFrame);
}
resizeCanvas(); draw(0);
document.addEventListener('visibilitychange', ()=>{ if(document.hidden && isPlaying && !isPaused) $('#btnPause').click(); });
