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
const levelNote = $('#levelNote');
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
  {id:'interstellar', title:'Interstellar Theme', artist:'Piano', file:'Interstellar (Main Theme Piano) (320kbps).mp3', bpm:null, duration:null, _buf:null},
  {id:'heatwaves', title:'Heat Waves', artist:'Glass Animals · slowed + reverb', file:'glass animals - heat waves ( slowed to perfection + reverb ) (320kbps).mp3', bpm:null, duration:null, _buf:null},
  {id:'unstoppable', title:'Unstoppable', artist:'Sia', file:'Sia - Unstoppable (Official Video - Live from the Nostalgic For The Present Tour) (320 kbps).mp3', bpm:null, duration:null, _buf:null},
  {id:'aintworried', title:"I Ain't Worried", artist:'OneRepublic', file:'OneRepublic - I Ain\u2019t Worried (From \u201cTop Gun_ Maverick\u201d) [Official Music Video] (320kbps).mp3', bpm:null, duration:null, _buf:null},
  {id:'aroundworld', title:'Around The World', artist:'ATC · Instrumental remake', file:'ATC - Around the world (Instrumental remake).mp3', bpm:null, duration:null, _buf:null},
  {id:'wellerman', title:'Wellerman Remix', artist:'220 Kid × Billen Ted', file:'Wellerman (Sea Shanty _ 220 KID x Billen Ted Remix) _ Official Video (320kbps).mp3', bpm:null, duration:null, _buf:null},
  {id:'dadada', title:'Da Da Da (Jarico Remix)', artist:'VHWX Remastered', file:'[Da Da Da \u0414\u0430 \u0434\u0430 \u0434\u0430] Jarico Remix _ VHWX Remastered (320 kbps).mp3', bpm:null, duration:null, _buf:null},
  {id:'renai', title:'Renai Circulation', artist:'Namirin cover', file:'Renai Circulation\u300c\u604b\u611b\u30b5\u30fc\u30ad\u30e5\u30ec\u30fc\u30b7\u30e7\u30f3\u300d\u6b4c\u3063\u3066\u307f\u305f\u3010\uff0a\u306a\u307f\u308a\u3093\u3011 (320 kbps).mp3', bpm:null, duration:null, _buf:null},
  {id:'ltheme', title:"L's Theme", artist:'Death Note BGM', file:'L Theme Ringtone \uff5c Death Note BGM Ringtone \uff5c Death Note Ringtone \uff5c Download Link ⬇️⬇️.mp3', bpm:null, duration:null, _buf:null},
];

let currentPreset = PRESETS[0];
let currentMode = 'arcade';
let customAudioBuffer = null;
let customObjectUrl = null;
let customName = null;
let detectedBpm = null;
let uploadedFile = false; // false = bundled library song, true = user upload/URL
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
const LEVELS = {
  easy:   {rate:0.82, label:'Easy · 82% tempo'},
  normal: {rate:1.00, label:'Normal · original tempo'},
  hard:   {rate:1.18, label:'Hard · 118% tempo'}
};
function level(){ return LEVELS[difficultySel.value] || LEVELS.normal; }
function chartTimeScale(){ return 1 / level().rate; }
function setLevelLabel(){ if(levelNote) levelNote.textContent = level().label; }
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
    div.className = 'song' + (p.id===currentPreset.id && !uploadedFile ? ' active' : '');
    div.innerHTML = `<span class="song-num">${String(i+1).padStart(2,'0')}</span>
      <div class="song-meta"><b>${p.title}</b><span>${p.artist}</span></div>
      <span class="song-bpm">${p.bpm ?? '···'}</span>`;
    div.onclick = ()=>{
      uploadedFile = false;
      if(customObjectUrl && !String(customObjectUrl).startsWith('http')) URL.revokeObjectURL(customObjectUrl);
      customObjectUrl = null;
      try{ audioEl.pause(); audioEl.removeAttribute('src'); audioEl.load(); }catch(e){}
      currentPreset = p;
      fileNameEl.textContent = 'No file yet';
      customBadge.style.display = 'none';
      buildTilesForCurrent().then(()=>renderSongs());
    };
    list.appendChild(div);
  });
  const label = uploadedFile
    ? (customName + ' — custom')
    : (currentPreset.title + ' — ' + (currentPreset.bpm ?? '··· BPM'));
  mastSong.textContent = label;
}

/* Library songs are real audio (songs/): fetched + decoded on first select,
   then analysed and played through the standard pipeline below.
   No synthesized placeholder charts. */

/* Rhythm analysis lives in audio-analysis.js: Hann STFT -> multi-band log
   spectral flux -> adaptive threshold -> autocorrelation tempo -> beat phase
   search -> 1/4-beat quantization -> strength selection -> seeded lanes ->
   validation. Analysis runs once per import; difficulty only re-selects. */

/* ---------- library song loading ----------
   Two paths so the game works however it is opened:
   1) fetch('songs/…') — fast path when served over http(s).
   2) embedded songs/<id>-data.js via a classic <script> tag — script
      subresources are NOT blocked on file://, so double-clicking
      index.html works too. The base64 string is freed right after decode. */
function loadScriptFile(src){
  return new Promise((resolve, reject)=>{
    const s = document.createElement('script');
    const to = setTimeout(()=>{ s.remove(); reject(new Error('script timeout')); }, 180000);
    s.onload = ()=>{ clearTimeout(to); s.remove(); resolve(); };
    s.onerror = ()=>{ clearTimeout(to); s.remove(); reject(new Error('script load failed')); };
    s.src = src;
    document.head.appendChild(s);
  });
}
function b64ToArrayBuffer(b64){
  const bin = atob(b64);
  const len = bin.length;
  const bytes = new Uint8Array(len);
  const CH = 32768;
  for(let i=0;i<len;i+=CH){
    const n = Math.min(CH, len-i);
    for(let j=0;j<n;j++) bytes[i+j] = bin.charCodeAt(i+j);
  }
  return bytes.buffer;
}
/* Every track plays as a 1-minute run: longer audio is trimmed to 60s with
   a smooth 3s fade-out baked into a copied buffer (never the user file).
   Shorter tracks play whole. Analysis/playback downstream just see duration. */
const SONG_CAP = 60, FADE_OUT = 3;
function trimToMinute(buf){
  if(!buf || buf.duration <= SONG_CAP + 0.5) return buf;
  const sr = buf.sampleRate, len = Math.floor(SONG_CAP * sr);
  const out = getAudioCtx().createBuffer(buf.numberOfChannels, len, sr);
  const fade = Math.floor(FADE_OUT * sr);
  for(let c=0;c<buf.numberOfChannels;c++){
    const src = buf.getChannelData(c), dst = out.getChannelData(c);
    dst.set(src.subarray(0, len));
    for(let i=0;i<fade;i++){ const k=i/fade; dst[len-1-i] *= k*k; }
  }
  return out;
}
async function ensurePresetBuffer(p, setP){
  if(p._buf) return p._buf;
  try{
    setP(0.05, 'Loading song…');
    const res = await fetch('songs/' + encodeURIComponent(p.file));
    if(!res.ok) throw new Error('HTTP ' + res.status);
    p._buf = await getAudioCtx().decodeAudioData(await res.arrayBuffer());
    return p._buf;
  }catch(e){ /* fall through to embedded data */ }
  try{
    setP(0.10, 'Loading embedded audio…');
    await loadScriptFile('songs/' + p.id + '-data.js');
    const uri = (window.__SONG_DATA || {})[p.id];
    if(!uri) throw new Error('missing embedded data');
    const b64 = uri.slice(uri.indexOf(',') + 1);
    try{ delete window.__SONG_DATA[p.id]; }catch(_){}
    setP(0.22, 'Decoding audio…');
    p._buf = await getAudioCtx().decodeAudioData(b64ToArrayBuffer(b64));
    return p._buf;
  }catch(e2){
    console.error(e2);
    const err = new Error('unavailable');
    err.friendly = 'Could not load "' + p.title + '". Pick Upload Music and choose the MP3 file instead.';
    throw err;
  }
}

/* ---------- build ---------- */
async function buildTilesForCurrent(){
  abortRunForChartUpdate();
  showOverlay('Loading track', currentPreset?.title || customName || 'Preparing song', 'Preparing audio…');
  const row = $('#analyzeRow');
  row.style.display = 'flex';
  const setP = (f, txt)=>{
    $('#analyzeBar').style.width = Math.round(f*100)+'%';
    if(txt){ $('#analyzeText').textContent = txt; overlayDesc.textContent = txt; }
  };
  setP(0.05, 'Preparing…');
  await new Promise(r=>setTimeout(r, 60));
  if(!uploadedFile && currentPreset){
    // bundled library song: fetch + decode once, then run the standard
    // analysis/playback pipeline on the real audio (no synth placeholders)
    if(!currentPreset._buf){
      try{
        await ensurePresetBuffer(currentPreset, setP);
        currentPreset._buf = trimToMinute(currentPreset._buf);
        currentPreset.duration = currentPreset._buf.duration;
      }catch(err){
        console.error(err);
        const why = (err && err.friendly) ||
          ('Could not load song file' + (err && err.message ? ' (' + err.message + ')' : '') + '.');
        fileNameEl.textContent = why;
        // leave the board in a clean empty state with an explanatory overlay
        tiles = []; songDuration = 0;
        pauseOffset = 0; resetGameState();
        progBar.style.width = '0%';
        progText.textContent = '0 / 0 seconds';
        showOverlay('Song failed to load', currentPreset.title, why + ' Select another track or upload a file instead.');
        row.style.display = 'none';
        draw(0);
        return;
      }
    }
    customAudioBuffer = currentPreset._buf;
    customName = currentPreset.title;
  }
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
    tiles = res.tiles.map(t=>({...t, time:t.time*chartTimeScale(), duration:(t.duration||0)*chartTimeScale()}));
    chartMeta = res.meta;
    songDuration = customAudioBuffer.duration * chartTimeScale();
    if(res.validation.warnings.length) console.warn('[chart]', res.validation.warnings);
    if(!res.validation.valid) console.error('[chart]', res.validation.errors);
    const conf = Math.round(res.confidence*100);
    detectLabel.textContent = `${res.bpm} BPM · ${res.tiles.length} notes`;
    customBadge.style.display = 'block';
    customBadge.textContent = `${uploadedFile ? 'Custom track' : 'Library track'} · ${res.bpm} BPM · ${res.stats.rawOnsets} onsets → ${res.stats.acceptedEvents} events → ${res.tiles.length} tiles`;
    overlayKicker.textContent = 'Custom track · analysed';
    overlayTitle.textContent = customName || 'Your song';
    overlayDesc.textContent = `${res.bpm} BPM · ${res.tiles.length} notes. Press play.`;
    mastSong.textContent = (customName||'Custom') + ` — ${res.bpm} BPM`;
    drawDebugView();
    if(!uploadedFile && currentPreset){
      // store detected tempo on the library entry for the song list
      currentPreset.bpm = res.bpm;
      overlayKicker.textContent = 'Library track · analysed';
      renderSongs();
    }
    setP(1, 'Ready to play');
  } else {
    fileNameEl.textContent = 'No song loaded.';
    row.style.display = 'none';
    return;
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
    audioSource.playbackRate.value = level().rate;
    audioSource.connect(ac.destination);
    // Start audio and chart from the same scheduled audio-clock instant.
    // This removes the old fixed 20ms drift between an audible beat and tile.
    const launchAt = ac.currentTime + 0.06;
    startTime = launchAt - pauseOffset;
    try{ audioSource.start(launchAt, Math.max(0,pauseOffset * level().rate)); }catch(e){ audioSource.start(); }
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
  const vpY = -H*0.18;
  // A wide keyboard and a narrower horizon make the lanes feel like one
  // continuous piano roll, rather than four disconnected square columns.
  const spread = y => {
    let t = (y-vpY)/(keyTop-vpY);
    t = Math.min(1, Math.max(0, t));
    return 0.48 + 0.52*t;
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
    if(currentMode==='arcade'){ score=Math.max(0,score-5); combo=0; updateHud(); spawnFeedback(lane,'−5','#ff6b7a'); }
    else if(currentMode==='classic'){ combo=0; updateHud(); }
    return;
  }
  handleHit(best, bestD<=PERFECT_W ? 'perfect' : bestD<=GREAT_W ? 'great' : 'good');
}
const isDark = ()=>document.documentElement.dataset.theme!=='light';
// Per-mode board palette: the whole 3D stage (tiles, glow, particles,
// keys, lanes) re-themes with the selected mode. Classic stays champagne
// gold, arcade burns red, zen runs mint-neon cyberpunk cyan.
const PALETTES = {
  classic: {
    hit:'#f0d9a8', great:'#cfd8ea', good:'#8f887a',
    glow:'240,200,120', line:'240,217,168',
    tile:['rgba(188,158,108,.88)','rgba(240,220,175,.96)','#fff8e2'],
    edge:'216,180,106',
    hold:['rgba(91,67,145,.82)','rgba(151,115,218,.92)','#ead8ff'], holdEdge:'226,205,255',
    key:['#fff3d0','#e8b64c'],
    dust:'#f0d9a8', parts:['#f0d9a8','#d8b46a','#fff6e0'], glyph:'#d8b46a'
  },
  arcade: {
    hit:'#ffb3ab', great:'#ffd0c2', good:'#8f887a',
    glow:'255,77,94', line:'255,150,140',
    tile:['rgba(190,90,80,.88)','rgba(255,150,135,.96)','#fff0ea'],
    edge:'255,93,93',
    hold:['rgba(150,40,70,.85)','rgba(230,70,110,.92)','#ffd9e2'], holdEdge:'255,120,150',
    key:['#ffe3dc','#ff5d5d'],
    dust:'#ff9a7a', parts:['#ff8a7a','#ff5d5d','#ffe9e2'], glyph:'#ff5d5d'
  },
  zen: {
    hit:'#a8f4ff', great:'#d7f9ff', good:'#8f887a',
    glow:'41,216,255', line:'141,243,255',
    tile:['rgba(70,150,180,.88)','rgba(140,220,245,.96)','#eafcff'],
    edge:'41,216,255',
    hold:['rgba(30,110,140,.85)','rgba(60,190,230,.92)','#d9f7ff'], holdEdge:'141,243,255',
    key:['#e2fbff','#29d8ff'],
    dust:'#8df3ff', parts:['#8df3ff','#29d8ff','#eafcff'], glyph:'#29d8ff'
  }
};
function pal(){ return PALETTES[currentMode] || PALETTES.classic; }
function handleHit(tile, grade){
  tile.hit = true;
  if(tile.type==='hold'){ tile.holding=true; holdState[tile.lane]=true; }
  // Traditional Piano Tiles rewards a clean run without runaway combo values.
  score += grade==='perfect' ? 10 : grade==='great' ? 7 : 4;
  combo++; if(combo>bestCombo) bestCombo=combo;
  if(grade==='perfect') perfect++; else if(grade==='great') great++; else good++;
  keyFlash[tile.lane]=1; // the piano key ignites as the tile lands in it
  spawnParticles(tile.lane, grade);
  const g = stageGeom(canvas.width, canvas.height);
  const P = pal();
  ripples.push({x:g.center(tile.lane, g.keyTop), y:g.keyTop, t:0, life:0.4,
    col: grade==='perfect' ? P.hit : `rgba(${P.line},.65)`});
  const fcol = grade==='perfect' ? P.hit : grade==='great' ? P.great : P.good;
  spawnFeedback(tile.lane, grade.toUpperCase(), fcol);
  if(hudGrade){
    hudGrade.textContent = grade.toUpperCase();
    hudGrade.style.color = fcol;
  }
  if(Math.random()<0.3) spawnFeedback(tile.lane, Math.random()<0.5?'♪':'♫', P.glyph);
  // score pop on perfects, combo pulse each 25
  try{
    if(grade==='perfect') hudScore.animate([{transform:'scale(1.22)'},{transform:'scale(1)'}],{duration:160,easing:'ease-out'});
    if(combo%25===0) hudCombo.animate([{transform:'scale(1.35)'},{transform:'scale(1)'}],{duration:200,easing:'ease-out'});
  }catch(_){}
  // tier bursts fire inside updateHud → paintComboFX (covers hits; misses re-arm silently)
  playPianoTone(tile.midi, 0.32, grade==='perfect'?0.42:grade==='great'?0.36:0.3);
  updateHud();
}
function releaseHold(lane){
  holdState[lane]=false;
  const now = getCurrentTime();
  for(const t of activeTiles){
    if(t.lane!==lane || t.type!=='hold' || !t.holding || !t.hit) continue;
    const tail = t.time+(t.duration||0.5);
    if(now >= tail-0.18){
      score += 5;
      spawnFeedback(lane,'HELD','#1f9d55');
      playPianoTone(t.midi+7, 0.16, 0.24);
    } else {
      combo=0; miss++;
      if(currentMode==='classic'){ t.holding=false; endGame(true); return; }
      if(currentMode==='arcade') score=Math.max(0,score-12);
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
  const P = pal();
  const cols = grade==='perfect' ? P.parts : [P.glyph,'#8f887a',P.hit];
  for(let i=0;i<14;i++) particles.push({x, y, vx:(Math.random()-0.5)*310, vy:-Math.random()*330-55,
    life:0.42+Math.random()*0.34, t:0, col:cols[i%3], s:1.6+Math.random()*2.6});
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
  const fsS = $('#fsScore'), fsC = $('#fsCombo');
  if(fsS) fsS.textContent = score.toLocaleString('en-US');
  if(fsC) fsC.textContent = combo + '×';
  hudAcc.textContent = accuracy().toFixed(1)+'%';
  statBest.textContent = bestCombo;
  statPerfect.textContent = perfect;
  const sg = $('#statGreat'); if(sg) sg.textContent = great;
  statGood.textContent = good; statMiss.textContent = miss;
  hpFill.style.width = hp+'%';
  paintComboFX();
}

/* ---------- combo atmosphere ---------- */
// Escalating reward ladder: subtle white whisper at ×2, heating through
// champagne → gold → amber → orange → rose → violet → ice. Bursts fire when
// the combo ENTERS a tier (tracked via burstTier, reset with the combo),
// so early game already feels alive without spamming every single hit.
const TIER_AT = [2,3,5,8,12,20,35,50,100,200,400];
const TIER_POWER = [.14,.22,.32,.45,.55,.7,.8,.9,1,1,1];
// Combo reward ramp per mode: classic heats champagne→violet→ice,
// arcade burns white→red→magenta, zen runs white→cyan→mint neon.
const TIER_SETS = {
  classic:['#ffffff','#ffffff','#e8e2d2','#f0d9a8','#ffd23f','#ff9a3c','#ff7a3c','#ff5d7a','#c084fc','#7df9ff','#ffffff'],
  arcade:['#ffffff','#ffe9e2','#ffd0c2','#ffab8a','#ff6b5e','#ff3b57','#ff2e63','#ff5da2','#c84bff','#ff8a7a','#ffffff'],
  zen:['#ffffff','#eaffff','#d7f9ff','#8df3ff','#29d8ff','#4dffa6','#00e5a0','#29d8ff','#8df3ff','#4dffa6','#ffffff']
};
function TIERS(){ return TIER_SETS[currentMode] || TIER_SETS.classic; }
let burstTier = -1;
function tierIndex(c){ let t = -1; for(let i = 0; i < TIER_AT.length; i++) if(c >= TIER_AT[i]) t = i; return t; }
function hexA(hex, a){
  const n = parseInt(hex.slice(1), 16);
  return `rgba(${(n >> 16) & 255},${(n >> 8) & 255},${n & 255},${a})`;
}
function paintComboFX(){
  // drives the board aura + website background glow (see --cg in style.css)
  try{ document.body.style.setProperty('--cg', Math.min(1, combo/60).toFixed(3)); }catch(_){}
  const t = tierIndex(combo);
  if(t > burstTier){ burstTier = t; comboBurst({color:TIERS()[t], power:TIER_POWER[t]}); }
  else if(t < burstTier) burstTier = t; // combo broke — silently re-arm
}
function comboBurst(tier){
  const col = tier.color, p = tier.power;
  // edge-of-screen pulse in the tier color
  const f = $('#edgeFlash');
  if(f){ try{ f.style.boxShadow = `inset 0 0 130px 34px ${hexA(col, .55)}`; f.animate([{opacity:0},{opacity:.25 + .65 * p, offset:.25},{opacity:0}],{duration:400 + 350 * p, easing:'ease-out'}); }catch(_){} }
  // score slam scaled by tier (main HUD + fullscreen HUD)
  const s = 1.1 + .45 * p;
  [hudScore, $('#fsScore')].forEach(el=>{ if(!el) return; try{ el.animate([{transform:`scale(${s})`},{transform:'scale(1)'}],{duration:280 + 200 * p, easing:'cubic-bezier(.2,1.6,.4,1)'});}catch(_){} });
  // board frame ignites in the tier color
  const fr = $('#gameFrame');
  if(fr){
    fr.style.borderColor = col;
    fr.style.boxShadow = `0 0 0 2px ${hexA(col, .9)}, 0 0 ${40 + 60 * p}px ${hexA(col, .55)}, 0 30px 80px rgba(0,0,0,.7)`;
    clearTimeout(fr._flashT);
    fr._flashT = setTimeout(()=>{ fr.style.borderColor = ''; fr.style.boxShadow = ''; }, 300 + 350 * p);
  }
  // center splash for the bigger moments
  if(p >= .45) comboSplash(col);
}
function comboSplash(col){
  const sp = $('#comboSplash');
  if(!sp) return;
  sp.textContent = combo + ' COMBO';
  sp.style.color = col;
  try{ sp.animate([{opacity:0, transform:'scale(.6)'},{opacity:1, transform:'scale(1.12)', offset:.3},{opacity:1, transform:'scale(1)', offset:.55},{opacity:0, transform:'scale(1.05)'}],{duration:750, easing:'ease-out'}); }catch(_){}
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
  glow.addColorStop(0,`rgba(${pal().glow},.14)`); glow.addColorStop(1,`rgba(${pal().glow},0)`);
  ctx.fillStyle=glow; ctx.fillRect(0,0,w,g.keyTop);
  // horizon haze where the lanes dissolve into light
  const haze = ctx.createRadialGradient(w/2,h*0.10,4, w/2,h*0.10,w*0.30);
  haze.addColorStop(0,`rgba(${pal().line},.12)`); haze.addColorStop(1,`rgba(${pal().line},0)`);
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
  const topSpread = g.spread(0);
  for(let i=1;i<4;i++){
    // i is a boundary (1..3), not a lane center.  This keeps every rail
    // attached to its corresponding piano-key seam.
    const xt=w/2+(i-2)*(w/4)*topSpread, xb=w/4*i;
    ctx.strokeStyle=`rgba(${pal().line},.13)`;
    ctx.beginPath(); ctx.moveTo(xt,0); ctx.lineTo(xb,g.keyTop); ctx.stroke();
    ctx.strokeStyle=`rgba(${pal().line},.30)`;
    ctx.beginPath(); ctx.moveTo((xt+xb)/2,g.keyTop/2); ctx.lineTo(xb,g.keyTop); ctx.stroke();
  }
  // pressed-lane wash + miss flash
  for(let i=0;i<4;i++){
    if(keyActive[i]){ ctx.fillStyle=`rgba(${pal().glow},.10)`; laneQuad(g,i,0,g.keyTop); ctx.fill(); }
    if(laneFlash[i]>0){ ctx.fillStyle=`rgba(255,80,95,${0.07*laneFlash[i]})`; laneQuad(g,i,0,g.keyTop); ctx.fill(); }
  }
  // soft diagonal light beams
  ctx.fillStyle=`rgba(${pal().line},.035)`;
  quad(w*0.08,0,w*0.30,0,w*0.16,g.keyTop,w*0.02,g.keyTop); ctx.fill();
  quad(w*0.92,0,w*0.70,0,w*0.84,g.keyTop,w*0.98,g.keyTop); ctx.fill();
  // drifting dust motes
  for(const m of dust){
    ctx.globalAlpha=m.a; ctx.fillStyle=pal().dust;
    ctx.fillRect(m.x*w, m.y*g.keyTop, m.s*dpr, m.s*dpr);
  }
  ctx.globalAlpha=1;

  // glossy black piano body the keys sit in
  const rimY = g.keyTop-9*dpr;
  const body=ctx.createLinearGradient(0,rimY,0,h);
  body.addColorStop(0,'#1e1e22'); body.addColorStop(0.2,'#0b0b0d'); body.addColorStop(1,'#000000');
  ctx.fillStyle=body; ctx.fillRect(0,rimY,w,h-rimY);
  ctx.fillStyle=`rgba(${pal().line},.22)`; ctx.fillRect(0,rimY,w,1.5*dpr);

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
      ctx.shadowColor=`rgba(${pal().glow},.95)`; ctx.shadowBlur=24*dpr;
      const kg=ctx.createLinearGradient(0,ky0,0,ky1);
      kg.addColorStop(0,pal().key[0]); kg.addColorStop(1,pal().key[1]);
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
  // Screen-linear travel keeps the established, readable game cadence.
  const basePps = {easy:285, normal:355, hard:430}[difficultySel.value] || 355;
  const pps = basePps*dpr;
  const gap = Math.max(2*dpr, w*0.006);

  // luminous glass tiles ride their lane's projection down into its key
  for(const t of activeTiles){
    if((t.hit && t.type==='tap') || t.missed) continue;
    const toHit = t.time-cur;
    const yH = g.keyTop - toHit*pps;
    // Constant tap length: scaling length with lane spread made far tiles
    // short and near tiles long, so tails visibly sped up and caught up.
    // Lane widths still taper with perspective; only length stays fixed.
    // Tap length follows lane width (not fixed px): tiles keep the same tall
    // rectangle proportions at any board size instead of turning into flat
    // slabs on wide screens. Holds stay duration-mapped.
    const laneW = w/4-gap*2;
    const lh = t.type==='hold' ? (t.duration||0.5)*pps : Math.max(150*dpr, laneW*1.1, pps*0.42);
    const yT = yH-lh;
    if(yH < -160*dpr || yT > h+80*dpr) continue;
    // Tiles slide UNDER the piano keys: clamp the head at the key line so a
    // tile can never paint over the keys. The struck key lights up instead
    // (keyFlash + particles + impact ring fire on hit).
    const yHc = Math.min(yH, g.keyTop);
    if(yT >= yHc) continue; // fully consumed below the key line
    const hx0=g.center(t.lane,yHc)-g.half(yHc)+gap, hx1=g.center(t.lane,yHc)+g.half(yHc)-gap;
    const tx0=g.center(t.lane,yT)-g.half(yT)+gap, tx1=g.center(t.lane,yT)+g.half(yT)-gap;
    // contact shadow for 3D depth (skipped once the head is under the keys)
    if(yHc >= yH){
      ctx.fillStyle='rgba(0,0,0,.45)';
      quad(hx0+4*dpr,yHc+7*dpr,hx1+4*dpr,yHc+7*dpr,tx1+4*dpr,yT+7*dpr,tx0+4*dpr,yT+7*dpr); ctx.fill();
    }
    ctx.save();
    if(!t.hit && toHit>0 && toHit<0.25){
      ctx.shadowColor=`rgba(${pal().glow},.9)`; ctx.shadowBlur=18*dpr*(1-toHit/0.25);
    }
    const tg=ctx.createLinearGradient(0,yT,0,yHc);
    if(t.type==='hold'){
      tg.addColorStop(0,pal().hold[0]); tg.addColorStop(.55,pal().hold[1]); tg.addColorStop(1,pal().hold[2]);
    } else {
      tg.addColorStop(0,pal().tile[0]); tg.addColorStop(0.45,pal().tile[1]); tg.addColorStop(1,pal().tile[2]);
    }
    ctx.fillStyle=tg;
    quad(hx0,yHc,hx1,yHc,tx1,yT,tx0,yT); ctx.fill();
    ctx.restore();
    ctx.strokeStyle = t.type==='hold' ? `rgba(${pal().holdEdge},.98)` : `rgba(${pal().edge},.75)`;
    ctx.lineWidth = 1.5*dpr;
    quad(hx0,yHc,hx1,yHc,tx1,yT,tx0,yT); ctx.stroke();
    // bright strike edge where the tile meets its key
    ctx.strokeStyle='rgba(255,255,255,.9)'; ctx.lineWidth=2.5*dpr;
    ctx.beginPath(); ctx.moveTo(hx0+3*dpr,yHc-3*dpr); ctx.lineTo(hx1-3*dpr,yHc-3*dpr); ctx.stroke();
    // diagonal glass shine
    ctx.fillStyle='rgba(255,255,255,.10)';
    quad(hx0,yHc,hx0+(hx1-hx0)*0.34,yHc,tx0+(tx1-tx0)*0.22,yT,tx0,yT); ctx.fill();
    if(t.type==='hold'){
      ctx.strokeStyle='rgba(255,255,255,.9)';
      ctx.lineWidth=Math.max(2*dpr,(hx1-hx0)*0.055);
      ctx.beginPath();
      ctx.moveTo((hx0+hx1)/2,yHc-8*dpr); ctx.lineTo((tx0+tx1)/2,yT+8*dpr);
      ctx.stroke();
      ctx.fillStyle='rgba(255,255,255,.86)';
      ctx.font=`700 ${Math.max(8,10*dpr)}px Inter, sans-serif`; ctx.textAlign='center';
      ctx.fillText('HOLD', (hx0+hx1)/2, yHc-(yHc-yT)*0.32);
    }
  }
  for(let i=particles.length-1;i>=0;i--){
    const p=particles[i]; p.t+=dt; p.x+=p.vx*dt; p.y+=p.vy*dt; p.vy+=560*dt;
    if(p.t>=p.life){ particles.splice(i,1); continue; }
    ctx.globalAlpha = 1-p.t/p.life; ctx.fillStyle=p.col;
    const ps=(p.s||2.2)*dpr;
    // Particle positions are already in canvas pixels (stageGeom uses the
    // backing canvas dimensions), so do not scale them a second time on HiDPI.
    ctx.fillRect(p.x, p.y, ps, ps); ctx.globalAlpha=1;
  }
  for(let i=feedbacks.length-1;i>=0;i--){
    const f=feedbacks[i]; f.t+=dt; f.y-=46*dt;
    if(f.t>=f.life){ feedbacks.splice(i,1); continue; }
    ctx.globalAlpha = 1-f.t/f.life;
    ctx.font = `800 ${15*dpr}px Sora, Inter, sans-serif`; ctx.textAlign='center';
    ctx.lineWidth=4*dpr; ctx.strokeStyle='rgba(0,0,0,.65)';
    ctx.strokeText(f.text, f.x, f.y);
    ctx.fillStyle=f.col; ctx.fillText(f.text, f.x, f.y);
    ctx.globalAlpha=1;
  }
  // impact rings blooming across the struck key
  for(let i=ripples.length-1;i>=0;i--){
    const r=ripples[i]; r.t+=dt;
    if(r.t>=r.life){ ripples.splice(i,1); continue; }
    const k = r.t/r.life;
    ctx.globalAlpha = (1-k)*0.7; ctx.strokeStyle=r.col; ctx.lineWidth=2*dpr;
    ctx.beginPath(); ctx.ellipse(r.x, r.y, (10+k*46)*dpr, (4+k*13)*dpr, 0, 0, Math.PI*2); ctx.stroke();
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
        t.holding=false; score+=5; combo++; if(combo>bestCombo)bestCombo=combo;
        perfect++; updateHud(); spawnFeedback(t.lane,'HELD','#1f9d55');
      }
      continue;
    }
    if(cur > t.time+0.16){
      t.missed=true; miss++; combo=0; laneFlash[t.lane]=Math.max(laneFlash[t.lane],0.8); updateHud();
      if(hudGrade){ hudGrade.textContent='MISS'; hudGrade.style.color='#ff6b7a'; }
      if(currentMode==='classic'){ spawnFeedback(t.lane,'MISS','#ff6b7a'); endGame(true); return; }
      if(currentMode==='arcade'){ score=Math.max(0,score-10); spawnFeedback(t.lane,'−10','#ff6b7a'); updateHud(); }
      else spawnFeedback(t.lane,'MISS','#c9a0a6');
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
  let rank='D', rankLabel='Warming up', rankCls='rD';
  if(acc>=98&&miss===0){ rank='S+'; rankLabel='Flawless'; rankCls='rS'; }
  else if(acc>=95){ rank='S'; rankLabel='Superstar'; rankCls='rS'; }
  else if(acc>=88){ rank='A'; rankLabel='Excellent'; rankCls='rA'; }
  else if(acc>=75){ rank='B'; rankLabel='Great groove'; rankCls='rB'; }
  else if(acc>=60){ rank='C'; rankLabel='Solid'; rankCls='rC'; }
  $('#resScore').textContent=score.toLocaleString('en-US'); $('#resCombo').textContent=bestCombo;
  $('#resAcc').textContent=acc.toFixed(1)+'%';
  const rankEl=$('#resRank'); rankEl.textContent=rank; rankEl.className=rankCls;
  $('#resRankLabel').textContent=rankLabel;
  // judgment breakdown bars (share of all judged notes)
  const totJ = perfect+great+good+miss || 1;
  const fills=[['Perfect',perfect],['Great',great],['Good',good],['Miss',miss]];
  fills.forEach(([k,v])=>{
    $('#res'+k).textContent=v;
    const bar=$('#bar'+k); if(bar) bar.style.width=(100*v/totJ).toFixed(1)+'%';
  });
  // all-time best (local)
  let best=0; try{ best=parseInt(localStorage.getItem('nocturne-best')||'0',10)||0; }catch(e){}
  const isBest = score>best;
  if(isBest){ try{ localStorage.setItem('nocturne-best', String(score)); }catch(e){} }
  $('#resBest').hidden = !isBest;
  $('#resultKicker').textContent = failed?'Ended early':'Finished';
  $('#resultTitle').textContent = failed?'Out of tune':'A clean performance';
  $('#resultSub').textContent = failed
    ? (currentMode==='classic'?'One miss ends a Classic run. Arcade subtracts points; Zen never judges.':`Run ended · rank ${rank}`)
    : `${customName||currentPreset.title} · rank ${rank} · ${acc}%`;
  try{ $('#resultDialog').showModal(); }catch(e){}
  showOverlay(failed?'Out of tune':'Finished', customName||currentPreset.title, failed?'Restart and take it from the top.':'Lovely. Play again or choose another piece.');
  $('#pauseMenu').classList.remove('open');
  $('#btnPlay').style.display=''; $('#btnPause').style.display='none';
}

/* ---------- transport ---------- */
$('#btnPlay').onclick = startGame;
$('#overlayPlay').onclick = startGame;
function togglePause(){
  if(!isPlaying) return;
  if(isPaused){
    isPaused=false; $('#btnPause').textContent='⏸';
    $('#pauseMenu').classList.remove('open');
    if(customAudioBuffer) startAudio(); else presetStartPerf = performance.now()-pauseOffset*1000;
  } else {
    pauseOffset=getCurrentTime(); isPaused=true; $('#btnPause').textContent='▶'; stopAudio();
    $('#pauseSong').textContent = customName||currentPreset.title;
    $('#pauseMenu').classList.add('open');
  }
}
$('#btnPause').onclick = togglePause;
$('#btnResume').onclick = togglePause;
$('#btnRestart2').onclick = ()=>$('#btnRestart').click();
$('#btnFull2').onclick = ()=>$('#btnFull').click();
if($('#btnSong2')) $('#btnSong2').onclick = ()=>{
  // end the run and land on the ready screen with the song list open
  $('#pauseMenu').classList.remove('open');
  pauseOffset=0; isPlaying=false; isPaused=false;
  stopAudio();
  if(loopRaf) cancelAnimationFrame(loopRaf);
  resetGameState();
  progBar.style.width='0%';
  progText.textContent=`0 / ${Math.floor(songDuration)} seconds`;
  $('#btnPlay').style.display=''; $('#btnPause').style.display='none';
  showOverlay('Ready', customName||currentPreset.title, 'Pick a track to play.');
  $('#songsPanel').classList.add('open'); $('#studioPanel').classList.remove('open');
  draw(0);
};
$('#btnRestart').onclick = ()=>{ pauseOffset=0; isPaused=false; stopAudio(); if(loopRaf)cancelAnimationFrame(loopRaf); isPlaying=false; resetGameState(); progBar.style.width='0%'; progText.textContent=`0 / ${Math.floor(songDuration)} seconds`; $('#pauseMenu').classList.remove('open'); $('#btnPlay').style.display=''; $('#btnPause').style.display='none'; showOverlay('Ready', customName||currentPreset.title, 'Press play.'); draw(0); };
$('#btnRetry').onclick = ()=>{ try{$('#resultDialog').close();}catch(e){} pauseOffset=0; startGame(); };

async function startGame(){
  if(tiles.length===0) await buildTilesForCurrent();
  if(tiles.length===0 || !customAudioBuffer) return; // nothing loaded — stay on overlay
  if(isPlaying && !isPaused) return;
  hideOverlay();
  await doCountdown();
  isPlaying=true; isPaused=false;
  $('#pauseMenu').classList.remove('open');
  $('#btnPlay').style.display='none'; $('#btnPause').style.display=''; $('#btnPause').textContent='⏸';
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
  customAudioBuffer = trimToMinute(decoded); customName = name;
  uploadedFile = true;
  analysisCache = null; analysisFor = null; chartMeta = null; // force fresh analysis
  if(customObjectUrl && !String(customObjectUrl).startsWith('http')){ try{URL.revokeObjectURL(customObjectUrl);}catch(e){} }
  customObjectUrl = objUrl;
  try{ audioEl.src = objUrl; }catch(e){}
  fileNameEl.textContent = `${name} · ${formatTime(customAudioBuffer.duration)}`;
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
  else if((k===' '||k==='enter') && window.__introDone && tourIdx<0 && $('#modeHome').hidden){ e.preventDefault(); if(isPlaying) $('#btnPause').click(); else startGame(); }
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
/* ---------- modes: home select, themes, switch-anywhere ---------- */
const MODES = ['classic','arcade','zen'];
function setMode(m, silent){
  if(!MODES.includes(m)) m = 'arcade';
  currentMode = m;
  document.body.dataset.gamemode = m;
  $$('.mode-pick .seg-btn').forEach(x=>x.classList.toggle('active', x.dataset.mode===m));
  $$('#modeHome .mode-card').forEach(x=>x.classList.toggle('picked', x.dataset.mode===m));
  try{ localStorage.setItem('nocturne-mode', m); }catch(e){}
  if(!silent) draw(0);
}
$$('.mode-pick .seg-btn').forEach(b=> b.onclick=()=>{ setMode(b.dataset.mode); });
try{ setMode(localStorage.getItem('nocturne-mode') || 'arcade', true); }catch(e){ setMode('arcade', true); }
$$('#diffSeg .seg-btn').forEach(b=> b.onclick=()=>{
  $$('#diffSeg .seg-btn').forEach(x=>x.classList.remove('active')); b.classList.add('active');
  difficultySel.value=b.dataset.diff;
  setLevelLabel();
  buildTilesForCurrent();
});
holdNotesChk.addEventListener('change', ()=>buildTilesForCurrent());
offsetSlider.addEventListener('input', ()=>{
  const v = parseInt(offsetSlider.value,10);
  offsetVal.textContent = (v>=0?'+':'')+v+'ms';
});
offsetSlider.addEventListener('change', ()=>{ if(customAudioBuffer) buildTilesForCurrent(); });
const btnTheme = $('#btnTheme');
function paintThemeBtn(){
  const icon = isDark() ? '☾' : '☀';
  if(btnTheme) btnTheme.textContent = icon;
}
function abortRunForChartUpdate(){
  if(!isPlaying && !isPaused) return;
  isPlaying=false; isPaused=false; pauseOffset=0;
  stopAudio();
  if(loopRaf) cancelAnimationFrame(loopRaf);
  $('#btnPause').style.display='none';
  $('#btnPlay').style.display='';
}
if(btnTheme) btnTheme.onclick = ()=>{
  const next = isDark() ? 'light' : 'dark';
  document.documentElement.dataset.theme = next;
  try{ localStorage.setItem('nocturne-theme', next); }catch(e){}
  paintThemeBtn(); draw(0); drawDebugView();
};
paintThemeBtn();
// mobile drawer transport (masthead is hidden on phones): pause mirrors the
// navbar button, home quits to the landing page
if($('#btnDrawerPause')) $('#btnDrawerPause').onclick = ()=>$('#btnPause').click();
if($('#btnDrawerHome')) $('#btnDrawerHome').onclick = goHome;
// header + panel upload shortcuts open the file picker
const openPicker = ()=>{ try{ fileInput.click(); }catch(e){} };
if($('#btnUpload')) $('#btnUpload').onclick = openPicker;
if($('#btnUpload2')) $('#btnUpload2').onclick = openPicker;
// key-hint letters on the 3D keys
if(keyHintsChk) keyHintsChk.addEventListener('change', ()=>draw(0));
// mobile drawers
const songsPanel = $('#songsPanel'), studioPanel = $('#studioPanel');
$('#btnFoldSongs').onclick = ()=>{
  songsPanel.classList.toggle('folded');
  $('#btnFoldSongs').textContent = songsPanel.classList.contains('folded') ? '›' : '‹';
};
$('#btnFoldStudio').onclick = ()=>{
  studioPanel.classList.toggle('folded');
  $('#btnFoldStudio').textContent = studioPanel.classList.contains('folded') ? '‹' : '›';
};
$('#btnCloseSongs').onclick = ()=>songsPanel.classList.remove('open');
$('#btnCloseStudio').onclick = ()=>studioPanel.classList.remove('open');
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
setLevelLabel();
buildTilesForCurrent();
window.addEventListener('resize', ()=>{ resizeCanvas(); draw(0); });
if(typeof ResizeObserver !== 'undefined'){
  new ResizeObserver(()=>{ resizeCanvas(); draw(0); }).observe(gameFrame);
}
resizeCanvas(); draw(0);
document.addEventListener('visibilitychange', ()=>{ if(document.hidden && isPlaying && !isPaused) $('#btnPause').click(); });

/* ---------- fullscreen stage ---------- */
const gameOuter = $('#gameOuter');
function paintFsPause(){
  const b = $('#fsPause'), ref = $('#btnPause');
  if(!b || !ref) return;
  b.style.display = ref.style.display;
  b.textContent = ref.textContent;
  const dp = $('#btnDrawerPause');
  if(dp) dp.textContent = ref.textContent;
}
function goHome(){
  // quit any run and return to the landing (mode select) page
  pauseOffset=0; isPlaying=false; isPaused=false;
  stopAudio();
  if(loopRaf) cancelAnimationFrame(loopRaf);
  resetGameState();
  progBar.style.width='0%';
  progText.textContent=`0 / ${Math.floor(songDuration)} seconds`;
  $('#pauseMenu').classList.remove('open');
  try{ $('#resultDialog').close(); }catch(e){}
  $('#btnPlay').style.display=''; $('#btnPause').style.display='none';
  showOverlay('Ready', customName||currentPreset.title, 'Press play.');
  showModeHome();
  draw(0);
}
function paintFsBtn(){
  const t = $('#btnFull');
  if(t) t.textContent = document.body.classList.contains('stage-full') ? '✕' : '⛶';
}
async function setStageFull(on){
  const want = on !== undefined ? on : !document.body.classList.contains('stage-full');
  document.body.classList.toggle('stage-full', want);
  paintFsBtn(); paintFsPause(); resizeCanvas(); draw(0);
  if(want && gameOuter && gameOuter.requestFullscreen){
    try{ await gameOuter.requestFullscreen(); }catch(e){ /* CSS-only fill still applies */ }
  } else if(!want && document.fullscreenElement){
    try{ await document.exitFullscreen(); }catch(e){}
  }
}
// mirror pause/play visibility+label (covers pause toggle, start, restart, game over)
new MutationObserver(paintFsPause).observe($('#btnPause'), {attributes:true, childList:true, subtree:true});
document.addEventListener('fullscreenchange', ()=>{
  document.body.classList.toggle('stage-full', !!document.fullscreenElement);
  paintFsBtn(); paintFsPause(); resizeCanvas(); draw(0);
});
if($('#btnFull')) $('#btnFull').onclick = ()=>setStageFull();
if($('#fsPause')) $('#fsPause').onclick = ()=>$('#btnPause').click();
paintFsBtn(); paintFsPause();

/* ---------- first-run tutorial ---------- */
const TUTE_KEY = 'nocturne-tutorial';
const tuteDone = ()=>{ try{ return !!localStorage.getItem(TUTE_KEY); }catch(_){ return true; } };
const tuteSet = v=>{ try{ localStorage.setItem(TUTE_KEY, v); }catch(_){} };
const TOUR_STEPS = [
  {title:'Your piano', text:'Tiles fall down four glowing lanes. Each lane ends on its own piano key — strike the tile exactly as it lands.', sel:'#gameFrame'},
  {title:'How to strike', text:'Desktop: D F J K or arrow keys. Mobile: tap the keys themselves. A gold key-flash plus burst means PERFECT. Long tiles: hold until the tail passes.', rect:()=>{ const r=$('#gameFrame').getBoundingClientRect(); return {x:r.x, y:r.y+r.height*0.58, width:r.width, height:r.height*0.42}; }},
  {title:'Pick a song', text:'Nine built-in tracks, analysed on-device into real beat-mapped charts. The BPM badge fills in once a song is analysed.', el:()=>{ const l=$('#songList'); return (l && l.firstElementChild) || $('#songsPanel'); }},
  {title:'Your music', text:'Drop any MP3, WAV, OGG or FLAC here — or paste a URL — and the game builds tiles from its actual rhythm. Nothing ever uploads.', sel:'#dropzone'},
  {title:'Tempo levels', text:'Easy plays at 82% tempo, Normal full speed, Hard 118%. Same chart, different tempo — holds included.', sel:'#diffSeg'},
  {title:'Modes', text:'Classic ends on a single miss. Arcade forgives and subtracts points. Zen never judges. Switch anytime from the ⏸ pause menu or Studio settings.', sel:'#studioModeSeg'},
  {title:'Ready?', text:'Press Play for the countdown, then play. Restart, pause and ⛶ fullscreen live in the top bar.', sel:'#overlayPlay', final:true},
];
let tourIdx = -1;
function tourTarget(st){
  if(st.rect){ try{ const r = st.rect(); if(r && r.width > 4 && r.height > 4) return r; }catch(_){} return null; }
  const el = typeof st.el === 'function' ? st.el() : $(st.sel);
  if(!el) return null;
  // open collapsed containers so the target can be measured
  const songs = el.closest && el.closest('#songsPanel');
  const studio = el.closest && el.closest('#studioPanel');
  if(songs){
    if(songs.classList.contains('folded')) $('#btnFoldSongs')?.click();
    if(getComputedStyle(songs).display === 'none') $('#btnSongs')?.click();
  }
  if(studio){
    if(studio.classList.contains('folded')) $('#btnFoldStudio')?.click();
    if(getComputedStyle(studio).display === 'none') $('#btnStudio')?.click();
  }
  try{ el.scrollIntoView({block:'nearest'}); }catch(_){}
  const r = el.getBoundingClientRect();
  if(r.width < 4 || r.height < 4) return null;
  return r;
}
function buildDots(){
  const d = $('#tourDots'); if(!d) return; d.innerHTML = '';
  TOUR_STEPS.forEach((_, i)=>{ const s = document.createElement('span'); if(i === tourIdx) s.classList.add('on'); d.appendChild(s); });
}
function positionTour(){
  if(tourIdx < 0) return;
  showTourStep(tourIdx);
}
function showTourStep(i){
  tourIdx = i;
  const st = TOUR_STEPS[i];
  // phone fix: collapse both drawers first so a panel opened on a previous
  // step can't cover the next target; tourTarget re-opens the one it needs
  songsPanel.classList.remove('open'); studioPanel.classList.remove('open');
  let r = tourTarget(st);
  if(!r){ // target unavailable (tiny viewport etc.) → skip ahead, or finish
    if(i + 1 < TOUR_STEPS.length) return showTourStep(i + 1);
    return endTour(true);
  }
  const pad = 10;
  const ring = $('#tourRing');
  ring.style.left = Math.max(4, r.x - pad) + 'px';
  ring.style.top = Math.max(4, r.y - pad) + 'px';
  ring.style.width = (r.width + pad * 2) + 'px';
  ring.style.height = (r.height + pad * 2) + 'px';
  $('#tourKicker').textContent = `Step ${i + 1} of ${TOUR_STEPS.length}`;
  $('#tourTitle').textContent = st.title;
  $('#tourText').textContent = st.text;
  buildDots();
  $('#tourBack').style.visibility = i === 0 ? 'hidden' : 'visible';
  $('#tourNext').textContent = st.final ? 'Start playing 🎹' : 'Next →';
  const card = $('#tourCard');
  const cw = Math.min(340, innerWidth - 24);
  card.style.width = cw + 'px';
  const ch = card.offsetHeight;
  let cx = Math.min(Math.max(12, r.x), innerWidth - cw - 12);
  let cy = r.y + r.height + 16;
  if(cy + ch > innerHeight - 12) cy = Math.max(12, r.y - ch - 16);
  card.style.left = cx + 'px';
  card.style.top = cy + 'px';
  // re-measure once next frame: drawers/panels animate open, so the first
  // measurement can land mid-transition
  if(!st._settled){
    st._settled = true;
    requestAnimationFrame(()=>{ st._settled = false; if(tourIdx===i) showTourStep(i); });
  }
}
function startTour(){
  if(isPlaying || tourIdx >= 0) return;
  $('#tourMask').hidden = false;
  showTourStep(0);
  window.addEventListener('resize', positionTour);
}
function endTour(finished){
  $('#tourMask').hidden = true;
  tourIdx = -1;
  window.removeEventListener('resize', positionTour);
  if(finished){
    tuteSet('done');
    if(!isPlaying){ try{ $('#overlayPlay').click(); }catch(_){} }
  } else tuteSet('skipped');
}
function maybeShowTutorial(){
  if(tuteDone() || isPlaying || tourIdx >= 0) return;
  try{ $('#tuteWelcome').showModal(); }catch(_){}
}
if($('#tourNext')) $('#tourNext').onclick = ()=>{ if(tourIdx >= TOUR_STEPS.length - 1) endTour(true); else showTourStep(tourIdx + 1); };
if($('#tourBack')) $('#tourBack').onclick = ()=>{ if(tourIdx > 0) showTourStep(tourIdx - 1); };
if($('#tourSkip')) $('#tourSkip').onclick = ()=>endTour(false);
if($('#btnTutePlay')) $('#btnTutePlay').onclick = ()=>{ try{ $('#tuteWelcome').close(); }catch(_){} startTour(); };
if($('#btnTuteSkip')) $('#btnTuteSkip').onclick = ()=>{ tuteSet('skipped'); try{ $('#tuteWelcome').close(); }catch(_){} };
if($('#btnTourReplay')) $('#btnTourReplay').onclick = ()=>{ try{ $('#howDialog').close(); }catch(_){} startTour(); };
// mode select home: shown after the intro room fades, every launch
function showModeHome(){
  const last = currentMode;
  $$('#modeHome .mode-card').forEach(c=>c.classList.toggle('picked', c.dataset.mode===last));
  $('#modeHomeSub').textContent = 'Three ways to play the same piano. Last time: ' + last[0].toUpperCase() + last.slice(1) + ' — press 1, 2 or 3.';
  $('#modeHome').hidden = false;
  requestAnimationFrame(()=>$('#modeHome').classList.add('open'));
}
function hideModeHome(){
  $('#modeHome').classList.remove('open');
  $('#modeHome').hidden = true;
}
let toastT = null;
function showToast(msg, ms=3600){
  const t = $('#toast'); if(!t) return;
  t.textContent = msg; t.classList.add('show');
  clearTimeout(toastT); toastT = setTimeout(()=>t.classList.remove('show'), ms);
}
$$('#modeHome .mode-card').forEach(c=> c.onclick=()=>{
  setMode(c.dataset.mode);
  hideModeHome();
  showToast('Mode set — change it anytime from the ⏸ pause menu or Studio settings.');
  maybeShowTutorial();
});
document.addEventListener('keydown', e=>{
  if($('#modeHome').hidden || inField(e.target)) return;
  const map = {'1':'classic','2':'arcade','3':'zen'};
  const m = map[e.key.toLowerCase()];
  if(m){ const card = $$('#modeHome .mode-card').find(c=>c.dataset.mode===m); if(card) card.click(); }
});
// welcome first-timers once the intro room has faded
if($('#enterBtn')) $('#enterBtn').addEventListener('click', ()=>setTimeout(showModeHome, 1200));
