/* Nocturne — 3D intro piano (Three.js r128, no modules).
   Builds a small ebony piano keyboard in a dark room, plays a soft
   generative wave across the keys, camera drifts, and on entry
   dollies forward then fades. Falls back to 2D canvas if WebGL/CDN fails. */
(function(){
  const intro = document.getElementById('intro');
  const meta = document.getElementById('introMeta');
  const enterBtn = document.getElementById('enterBtn');
  const canvas = document.getElementById('piano3d');
  let done = false, raf = null;

  window.__introDone = false;
  function finish(){
    if(done) return; done = true;
    window.__introDone = true;
    intro.classList.add('leave');
    if(raf) cancelAnimationFrame(raf);
    setTimeout(()=>{ intro.style.display='none'; }, 1000);
  }
  enterBtn.addEventListener('click', ()=>{
    // camera push-in before fade
    window.__introExit = true;
    setTimeout(finish, 650);
  });
  // allow skip with key
  window.addEventListener('keydown', e=>{ if(!done && (e.key==='Enter'||e.key===' ')) {/* don't hijack game space after */} });

  function setMeta(t){ if(meta) meta.textContent = t; }

  // Fallback 2D shimmer if THREE missing
  if(typeof THREE === 'undefined'){
    setMeta('tap “Take your seat” to begin');
    const c2 = canvas.getContext('2d');
    let t = 0;
    (function loop2(){
      if(done) return;
      raf = requestAnimationFrame(loop2);
      t += 0.02;
      const w = canvas.width = canvas.clientWidth, h = canvas.height = canvas.clientHeight;
      c2.fillStyle = '#0d0c0a'; c2.fillRect(0,0,w,h);
      const n = 14, kw = w / n;
      for(let i=0;i<n;i++){
        const p = Math.sin(t*1.4 - i*0.55)*0.5+0.5;
        c2.fillStyle = `rgba(242,237,225,${0.06+p*0.16})`;
        c2.fillRect(i*kw+2, h*0.28, kw-4, h*0.4);
        c2.fillStyle = '#f2ede1';
        c2.fillRect(i*kw+2, h*0.28 + (1-p)*40, kw-4, 3);
      }
    })();
    return;
  }

  try{
    const renderer = new THREE.WebGLRenderer({canvas, antialias:true, alpha:false});
    renderer.setPixelRatio(Math.min(2, window.devicePixelRatio||1));
    const scene = new THREE.Scene();
    scene.background = new THREE.Color(0x0d0c0a);
    scene.fog = new THREE.Fog(0x0d0c0a, 14, 30);

    const camera = new THREE.PerspectiveCamera(42, 1, 0.1, 100);
    camera.position.set(0, 5.6, 12.2);
    camera.lookAt(0, 1.5, 0);
    camera.userData.baseZ = 12.2;

    // lights — warm single spot like a stage lamp, no neon
    scene.add(new THREE.AmbientLight(0xbfb49a, 0.35));
    const spot = new THREE.SpotLight(0xffe9bd, 1.5, 40, Math.PI/5, 0.45);
    spot.position.set(0, 10, 6);
    spot.target.position.set(0,1.1,0);
    scene.add(spot); scene.add(spot.target);
    const rim = new THREE.DirectionalLight(0x8f9bb0, 0.25);
    rim.position.set(-6, 4, -6); scene.add(rim);

    // floor
    const floor = new THREE.Mesh(
      new THREE.PlaneGeometry(60, 60),
      new THREE.MeshStandardMaterial({color:0x12110e, roughness:0.9, metalness:0.05})
    );
    floor.rotation.x = -Math.PI/2; floor.position.y = -0.75; scene.add(floor);

    // piano body + keys — lifted so the title clears it
    const piano = new THREE.Group(); piano.position.y = 1.35; scene.add(piano);
    const ebony = new THREE.MeshStandardMaterial({color:0x191611, roughness:0.35, metalness:0.25});
    const ivory = new THREE.MeshStandardMaterial({color:0xf1ead9, roughness:0.5, metalness:0.02});
    const ebonyKey = new THREE.MeshStandardMaterial({color:0x0f0e0c, roughness:0.4, metalness:0.15});

    const body = new THREE.Mesh(new THREE.BoxGeometry(11.4, 0.9, 3.4), ebony);
    body.position.y = -0.28; piano.add(body);
    const fallboard = new THREE.Mesh(new THREE.BoxGeometry(11.4, 0.5, 0.5), ebony);
    fallboard.position.set(0, 0.35, -1.45); piano.add(fallboard);

    const N = 15, KW = 0.68, whiteKeys = [], blackKeys = [];
    const blackAfter = new Set([0,1,3,4,5,7,8,10,11,12]); // pattern
    for(let i=0;i<N;i++){
      const k = new THREE.Mesh(new THREE.BoxGeometry(KW, 0.32, 2.5), ivory.clone());
      k.position.set((i-(N-1)/2)*(KW+0.045), 0.32, 0.25);
      piano.add(k); whiteKeys.push(k);
      if(blackAfter.has(i) && i < N-1){
        const b = new THREE.Mesh(new THREE.BoxGeometry(0.42, 0.5, 1.4), ebonyKey.clone());
        b.position.set((i-(N-1)/2)*(KW+0.045) + (KW+0.045)/2, 0.52, -0.25);
        piano.add(b); blackKeys.push(b);
      }
    }

    // falling tiles preview above keys (thin ivory slabs)
    const tiles = [];
    const tileGeo = new THREE.BoxGeometry(0.62, 0.06, 1.1);
    for(let i=0;i<16;i++){
      const m = new THREE.Mesh(tileGeo, new THREE.MeshStandardMaterial({
        color:0xe9e2d2, roughness:0.6, transparent:true, opacity:0.9}));
      resetTile(m, true);
      scene.add(m); tiles.push(m);
    }
    const KEY_Y = 1.35 + 0.32; // top of white keys in world space
    function resetTile(m, randomY){
      const lane = Math.floor(Math.random()*N);
      m.position.set((lane-(N-1)/2)*(KW+0.045), randomY? 3.2+Math.random()*8 : 9+Math.random()*3, 0.25);
      m.userData.lane = lane;
      m.userData.speed = 1.6 + Math.random()*1.6;
    }

    // dust particles
    const dustGeo = new THREE.BufferGeometry();
    const dustN = 220, pos = new Float32Array(dustN*3);
    for(let i=0;i<dustN;i++){ pos[i*3]=(Math.random()-0.5)*22; pos[i*3+1]=Math.random()*9; pos[i*3+2]=(Math.random()-0.5)*14; }
    dustGeo.setAttribute('position', new THREE.BufferAttribute(pos,3));
    const dust = new THREE.Points(dustGeo, new THREE.PointsMaterial({color:0xcbb87a, size:0.045, transparent:true, opacity:0.5}));
    scene.add(dust);

    function resize(){
      const w = intro.clientWidth, h = intro.clientHeight;
      renderer.setSize(w, h, false);
      camera.aspect = w/h; camera.updateProjectionMatrix();
      // pull back on narrow screens so the full keyboard stays in frame
      camera.userData.baseZ = camera.aspect < 0.85 ? 15.5 : 12.2;
    }
    window.addEventListener('resize', resize); resize();

    const clock = new THREE.Clock();
    let exitT = 0;
    setMeta('a quiet room · tap “Take your seat”');

    function animate(){
      if(done) return;
      raf = requestAnimationFrame(animate);
      const t = clock.getElapsedTime();

      // generative wave: press keys in a slow arpeggio
      whiteKeys.forEach((k,i)=>{
        const ph = Math.sin(t*1.15 - i*0.62);
        const press = Math.max(0, ph-0.55)/0.45; // 0..1
        k.position.y = 0.32 - press*0.14;
        k.material.emissive = k.material.emissive || new THREE.Color(0);
        k.material.emissive.setHex(press>0.02 ? 0x33270e : 0x000000);
      });
      blackKeys.forEach((k,i)=>{
        const ph = Math.sin(t*1.5 - i*0.9 + 1.3);
        const press = Math.max(0, ph-0.62)/0.38;
        k.position.y = 0.52 - press*0.12;
      });

      // tiles drift down toward keys, fade near bottom
      tiles.forEach(m=>{
        m.position.y -= m.userData.speed * 0.022;
        m.material.opacity = Math.max(0, Math.min(0.9, (m.position.y-KEY_Y)*0.28));
        if(m.position.y < KEY_Y + 0.1){ resetTile(m, false); }
      });

      dust.rotation.y = t*0.012;

      // camera: gentle drift, then push in on exit
      if(window.__introExit){
        exitT += 0.02;
        camera.position.z = camera.userData.baseZ - exitT*9;
        camera.position.y = 5.6 - exitT*2.6;
        camera.lookAt(0, 1.5 - exitT*0.2, 0);
      } else {
        camera.position.x = Math.sin(t*0.16)*1.6;
        camera.position.z = camera.userData.baseZ + Math.sin(t*0.11)*0.5;
        camera.lookAt(0, 1.5, 0);
      }
      renderer.render(scene, camera);
    }
    animate();
  }catch(err){
    setMeta('tap “Take your seat” to begin');
    console.warn('3D intro failed, continuing:', err);
  }
})();
