/* Nocturne rhythm analysis v3 — UMD (browser + node).
 *
 * Pipeline:
 *   PCM mono -> DC removal / light normalization / pre-emphasis
 *   -> Hann-windowed STFT (FRAME 2048, HOP 512) -> RMS + silence gate
 *   -> per-band log spectral flux (LOW 20-200 / MID 200-2000 / HIGH 2000-10000 Hz)
 *      + chroma-change flux (harmonic/melodic attacks: piano, vocals)
 *   -> combined onset envelope -> adaptive threshold (local mean + k*std)
 *   -> peak picking (parabolic interpolation, min 80ms separation)
 *   -> global tempo via envelope autocorrelation (60-200 BPM, octave-normalized)
 *   -> DYNAMIC beat tracking: anchor phase + walked grid with local
 *      interval re-fits (continuity-clamped), so the grid bends with drift
 *   -> quantization to the LOCAL 1/4-beat grid (max ~100ms snap)
 *   -> strength scoring -> difficulty selection (same analysis)
 *   -> constrained lane assignment (seeded, deterministic)
 *   -> chart validation + repair
 *
 * v3 changes (why):
 *   1. Removed the beat-grid fallback that invented near-zero-strength tiles
 *      at beats with no onset evidence. Sparse music now yields sparse
 *      charts; tiles only ever trace to real detected onsets.
 *   2. Replaced the rigid global grid with a walking beat tracker: tempo and
 *      phase are re-fit in rolling windows with continuity clamps, so rubato
 *      and mid-song tempo changes stay tracked instead of drifting off.
 *   3. Added a chroma-change (harmonic) onset detector voiced alongside the
 *      percussive flux, and parametrized the band weights (W_LOW/W_MID/
 *      W_HIGH/W_HARM), so soft piano attacks and vocal phrasing are detected
 *      instead of only drums and cymbals.
 *
 * Tile TIMING always derives from the audio. Seeded PRNG is used only for
 * lane presentation (and never for timing).
 */
(function (root, factory) {
  if (typeof module !== 'undefined' && module.exports) module.exports = factory();
  else root.NocturneAnalysis = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  var ANALYSIS_VERSION = 3;
  var FRAME = 2048;
  var HOP = 512;
  var MIN_ONSET_GAP = 0.08;      // 80ms minimum onset separation
  var MAX_QUANT_ERR = 0.055;     // preserve the audible onset; avoid loose beat snaps
  var BPM_MIN = 60, BPM_MAX = 200;

  // pThr: event power needed before a cross-hand double is considered.
  // The game intentionally caps simultaneous notes at two.
  var DIFF = {
    easy:   { maxRate: 1.35, minGap: 0.42, subs: { '1': 1 },                    dbl: 0.06, dblDense: 0.05, pThr: 0.66 },
    normal: { maxRate: 1.90, minGap: 0.24, subs: { '1': 1, '1/2': 1 },           dbl: 0.13, dblDense: 0.18, pThr: 0.57 },
    hard:   { maxRate: 2.55, minGap: 0.22, subs: { '1': 1, '1/2': 1, '1/4': 1 }, dbl: 0.16, dblDense: 0.22, pThr: 0.48 },
    insane: { maxRate: 3.0,  minGap: 0.18, subs: { '1': 1, '1/2': 1, '1/4': 1 }, dbl: 0.18, dblDense: 0.24, pThr: 0.45 }
  };

  /* ---------- utils ---------- */
  function mulberry32(seed) {
    var a = seed >>> 0;
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function hashSamples(x, sr) {
    var h = 2166136261;
    var step = Math.max(1, Math.floor(x.length / 20000));
    for (var i = 0; i < x.length; i += step) {
      var q = (x[i] * 32767) | 0;
      h ^= (q & 0xffff); h = Math.imul(h, 16777619);
    }
    h ^= (sr | 0); h = Math.imul(h, 16777619);
    h ^= x.length; h = Math.imul(h, 16777619);
    return h >>> 0;
  }
  function medianOf(arr) {
    var s = arr.slice().sort(function (a, b) { return a - b; });
    var m = s.length >> 1;
    return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
  }

  /* ---------- FFT (iterative radix-2, real input) ---------- */
  var twiddleCache = {};
  function getTwiddles(n) {
    if (twiddleCache[n]) return twiddleCache[n];
    var stages = [];
    for (var len = 2; len <= n; len <<= 1) {
      var ang = (-2 * Math.PI) / len;
      stages.push({ len: len, wr: Math.cos(ang), wi: Math.sin(ang) });
    }
    twiddleCache[n] = stages;
    return stages;
  }
  // in-place magnitude spectrum of real frame (length must be power of two)
  function magnitudeSpectrum(re, im, out) {
    var n = re.length;
    // bit-reversal
    for (var i = 1, j = 0; i < n; i++) {
      var bit = n >> 1;
      for (; j & bit; bit >>= 1) j ^= bit;
      j ^= bit;
      if (i < j) {
        var tr = re[i]; re[i] = re[j]; re[j] = tr;
        var ti = im[i]; im[i] = im[j]; im[j] = ti;
      }
    }
    var stages = getTwiddles(n);
    for (var s = 0; s < stages.length; s++) {
      var len = stages[s].len, wr0 = stages[s].wr, wi0 = stages[s].wi;
      for (var k = 0; k < n; k += len) {
        var wr = 1, wi = 0;
        for (var m = 0; m < len / 2; m++) {
          var ur = re[k + m], ui = im[k + m];
          var vr = re[k + m + len / 2] * wr - im[k + m + len / 2] * wi;
          var vi = re[k + m + len / 2] * wi + im[k + m + len / 2] * wr;
          re[k + m] = ur + vr; im[k + m] = ui + vi;
          re[k + m + len / 2] = ur - vr; im[k + m + len / 2] = ui - vi;
          var nwr = wr * wr0 - wi * wi0;
          wi = wr * wi0 + wi * wr0; wr = nwr;
        }
      }
    }
    var half = n / 2;
    for (var b = 0; b <= half; b++) out[b] = Math.sqrt(re[b] * re[b] + im[b] * im[b]) / n;
    return out;
  }

  /* ---------- step 1: preprocess ---------- */
  function preprocess(samples) {
    var n = samples.length;
    var out = new Float32Array(n);
    var mean = 0;
    for (var i = 0; i < n; i++) mean += samples[i];
    mean /= Math.max(1, n);
    var peak = 0;
    for (var j = 0; j < n; j++) {
      var v = samples[j] - mean;
      out[j] = v;
      var a = Math.abs(v);
      if (a > peak) peak = a;
    }
    // light normalization: lift quiet recordings, never crush dynamics
    var g = peak > 1e-6 ? Math.min(3, 0.9 / peak) : 1;
    // gentle pre-emphasis (high-pass) to surface hats/transients
    var prev = 0;
    for (var k = 0; k < n; k++) {
      var x = out[k] * g;
      out[k] = x - 0.5 * prev;
      prev = x;
    }
    return { data: out, peak: peak };
  }

  /* ---------- step 2: STFT frames + bands ---------- */
  function bandEdges(sr) {
    var binHz = sr / FRAME;
    function range(lo, hi) {
      return [Math.max(1, Math.floor(lo / binHz)), Math.min(FRAME / 2, Math.ceil(hi / binHz))];
    }
    return { low: range(20, 200), mid: range(200, 2000), high: range(2000, 10000) };
  }

  // Onset weights. The percussive bands catch drums/transients; HARM catches
  // harmonic change (piano attacks, vocal phrasing) that high-band flux
  // misses. v2 tilted permanently toward percussion (high-band dominant and
  // nothing harmonic); v3 voices both detectors and lets the p95
  // normalization below settle their relative scale per song.
  var W_LOW = 0.40, W_MID = 0.30, W_HIGH = 0.60, W_HARM = 0.90;

  function frameAnalysis(data, sr, onProgress) {
    var edges = bandEdges(sr);
    var hann = new Float32Array(FRAME);
    for (var i = 0; i < FRAME; i++) hann[i] = 0.5 * (1 - Math.cos((2 * Math.PI * i) / FRAME));
    var nFrames = Math.max(1, Math.floor((data.length - FRAME) / HOP));
    var fps = sr / HOP;
    var re = new Float64Array(FRAME), im = new Float64Array(FRAME), mag = new Float64Array(FRAME / 2 + 1);
    var prev = new Float64Array(FRAME / 2 + 1);
    // chroma classes for the melodic band (200-5000 Hz): bin -> pitch class
    // 0..11, or -1 outside the band. Precomputed once per analysis.
    var binHz = sr / FRAME;
    var chromaCls = new Int8Array(FRAME / 2 + 1);
    for (var cb = 0; cb <= FRAME / 2; cb++) {
      var cf = cb * binHz;
      if (cf < 200 || cf > 5000) { chromaCls[cb] = -1; continue; }
      var pc = Math.round(12 * Math.log(cf / 440) / Math.LN2) % 12;
      chromaCls[cb] = (pc + 12) % 12;
    }
    var chA = new Float64Array(12), chB = new Float64Array(12);
    var chPrev = chA, chNow = chB;
    var C = 60; // log compression
    var nov = new Float32Array(nFrames);
    var rms = new Float32Array(nFrames);
    var lowShare = new Float32Array(nFrames);
    var lowFlux = new Float32Array(nFrames); // raw low-band flux, for beat-phase voting
    var peakRms = 0;

    // first pass RMS peak (for silence gate) — cheap loop
    for (var f = 0; f < nFrames; f++) {
      var s0 = f * HOP, acc = 0;
      for (var j = 0; j < FRAME; j += 4) { var v = data[s0 + j]; acc += v * v; }
      var r = Math.sqrt(acc / (FRAME / 4));
      rms[f] = r;
      if (r > peakRms) peakRms = r;
    }

    for (var fr = 0; fr < nFrames; fr++) {
      var st = fr * HOP;
      for (var k = 0; k < FRAME; k++) { re[k] = data[st + k] * hann[k]; im[k] = 0; }
      magnitudeSpectrum(re, im, mag);
      var fL = 0, fM = 0, fH = 0, eL = 0;
      var b;
      for (b = edges.low[0]; b <= edges.low[1]; b++) {
        var dL = Math.log1p(C * mag[b]) - Math.log1p(C * prev[b]);
        if (dL > 0) fL += dL;
        eL += mag[b] * mag[b];
      }
      for (b = edges.mid[0]; b <= edges.mid[1]; b++) {
        var dM = Math.log1p(C * mag[b]) - Math.log1p(C * prev[b]);
        if (dM > 0) fM += dM;
      }
      for (b = edges.high[0]; b <= edges.high[1]; b++) {
        var dH = Math.log1p(C * mag[b]) - Math.log1p(C * prev[b]);
        if (dH > 0) fH += dH;
      }
      // harmonic-change flux: normalized positive chroma difference.
      // Piano/vocal note changes redistribute harmonic energy across pitch
      // classes even when broadband flux barely moves, so this fires on soft
      // attacks; normalization keeps quiet passages comparable to loud ones.
      // (A longer-baseline variant was tried: comparing against sound from
      // ~500ms ago leaves a 500ms "halo" of elevated novelty after every
      // attack in sparse material, which inflates any local threshold and
      // buries the following legato attacks. Adjacent-frame it is; vibrato
      // trains are handled downstream by the rise gate + chain suppression.)
      var hf = 0, chTot = 0, cc;
      for (cc = 0; cc < 12; cc++) chNow[cc] = 0;
      for (b = edges.low[1]; b <= FRAME / 2 && b * binHz <= 5000; b++) {
        var cls = chromaCls[b];
        if (cls >= 0) chNow[cls] += Math.log1p(C * mag[b]);
      }
      for (cc = 0; cc < 12; cc++) {
        var dc = chNow[cc] - chPrev[cc];
        if (dc > 0) hf += dc;
        chTot += chNow[cc];
        chPrev[cc] = chNow[cc];
      }
      var harm = hf / Math.max(1e-9, chTot);
      for (b = 0; b <= FRAME / 2; b++) prev[b] = mag[b];
      // Soft-AND with level-rise evidence: a spectral change only counts as
      // an onset if the level is also rising out of a recent dip. Attacks
      // (even soft legato ones) rise sharply from their dip and score up to
      // 1.5x; vibrato wobble and decay texture sit near 0.5x. This separates
      // soft attacks from sustain wobble that no pure-flux amplitude
      // threshold can split (measured: both peak ~0.55 on ballads).
      var dipM = rms[fr];
      for (var db = Math.max(0, fr - 8); db < fr; db++) {
        if (rms[db] < dipM) dipM = rms[db];
      }
      var riseG = (rms[Math.min(nFrames - 1, fr + 2)] - dipM) / Math.max(1e-4, peakRms * 0.1);
      if (riseG < 0) riseG = 0; else if (riseG > 1) riseG = 1;
      nov[fr] = (W_LOW * fL + W_MID * fM + W_HIGH * fH + W_HARM * harm) * (0.5 + riseG);
      lowFlux[fr] = fL; // unnormalized low-band flux, for beat-phase voting
      var tot = 0;
      for (b = 1; b <= FRAME / 2; b++) tot += mag[b] * mag[b];
      lowShare[fr] = eL / Math.max(1e-12, tot);
      if (onProgress && (fr & 2047) === 0) onProgress(fr / nFrames);
    }
    // normalize novelty by 95th percentile
    var cp = Array.prototype.slice.call(nov).sort(function (a, b) { return a - b; });
    var p95 = cp[Math.floor(cp.length * 0.95)] || 1;
    for (var q = 0; q < nFrames; q++) nov[q] /= Math.max(1e-9, p95);
    return { novelty: nov, rms: rms, peakRms: peakRms, lowShare: lowShare, lowFlux: lowFlux, nFrames: nFrames, fps: fps };
  }

  function isSilent(rms, peakRms) {
    var floor = Math.max(1e-4, peakRms * 0.02);
    return rms < floor;
  }

  /* ---------- step 3: adaptive peaks ----------
     v3 addition — energy-rise gate: vibrato/tremolo on a sustained note
     produces strong spectral flux (energy sloshing between bins) with
     almost no level change, and those wobble peaks can outscore the soft
     attack that started the note. A genuine onset coincides with an RMS
     rise measured from the recent local MINIMUM (dip-then-rise): legato
     notes that start on an already-loud pedestal still show a dip recovery,
     while pure wobble crests barely rise above their trough. */
  function detectOnsets(nov, rms, peakRms, fps, thresholdFactor) {
    var n = nov.length;
    // ±1.0s local window (was ±0.5s): on sparse material the wider window
    // dilutes sustain wobble with surrounding gap silence, dropping the
    // threshold onto soft attacks; on dense drums the statistics barely
    // change, so percussive detection is unaffected.
    var win = Math.max(8, Math.round(fps * 1.0));
    var back = Math.max(1, Math.round(0.09 * fps));
    var fwd = Math.max(1, Math.round(0.02 * fps));
    var riseTol = 0.02 * Math.max(1e-4, peakRms);
    var raw = [];
    var minGapF = Math.max(2, Math.round(MIN_ONSET_GAP * fps));
    for (var i = 2; i < n - 2; i++) {
      var a = Math.max(0, i - win), b = Math.min(n, i + win);
      var sum = 0, sum2 = 0, cnt = 0;
      for (var j = a; j < b; j += 3) { var v = nov[j]; sum += v; sum2 += v * v; cnt++; }
      var mean = sum / Math.max(1, cnt);
      var variance = Math.max(0, sum2 / Math.max(1, cnt) - mean * mean);
      var thr = Math.max(mean + thresholdFactor * Math.sqrt(variance), 0.18);
      var x = nov[i];
      if (x < thr) continue;
      if (!(x >= nov[i - 1] && x >= nov[i + 1] && x > nov[i - 2] && x >= nov[i + 2])) continue;
      var w0 = Math.max(0, i - back), wEnd = Math.min(n - 1, i + fwd);
      var dip = rms[w0];
      for (var wm = w0 + 1; wm <= i; wm++) if (rms[wm] < dip) dip = rms[wm];
      if (rms[wEnd] - dip < riseTol) continue;
      var pa = nov[i - 1], pb = x, pc = nov[i + 1];
      var den = pa - 2 * pb + pc;
      var off = den !== 0 ? 0.5 * (pa - pc) / den : 0;
      off = Math.max(-0.5, Math.min(0.5, off));
      raw.push({ frame: i, time: (i + off) / fps, str: x });
    }
    // enforce min separation (keep stronger)
    var peaks = [];
    for (var k = 0; k < raw.length; k++) {
      var p = raw[k];
      var last = peaks[peaks.length - 1];
      if (last && p.time - last.time < MIN_ONSET_GAP) {
        if (p.str > last.str) peaks[peaks.length - 1] = p;
      } else peaks.push(p);
    }
    // drop onsets inside silence
    var voiced = peaks.filter(function (p) {
      var fr = Math.max(0, Math.min(n - 1, Math.round(p.time * fps)));
      return !isSilent(rms[fr], peakRms);
    });
    // sustain-wobble chain suppression: vibrato/tremolo fires quasi-periodic
    // peaks on HIGH sustained energy with no fresh attack behind them, while
    // genuine rapid notes (drums, trills, repeated piano) either decay
    // between hits (RMS dips) or arrive with a real level rise. Drop a peak
    // when it closely follows another peak AND the ±0.3s context never drops
    // to 30% of peak RMS (true sustain) AND its own ~110ms rise is under 5%
    // of peak RMS (no fresh attack). lastPt advances even for dropped peaks
    // so a wobble train cannot re-anchor itself.
    var kept2 = [];
    var lastPt = -1e9;
    for (var si = 0; si < voiced.length; si++) {
      var sp = voiced[si];
      var dropWobble = false;
      if (sp.time - lastPt < 0.9) {
        var wa = Math.max(0, Math.round((sp.time - 0.3) * fps));
        var wb = Math.min(n - 1, Math.round((sp.time + 0.3) * fps));
        var wsum = 0, wcnt = 0;
        for (var wi = wa; wi <= wb; wi++) { wsum += rms[wi]; wcnt++; }
        if (wsum / Math.max(1, wcnt) > 0.3 * Math.max(1e-4, peakRms)) {
          var sfr = Math.max(0, Math.min(n - 1, sp.frame));
          var rise = rms[Math.min(n - 1, sfr + 2)] - rms[Math.max(0, sfr - 8)];
          if (rise < 0.05 * Math.max(1e-4, peakRms)) dropWobble = true;
        }
      }
      lastPt = sp.time;
      if (!dropWobble) kept2.push(sp);
    }
    return kept2;
  }

  /* ---------- step 4: tempo (fractional-lag autocorrelation) ---------- */
  function estimateTempo(nov, fps) {
    var n = nov.length;
    var mean = 0;
    for (var i = 0; i < n; i++) mean += nov[i];
    mean /= Math.max(1, n);
    var minLag = Math.max(4, Math.floor((fps * 60) / BPM_MAX));
    var maxLag = Math.min(n - 1, Math.ceil((fps * 60) / BPM_MIN));
    var R = new Float64Array(maxLag + 1);
    var step = Math.max(1, Math.floor(n / 800));
    for (var lag = minLag; lag <= maxLag; lag++) {
      var dot = 0, n1 = 0, n2 = 0;
      for (var i2 = 0; i2 + lag < n; i2 += step) {
        var x = nov[i2] - mean, y = nov[i2 + lag] - mean;
        dot += x * y; n1 += x * x; n2 += y * y;
      }
      R[lag] = dot / Math.max(1e-9, Math.sqrt(n1 * n2));
    }
    var bestLag = minLag, bestScore = -1e9, bestBpm = 120;
    for (var bpm = BPM_MIN; bpm <= BPM_MAX; bpm++) {
      var L = Math.round((fps * 60) / bpm);
      if (L < minLag || L > maxLag) continue;
      var prior = 1;
      if (bpm >= 90 && bpm <= 140) prior = 1.06;
      if (bpm < 75 || bpm > 175) prior = 0.94;
      var s = R[L] * prior;
      if (s > bestScore) { bestScore = s; bestLag = L; bestBpm = bpm; }
    }
    // parabolic interpolation -> fractional lag -> sub-BPM precision
    // (integer lags alone quantize to ±2 BPM at 43fps envelopes)
    var lagF = bestLag;
    if (bestLag > minLag && bestLag < maxLag) {
      var ra = R[bestLag - 1], rb = R[bestLag], rc = R[bestLag + 1];
      var den = ra - 2 * rb + rc;
      if (den !== 0) {
        var delta = 0.5 * (ra - rc) / den;
        if (delta > -1 && delta < 1) lagF = bestLag + delta;
      }
    }
    var bpmF = (fps * 60) / lagF;
    // octave normalization into musical range
    if (bpmF < 70) bpmF *= 2;
    else if (bpmF > 180) bpmF /= 2;
    // confidence: winner prominence above median lag score
    var vals = [];
    for (var q = minLag; q <= maxLag; q++) vals.push(R[q]);
    var med = medianOf(vals);
    var conf = Math.max(0, Math.min(1, (R[bestLag] - med) / 0.25));
    return { bpm: Math.round(bpmF), rawBpm: bestBpm, confidence: conf };
  }

  // Full-envelope autocorrelation at one lag (for the subharmonic guard).
  function envelopeCorr(nov, fps) {
    var n = nov.length, mean = 0;
    for (var i = 0; i < n; i++) mean += nov[i];
    mean /= Math.max(1, n);
    var step = Math.max(1, Math.floor(n / 800));
    return function (lag) {
      if (lag < 1 || lag >= n) return -1;
      var dot = 0, n1 = 0, n2 = 0;
      for (var j = 0; j + lag < n; j += step) {
        var u = nov[j] - mean, v = nov[j + lag] - mean;
        dot += u * v; n1 += u * u; n2 += v * v;
      }
      return dot / Math.max(1e-9, Math.sqrt(n1 * n2));
    };
  }

  /* ---------- step 5: dynamic beat tracking ----------
     v2 estimated one global BPM + offset (anchored to the first 40s) and
     extrapolated it rigidly, so tempo drift, rubato, or a mid-song tempo
     change left the back half of the chart off the music. v3 walks the beat
     grid through the whole track instead:
       - anchor: same strongest-onset phase search on the first 40s,
       - walk: each next beat is predicted from the current local interval
         then pulled to the nearest novelty peak (±6%: evidence, not teleport),
       - re-fit: every 8 beats the local interval is re-estimated by
         autocorrelation in a ±6s window, clamped to ±20% of the running
         value so one noisy bar can't yank the grid (continuity constraint).
     Result: beats[] bends with the performance; intervals[] carries the
     local beat length per beat for quantization. Fully deterministic.
     Phase candidates are seeded from the STRONGEST onsets (kicks/downbeats),
     then refined locally. A blind full-period sweep locks onto hats. */
  function trackBeats(nov, fps, duration, bpm, peaks, lowFlux) {
    var beat = 60 / bpm;
    var horizon = Math.min(duration, 40); // phase search on first 40s
    var n = Math.min(nov.length, Math.floor(horizon * fps));
    function gridScore(off) {
      var s = 0, cnt = 0;
      for (var t = off; t < horizon; t += beat) {
        var fr = Math.round(t * fps);
        var m = 0;
        for (var d = -2; d <= 2; d++) {
          var q = fr + d;
          if (q >= 0 && q < n && nov[q] > m) m = nov[q];
        }
        s += m; cnt++;
      }
      return s / Math.max(1, cnt);
    }
    var cands = [0];
    var top = (peaks || []).slice().sort(function (a, b) { return b.str - a.str; }).slice(0, 12);
    for (var c = 0; c < top.length; c++) {
      var ph = (((top[c].time % beat) + beat) % beat);
      cands.push(ph);
      // The strongest peaks may all be off-beats (bright hats outscoring a
      // narrowband kick); the ±40ms refine below could never walk half a
      // beat to the true downbeat. Always evaluate the opposite phase too
      // and let the low-frequency support decide between them.
      cands.push((ph + beat / 2) % beat);
    }
    // Phase pick: novelty evidence weighted by LOW-BAND FLUX at the grid
    // points. The strongest peaks can be off-beats (bright hats outscore a
    // narrowband kick in summed flux), and a ±40ms refine can never walk
    // half a beat to the true downbeat — so the opposite phase is always
    // evaluated too (see candidate seeding above). Beats are low-frequency
    // EVENTS (kick/bass attacks): low-band flux spikes only at the hit,
    // while low-band ENERGY persists through the decay and cannot tell
    // phases apart. On material with no low-end contrast (piano, vocals)
    // the weight is ~flat and novelty decides. lowFlux is normalized by its
    // own p95 so the weight is comparable across songs.
    var lowNorm = null;
    if (lowFlux) {
      var cp = Array.prototype.slice.call(lowFlux).sort(function (a, b) { return a - b; });
      var p95 = cp[Math.floor(cp.length * 0.95)] || 1;
      lowNorm = new Float32Array(lowFlux.length);
      for (var li = 0; li < lowFlux.length; li++) lowNorm[li] = lowFlux[li] / Math.max(1e-9, p95);
    }
    function lowSupport(off) {
      if (!lowNorm) return 1;
      var s = 0, cnt = 0;
      for (var t = off; t < horizon; t += beat) {
        var fr = Math.round(t * fps);
        var m = 0;
        for (var d = -2; d <= 2; d++) {
          var q = fr + d;
          if (q >= 0 && q < lowNorm.length && lowNorm[q] > m) m = lowNorm[q];
        }
        s += m; cnt++;
      }
      return s / Math.max(1, cnt);
    }
    var bestOff = 0, bestScore = -1;
    for (var k = 0; k < cands.length; k++) {
      for (var dj = -0.04; dj <= 0.0401; dj += 0.008) {
        var off = (cands[k] + dj + beat) % beat;
        var fs = gridScore(off) * (0.5 + lowSupport(off));
        if (fs > bestScore) { bestScore = fs; bestOff = off; }
      }
    }
    // Walk the grid forward and backward from the anchor so local tempo
    // drift bends the grid instead of breaking it. NFR/nov/fps close over.
    var NFR = nov.length;
    // local interval re-fit: autocorrelate the onset envelope around time t,
    // lag constrained near the running interval (continuity), absolute-clamped
    // to the 60-200 BPM musical range, with parabolic refinement.
    function localInterval(t, refBeat) {
      var span = 6;
      var a = Math.max(0, Math.floor((t - span) * fps));
      var b = Math.min(NFR - 1, Math.ceil((t + span) * fps));
      if (b - a < 8) return refBeat;
      var lo = Math.max(Math.round(refBeat * 0.75 * fps), Math.floor(fps * 60 / BPM_MAX));
      var hi = Math.min(Math.round(refBeat * 1.25 * fps), Math.ceil(fps * 60 / BPM_MIN));
      if (hi <= lo) return refBeat;
      var mean = 0, cnt = 0, ii;
      for (ii = a; ii <= b; ii++) { mean += nov[ii]; cnt++; }
      mean /= Math.max(1, cnt);
      var step = Math.max(1, Math.floor((b - a) / 400));
      function corrAt(lag) {
        var dot = 0, n1 = 0, n2 = 0;
        for (var j = a; j + lag <= b; j += step) {
          var u = nov[j] - mean, v = nov[j + lag] - mean;
          dot += u * v; n1 += u * u; n2 += v * v;
        }
        return dot / Math.max(1e-9, Math.sqrt(n1 * n2));
      }
      var bestL = Math.round(refBeat * fps), bestR = -1e9;
      for (var lag = lo; lag <= hi; lag++) {
        var r = corrAt(lag);
        if (r > bestR) { bestR = r; bestL = lag; }
      }
      var lagF = bestL;
      if (bestL > lo && bestL < hi) {
        var r0 = corrAt(bestL - 1), r1 = corrAt(bestL), r2 = corrAt(bestL + 1);
        var den = r0 - 2 * r1 + r2;
        if (den !== 0) {
          var dl = 0.5 * (r0 - r2) / den;
          if (dl > -1 && dl < 1) lagF = bestL + dl;
        }
      }
      var iv = lagF / fps;
      iv = Math.max(refBeat * 0.8, Math.min(refBeat * 1.2, iv));
      iv = Math.max(60 / BPM_MAX, Math.min(60 / BPM_MIN, iv));
      return iv;
    }
    // Beat targets: detected onset peaks mapped onto frames. Snapping
    // prefers these over raw novelty maxima so the grid locks onto real
    // note attacks rather than decay wobble or vibrato bumps between them.
    var peakAt = new Float32Array(NFR);
    for (var pi = 0; pi < (peaks || []).length; pi++) {
      var pf = peaks[pi].frame;
      if (pf >= 0 && pf < NFR && peaks[pi].str > peakAt[pf]) peakAt[pf] = peaks[pi].str;
    }
    // strongest local evidence near a predicted beat time (±6% window).
    // In dead silence there is no evidence: hold the prediction instead of
    // jumping to noise.
    function snapToPeak(t, interval) {
      var w = Math.max(2 / fps, interval * 0.06);
      var bf = Math.round(t * fps), bw = Math.max(1, Math.round(w * fps));
      var bm = -1, bt2 = t;
      for (var d = -bw; d <= bw; d++) {
        var q = bf + d;
        if (q < 0 || q >= NFR) continue;
        var m = 0;
        for (var e = -2; e <= 2; e++) {
          var qq = q + e;
          if (qq >= 0 && qq < NFR && nov[qq] > m) m = nov[qq];
        }
        m += 1.5 * (peakAt[q] || 0);
        if (m > bm) { bm = m; bt2 = q / fps; }
      }
      if (bm <= 1e-9) return t;
      return bt2;
    }
    var fwd = [bestOff], cur = beat, steps = 0;
    while (true) {
      if (steps > 0 && steps % 8 === 0) {
        cur = localInterval(fwd[fwd.length - 1], cur);
      }
      var pred = fwd[fwd.length - 1] + cur;
      if (pred > duration - 0.15) break;
      if (pred < 0.3 - cur) { fwd.push(pred); steps++; continue; }
      fwd.push(snapToPeak(pred, cur));
      steps++;
      if (steps > 10000) break; // pathological guard
    }
    var beats = fwd.slice();
    var back = bestOff, bsteps = 0;
    while (true) {
      if (bsteps > 0 && bsteps % 8 === 0) {
        cur = localInterval(back, cur);
      }
      var pb = back - cur;
      if (pb < 0.3) break;
      back = snapToPeak(pb, cur);
      beats.unshift(back);
      bsteps++;
      if (bsteps > 10000) break;
    }
    // local interval per beat (forward differences; last repeats) so
    // quantization below can snap to the bent grid, not the global average.
    var intervals = [];
    for (var bi = 0; bi < beats.length; bi++) {
      intervals.push(bi + 1 < beats.length ? beats[bi + 1] - beats[bi]
        : (beats.length > 1 ? beats[beats.length - 1] - beats[beats.length - 2] : beat));
    }
    // downbeat: strongest low-frequency beat of each bar of 4
    var downPhase = 0, downBest = -1;
    for (var ph = 0; ph < 4; ph++) {
      var e = 0, c = 0;
      for (var k = ph; k < beats.length; k += 4) {
        var f2 = Math.round(beats[k] * fps);
        if (f2 >= 0 && f2 < nov.length) { e += nov[f2]; c++; }
      }
      e /= Math.max(1, c);
      if (e > downBest) { downBest = e; downPhase = ph; }
    }
    // beatInterval is reported as the median LOCAL interval (the honest
    // summary of a bending grid); beatOffset stays the initial phase anchor.
    var medIv = beat;
    if (intervals.length) {
      var sIv = intervals.slice().sort(function (a, b) { return a - b; });
      medIv = sIv[Math.floor(sIv.length / 2)];
    }
    return { beatInterval: medIv, beatOffset: bestOff, beats: beats, downPhase: downPhase, intervals: intervals };
  }

  /* ---------- step 6: quantize + score (local grid) ----------
     v2 snapped every onset to one rigid global grid; onsets late in a
     drifting song were rejected as noise or yanked far from what was played.
     v3 snaps each onset to its NEAREST bent-grid beat using that beat's own
     local interval, so quantization error stays small everywhere. */
  function nearestBeatIdx(beats, t) {
    var lo = 0, hi = beats.length - 1;
    if (!beats.length) return -1;
    if (t <= beats[0]) return 0;
    if (t >= beats[hi]) return hi;
    while (hi - lo > 1) {
      var mid = (lo + hi) >> 1;
      if (beats[mid] < t) lo = mid; else hi = mid;
    }
    return (t - beats[lo] <= beats[hi] - t) ? lo : hi;
  }
  function quantizeAndScore(peaks, grid, fps, lowShare) {
    var beats = grid.beats || [], intervals = grid.intervals || [];
    // Sparse material (median onset gap > 0.45s: rubato ballads, slow piano)
    // keeps its EXACT detected timing instead of snapping to a grid that may
    // be fictional there. Snapping exists to tighten dense rhythmic playing;
    // yanking an isolated rubato note 100ms+ to a wrong grid is worse than
    // no snap at all. Subdivision labels are still computed for downstream
    // scoring (mostly moot: sparse mode keeps every subdivision).
    var sparseQ = false;
    if (peaks.length > 4) {
      var pg = [];
      for (var pi = 1; pi < peaks.length; pi++) pg.push(peaks[pi].time - peaks[pi - 1].time);
      sparseQ = medianOf(pg) > 0.45;
    }
    var out = [];
    for (var i = 0; i < peaks.length; i++) {
      var p = peaks[i];
      var j = nearestBeatIdx(beats, p.time);
      var sub = (j >= 0 && intervals[j]) ? intervals[j] / 4 : 0.25;
      var ref = j >= 0 ? beats[j] : p.time;
      var g = Math.round((p.time - ref) / sub);
      var qt = ref + g * sub;
      var err = Math.abs(qt - p.time);
      var division = ((g % 4) + 4) % 4; // 0 beat, 2 half, else quarter
      var subdiv = division === 0 ? '1' : division === 2 ? '1/2' : '1/4';
      var quantized = err <= MAX_QUANT_ERR;
      if (!quantized && p.str < 0.8 && !sparseQ) continue; // noise: reject
      var time = (quantized && !sparseQ) ? (qt * 0.55 + p.time * 0.45) : p.time;
      var align = division === 0 ? 0.35 : division === 2 ? 0.2 : 0.08;
      var fr = Math.max(0, Math.min(lowShare.length - 1, p.frame));
      // kick/bass fundamentals live almost entirely below 200 Hz; give them
      // a full bonus so narrowband low-end onsets survive spacing contests
      // against broadband hats (flux sums favor many bright bins).
      var lowBonus = lowShare[fr] > 0.5 ? 0.30 : (lowShare[fr] > 0.35 ? 0.15 : 0);
      // downbeat bonus: absolute beat index = nearest beat + subdiv offset
      var beatIdx = (j >= 0 ? j : 0) + Math.round(g / 4);
      var isDown = ((beatIdx - grid.downPhase) % 4 + 4) % 4 === 0 && division === 0;
      var strength = p.str + align + lowBonus + (isDown ? 0.12 : 0);
      out.push({
        time: time, strength: strength, confidence: Math.min(1, p.str),
        subdivision: subdiv, downbeat: isDown, frame: p.frame
      });
    }
    out.sort(function (a, b) { return a.time - b.time; });
    return out;
  }

  /* ---------- step 7: cluster near-simultaneous onsets ----------
     Onsets within 45ms form ONE musical event (a drum hit + bass transient
     arriving together). The cluster keeps every voice's energy: the timestamp
     comes from the strongest voice, but count/strength feed the chord
     composer below instead of being discarded. */
  function clusterEvents(cands, diffKey) {
    var cfg = DIFF[diffKey] || DIFF.normal;
    // Sparse-mode bypass: subdivision filtering exists to thin DENSE tracks.
    // On sparse material (median onset gap > 0.45s) there is nothing to thin,
    // and bin labels on a weak grid are arbitrary — dropping them would
    // delete real notes. Keep everything; density caps still apply.
    var sparse = false;
    if (cands.length > 4) {
      var gaps = [];
      for (var gi = 1; gi < cands.length; gi++) gaps.push(cands[gi].time - cands[gi - 1].time);
      sparse = medianOf(gaps) > 0.45;
    }
    var pool = sparse ? cands.slice() : cands.filter(function (c) { return cfg.subs[c.subdivision]; });
    pool.sort(function (a, b) { return a.time - b.time; });
    var clusters = [];
    for (var i = 0; i < pool.length; i++) {
      var c = pool[i];
      var last = clusters[clusters.length - 1];
      if (last && c.time - last.spanEnd < 0.045) {
        last.members.push(c);
        last.spanEnd = c.time;
        last.count++;
        last.sum += c.strength;
        if (c.strength > last.str) {
          last.str = c.strength; last.time = c.time;
          last.subdivision = c.subdivision; last.downbeat = c.downbeat;
          last.confidence = c.confidence; last.frame = c.frame;
        }
      } else {
        clusters.push({
          time: c.time, spanEnd: c.time, str: c.strength, sum: c.strength,
          count: 1, members: [c], subdivision: c.subdivision,
          downbeat: c.downbeat, confidence: c.confidence, frame: c.frame
        });
      }
    }
    return clusters;
  }

  /* ---------- step 8: polyphonic composer ----------
     Turns each musical event into one or two lanes. Chord probability is
     driven by energy; pairs remain cross-hand and never exceed two tiles. */
  // Hands: D,F (lanes 0,1) = left hand · J,K (lanes 2,3) = right hand.
  // HARD RULE: no simultaneous pair may sit on one hand — D+F and J+K
  // pairs are unplayable. Cross-hand pairs only (D+J, F+K, F+J, K+D).
  var PAIRS = [[0, 2], [1, 3], [1, 2], [0, 3]];
  function sameHand(a, b) { return (a < 2) === (b < 2); }

  function walkLane(rng, mem, gapPrev) {
    var prev = mem.lane, cand;
    if (prev < 0) {
      cand = Math.floor(rng() * 4);
    } else if (gapPrev > 0.6) {
      cand = Math.floor(rng() * 4); // breathing room: free choice
    } else {
      var r = rng();
      if (r < 0.62) {
        cand = prev + mem.dir; // continue the run (0-1-2-3 / 3-2-1-0)
        if (cand > 3 || cand < 0) { mem.dir = -mem.dir; cand = prev + mem.dir; }
      } else if (r < 0.85) {
        cand = Math.max(0, Math.min(3, prev + (rng() < 0.5 ? -1 : 1))); // neighbor
      } else {
        cand = Math.floor(rng() * 4); // occasional leap
      }
      if (cand === prev && mem.run >= 1 && rng() < 0.9) cand = (cand + 1 + Math.floor(rng() * 2)) % 4;
      if (cand === prev && mem.prev2 === prev) cand = (cand + 2) % 4; // never 3 in a row
      var h = mem.hist;
      if (h.length >= 3 && cand === h[h.length - 2] && prev === h[h.length - 3] && rng() < 0.7) {
        cand = (cand + 1) % 4; // break ABAB loops
      }
    }
    if (cand !== prev && prev >= 0) mem.dir = cand > prev ? 1 : -1;
    mem.run = cand === prev ? mem.run + 1 : 0;
    mem.prev2 = prev;
    mem.hist.push(cand);
    if (mem.hist.length > 6) mem.hist.shift();
    return cand;
  }

  function pairKey(p) { return p[0] + '+' + p[1]; }

  function composeEvents(analysis, diffKey, seed, allowHolds) {
    var cfg = DIFF[diffKey] || DIFF.normal;
    var duration = analysis.duration;
    var rng = mulberry32(seed);
    // chronological spacing pass: conflicting close events keep the stronger
    var clusters = clusterEvents(analysis.candidates, diffKey);
    // NOTE (v3): a previous revision inserted a synthetic near-zero-strength
    // tile at every beat-grid position lacking a nearby onset cluster. That
    // made tiles appear during melodic/vocal passages with no corresponding
    // sound — the chart followed the metronome, not the music. Removed:
    // every cluster below now traces to a real detected onset, so sparse
    // music correctly yields a sparse chart. Playability on quiet songs is
    // preserved by the spacing pass (strong events are never dropped for
    // weak ones) and by sustain-gated holds, not by invented notes.
    var kept = [];
    // Beat-preference weights: when two events collide inside minGap, the
    // on-beat one survives even if it is spectrally weaker (a narrowband
    // kick routinely loses raw-strength contests to broadband hats). The
    // pulse is the chart's skeleton; off-beat grace notes are expendable.
    function conflictScore(cl) {
      return cl.str + (cl.downbeat ? 0.2 : 0) +
        (cl.subdivision === '1' ? 0.3 : (cl.subdivision === '1/2' ? 0.1 : 0));
    }
    for (var i = 0; i < clusters.length; i++) {
      var cl = clusters[i];
      if (cl.time < 0.3 || cl.time > duration - 0.2) continue;
      var last = kept[kept.length - 1];
      if (last && cl.time - last.time < cfg.minGap - 1e-6) {
        if (conflictScore(cl) > conflictScore(last)) kept[kept.length - 1] = cl;
      } else kept.push(cl);
    }
    // rank-normalized power: an event's strength relative to THIS song
    // (a lone max-normalization buries everything below the loudest crash).
    // sig = musically above-average onset — chords need real significance.
    var byStr = kept.slice().sort(function (a, b) { return a.str - b.str; });
    for (var mr = 0; mr < byStr.length; mr++) {
      byStr[mr]._rank = byStr.length > 1 ? mr / (byStr.length - 1) : 0.5;
    }
    var medStr = byStr.length ? byStr[Math.floor(byStr.length / 2)].str : 0.0001;
    var maxTiles = Math.max(4, Math.ceil(cfg.maxRate * 1.6)); // soft tile-level cap

    var mem = { lane: -1, prev2: -1, dir: 1, run: 0, hist: [], lastPair: null, lastTriple: null, prevCount: 1 };
    var out = []; // {time, lanes[], holdLane, holdDur, subdivision, downbeat, confidence, str}
    var emitted = []; // tile times for the soft rate cap

    for (var k = 0; k < kept.length; k++) {
      var ev = kept[k];
      var gapPrev = k > 0 ? ev.time - kept[k - 1].time : 9;
      // local density: events/sec in a ±1.25s window
      var cnt = 0;
      for (var w = 0; w < kept.length; w++) {
        if (Math.abs(kept[w].time - ev.time) <= 1.25) cnt++;
      }
      var density = Math.min(1, (cnt / 2.5) / cfg.maxRate);
      var sig = ev.str > medStr * 1.05;
      var power = 0.7 * ev._rank + 0.2 * Math.min(1, (ev.count - 1) / 2) +
        (ev.downbeat ? 0.15 : 0);

      // A musical moment gets either one note or one cross-hand pair.
      var doubleP = (sig && power > cfg.pThr)
        ? cfg.dbl + cfg.dblDense * density + (ev.downbeat ? 0.18 : 0)
        : 0;
      if (mem.prevCount >= 2) doubleP *= 0.45; // break chord runs: chord-single-chord
      var n = rng() < Math.min(0.55, doubleP) ? 2 : 1;

      // soft tile rate cap: shrink chords, never erase rhythm
      var recent = 0;
      for (var e2 = emitted.length - 1; e2 >= 0; e2--) {
        if (ev.time - emitted[e2] < 1.0) recent++;
        else break;
      }
      if (recent + n > maxTiles) n = Math.max(1, maxTiles - recent);

      var melody = walkLane(rng, mem, gapPrev);
      var lanes;
      if (n === 1) {
        lanes = [melody];
      } else if (n === 2) {
        var opts = PAIRS.filter(function (p) { return p[0] === melody || p[1] === melody; });
        opts = opts.filter(function (p) { return pairKey(p) !== mem.lastPair; });
        if (!opts.length) opts = PAIRS.filter(function (p) { return pairKey(p) !== mem.lastPair; });
        var pick = opts[Math.floor(rng() * opts.length)];
        lanes = [melody].concat(pick.filter(function (l) { return l !== melody; }));
        if (lanes.length < 2) lanes = pick.slice();
        mem.lastPair = pairKey(lanes.slice(0, 2).sort());
      }
      if (n === 1) mem.lastPair = null;
      mem.lane = melody;
      mem.prevCount = n;

      // holds: sustained voices become long tiles (primary lane; rarely a
      // second simultaneous hold on very strong, wide-open moments)
      var holdLane = -1, holdDur = 0, holdLane2 = -1, holdDur2 = 0;
      if (allowHolds && diffKey !== 'easy' && ev.subdivision === '1' && ev.confidence > 0.3) {
        var nextT = k + 1 < kept.length ? kept[k + 1].time : 1e9;
        var gap = nextT - ev.time;
        if (gap > 0.45) {
          var f0 = ev.frame, rms = analysis.rms, fps = analysis.fps;
          var look = Math.min(rms.length - 1, f0 + Math.round(0.55 * fps));
          var acc = 0, cc = 0;
          for (var f = f0 + 2; f <= look; f += 2) { acc += rms[f]; cc++; }
          var tail = acc / Math.max(1, cc);
          var head = Math.max(1e-7, rms[Math.min(rms.length - 1, f0)]);
          var ratio = tail / head;
          if (ratio > 0.42) {
            holdLane = lanes[0]; holdDur = Math.min(1.2, gap - 0.1);
            if (lanes.length > 1 && gap > 0.9 && ratio > 0.6 &&
                (diffKey === 'hard' || diffKey === 'insane') && rng() < 0.4) {
              holdLane2 = lanes[1]; holdDur2 = Math.min(1.0, gap - 0.15);
            }
          }
        }
      }

      out.push({
        time: ev.time, lanes: lanes, holdLane: holdLane, holdDur: holdDur,
        holdLane2: holdLane2, holdDur2: holdDur2, subdivision: ev.subdivision,
        downbeat: ev.downbeat, confidence: ev.confidence, str: ev.str
      });
      for (var q = 0; q < lanes.length; q++) emitted.push(ev.time);
    }
    return out;
  }

  /* ---------- step 9: validate + repair (polyphony-aware) ----------
     Same timestamp in DIFFERENT lanes is legal gameplay (chords).
   Only same-lane duplicates and >2 simultaneous stacks are repaired. */
  function simultaneousRun(tiles, i) {
    var run = [i];
    for (var j = i + 1; j < tiles.length; j++) {
      if (Math.abs(tiles[j].time - tiles[i].time) < 0.02) run.push(j);
      else break;
    }
    return run;
  }
  function validateChart(tiles, duration) {
    var warnings = [], errors = [];
    var fixed = tiles.slice().sort(function (a, b) { return a.time - b.time; });
    // repair: clamp lanes, drop out-of-range times
    fixed = fixed.filter(function (t, idx) {
      if (!(t.time >= 0) || !(t.time <= duration)) { errors.push('drop out-of-range tile #' + idx); return false; }
      if (t.lane < 0 || t.lane > 3 || (t.lane | 0) !== t.lane) {
        errors.push('repair invalid lane #' + idx);
        t.lane = Math.max(0, Math.min(3, t.lane | 0));
      }
      return true;
    });
    // A rapid repeat on the same lane reads as overlapping "FF" tiles and is
    // not playable at this game's visual tile length. Keep the stronger one.
    for (var sg = fixed.length - 1; sg > 0; sg--) {
      if (fixed[sg].lane === fixed[sg - 1].lane && fixed[sg].time - fixed[sg - 1].time < 0.18) {
        var dropSame = (fixed[sg].str || 0) > (fixed[sg - 1].str || 0) ? sg - 1 : sg;
        errors.push('repair close same-lane repeat @' + fixed[dropSame].time.toFixed(3));
        fixed.splice(dropSame, 1);
      }
    }
    // repair: same timestamp in the SAME lane is a duplicate (drop weaker).
    // Same timestamp in DIFFERENT lanes is a chord — always legal.
    // More than two simultaneous lanes is never allowed — drop the weakest.
    var i = 1;
    while (i < fixed.length) {
      var stack = simultaneousRun(fixed, i - 1);
      if (stack.length > 1) {
        var seen = {};
        var drop = [];
        for (var r = 0; r < stack.length; r++) {
          var L = fixed[stack[r]].lane;
          if (seen[L] !== undefined) {
            errors.push('repair duplicate ts lane @' + fixed[stack[r]].time.toFixed(3));
            drop.push(stack[r]);
          } else seen[L] = stack[r];
        }
        var live = stack.filter(function (idx) { return drop.indexOf(idx) < 0; });
        if (live.length > 2) {
          live.sort(function (a, b) { return (fixed[b].str || 0) - (fixed[a].str || 0); });
          var cut = live.slice(2);
          errors.push('repair ' + live.length + '-stack @' + fixed[live[0]].time.toFixed(3));
          drop = drop.concat(cut);
        }
        // same-hand 2-stack: keep the timing, move the weaker tile's lane
        // to the free opposite hand (lane is presentation, timing is music)
        if (live.length === 2 && sameHand(fixed[live[0]].lane, fixed[live[1]].lane)) {
          var weak = (fixed[live[0]].str || 0) >= (fixed[live[1]].str || 0) ? live[1] : live[0];
          var strongLane = fixed[live[0] === weak ? live[1] : live[0]].lane;
          fixed[weak].lane = strongLane < 2 ? 2 : 1; // free lane on the other hand
          errors.push('repair same-hand pair @' + fixed[weak].time.toFixed(3));
        }
        if (drop.length) {
          drop.sort(function (a, b) { return b - a; });
          for (var d = 0; d < drop.length; d++) fixed.splice(drop[d], 1);
          i = Math.max(1, stack[0]); // re-scan the repaired stack (indices shifted)
          continue;
        }
        i = stack[stack.length - 1] + 1; // legal chord — hop past it
        continue;
      }
      i++;
    }
    // checks
    var run = 1;
    for (var k = 1; k < fixed.length; k++) {
      if (fixed[k].time < fixed[k - 1].time) errors.push('unsorted chart');
      if (fixed[k].lane === fixed[k - 1].lane) {
        run++;
        if (run >= 4) warnings.push('lane ' + fixed[k].lane + ' repeats 4x near ' + fixed[k].time.toFixed(2) + 's');
      } else run = 1;
    }
    // density: any 2s window above 12 tiles/sec equivalent
    for (var w = 0; w < fixed.length; w++) {
      var cnt = 0;
      for (var m = w; m < fixed.length && fixed[m].time - fixed[w].time < 2; m++) cnt++;
      if (cnt > 20) { warnings.push('dense burst near ' + fixed[w].time.toFixed(1) + 's'); break; }
    }
    if (fixed.length === 0) errors.push('empty chart');
    return { valid: errors.length === 0, warnings: warnings, errors: errors, tiles: fixed };
  }

  /* ---------- orchestrators ---------- */
  function diffCode(d) { return { easy: 11, normal: 22, hard: 33, insane: 44 }[d] || 22; }

  // Heavy one-time analysis. Returns compact, cacheable result.
  function analyzeSong(samples, sampleRate, duration, onProgress) {
    var prog = onProgress || function () {};
    return new Promise(function (resolve) {
      function run() {
        var seed = hashSamples(samples, sampleRate);
        var pre = preprocess(samples);
        var fr = frameAnalysis(pre.data, sampleRate, function (f) { prog(0.05 + f * 0.5); });
        prog(0.6);
        // tempo first (needs full envelope), then detection threshold is fixed 1.25 here;
        // difficulty only selects from candidates later.
        var tempo = estimateTempo(fr.novelty, fr.fps);
        prog(0.7);
        var peaks = detectOnsets(fr.novelty, fr.rms, fr.peakRms, fr.fps, 1.1);
        // Subharmonic guard: a fast-yet-sparse reading is usually a
        // vibrato/tremolo rate sitting an octave above the true pulse (e.g.
        // 166 BPM on a ballad). Fold down when the half-tempo lag correlates
        // nearly as well. Dense fast tracks are exempt (real 150+ BPM music
        // is never onset-sparse), so genuine uptempo is never folded.
        if (tempo.bpm > 140 && peaks.length / Math.max(1, duration) < 4) {
          var corr = envelopeCorr(fr.novelty, fr.fps);
          var lFast = Math.round(fr.fps * 60 / tempo.bpm);
          var lSlow = Math.round(fr.fps * 60 / (tempo.bpm / 2));
          if (corr(lSlow) >= 0.8 * corr(lFast)) {
            tempo = { bpm: Math.round(tempo.bpm / 2), rawBpm: tempo.rawBpm, confidence: tempo.confidence * 0.9 };
          }
        }
        prog(0.78);
        var grid = trackBeats(fr.novelty, fr.fps, duration, tempo.bpm, peaks, fr.lowFlux);
        prog(0.86);
        var cands = quantizeAndScore(peaks, grid, fr.fps, fr.lowShare);
        prog(0.94);
        resolve({
          version: ANALYSIS_VERSION,
          seed: seed,
          bpm: tempo.bpm,
          rawBpm: tempo.rawBpm,
          confidence: tempo.confidence,
          beatInterval: grid.beatInterval,
          beatOffset: grid.beatOffset,
          downPhase: grid.downPhase,
          beats: grid.beats,
          candidates: cands,
          rawOnsets: peaks.length,
          rms: fr.rms,
          fps: fr.fps,
          duration: duration,
          sampleRate: sampleRate
        });
      }
      setTimeout(run, 30); // let UI paint ANALYZING state
    });
  }

  // Fast sync chart build from cached analysis (difficulty = selection, not re-detection).
  // Each musical event becomes 1-3 lane(s) by energy; timing is untouched.
  function buildChart(analysis, opts) {
    opts = opts || {};
    var diff = opts.difficulty || 'normal';
    var seed = (analysis.seed ^ (diffCode(diff) * 2654435761)) >>> 0;
    var events = composeEvents(analysis, diff, seed, opts.allowHolds !== false);
    var offS = (opts.offsetMs || 0) / 1000;
    var tiles = [];
    var singles = 0, doubles = 0, triples = 0;
    for (var i = 0; i < events.length; i++) {
      var ev = events[i];
      var t = ev.time + offS;
      if (t < 0.3 || t > analysis.duration - 0.15) continue;
      var bright = ev.confidence > 0.55;
      if (ev.lanes.length === 1) singles++;
      else if (ev.lanes.length === 2) doubles++;
      else triples++;
      for (var q = 0; q < ev.lanes.length; q++) {
        var lane = ev.lanes[q];
        var midi = [60, 64, 67, 72][lane] + (bright ? 12 : 0);
        var isHold = lane === ev.holdLane || lane === ev.holdLane2;
        var dur = lane === ev.holdLane ? ev.holdDur : ev.holdDur2;
        if (isHold) tiles.push({ time: t, lane: lane, type: 'hold', duration: dur, midi: midi, str: ev.str });
        else tiles.push({ time: t, lane: lane, type: 'tap', midi: midi, str: ev.str });
      }
    }
    var v = validateChart(tiles, analysis.duration);
    if (typeof console !== 'undefined' && console.info) {
      console.info('[chart] ' + analysis.bpm + ' BPM · ' + tiles.length +
        ' tiles (' + singles + ' single / ' + doubles + ' double / ' + triples + ' triple)');
    }
    // strip internal score before handing to engine
    var clean = v.tiles.map(function (t) {
      return t.type === 'hold'
        ? { time: t.time, lane: t.lane, type: 'hold', duration: t.duration, midi: t.midi }
        : { time: t.time, lane: t.lane, type: 'tap', midi: t.midi };
    });
    return {
      tiles: clean,
      bpm: analysis.bpm,
      confidence: analysis.confidence,
      beatInterval: analysis.beatInterval,
      beatOffset: analysis.beatOffset,
      meta: {
        bpm: analysis.bpm, beatOffset: analysis.beatOffset,
        confidence: analysis.confidence, analysisVersion: ANALYSIS_VERSION
      },
      stats: {
        rawOnsets: analysis.rawOnsets,
        acceptedEvents: events.length,
        finalTiles: clean.length,
        singles: singles, doubles: doubles, triples: triples,
        duration: analysis.duration
      },
      validation: { valid: v.valid, warnings: v.warnings, errors: v.errors }
    };
  }

  return {
    ANALYSIS_VERSION: ANALYSIS_VERSION,
    DIFF: DIFF,
    analyzeSong: analyzeSong,
    buildChart: buildChart,
    validateChart: validateChart,
    _internals: {
      preprocess: preprocess, frameAnalysis: frameAnalysis, detectOnsets: detectOnsets,
      estimateTempo: estimateTempo, trackBeats: trackBeats, quantizeAndScore: quantizeAndScore,
      clusterEvents: clusterEvents, composeEvents: composeEvents,
      mulberry32: mulberry32, hashSamples: hashSamples
    }
  };
});
