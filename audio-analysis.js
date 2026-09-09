/* Nocturne rhythm analysis v2 — UMD (browser + node).
 *
 * Pipeline:
 *   PCM mono -> DC removal / light normalization / pre-emphasis
 *   -> Hann-windowed STFT (FRAME 2048, HOP 512) -> RMS + silence gate
 *   -> per-band log spectral flux (LOW 20-200 / MID 200-2000 / HIGH 2000-10000 Hz)
 *   -> combined onset envelope -> adaptive threshold (local mean + k*std)
 *   -> peak picking (parabolic interpolation, min 80ms separation)
 *   -> tempo via envelope autocorrelation (60-200 BPM, octave-normalized)
 *   -> beat phase search -> beat grid + downbeat detection
 *   -> quantization to 1/4-beat grid (max ~100ms snap)
 *   -> strength scoring -> difficulty selection (same analysis)
 *   -> constrained lane assignment (seeded, deterministic)
 *   -> chart validation + repair
 *
 * Tile TIMING always derives from the audio. Seeded PRNG is used only for
 * lane presentation (and never for timing).
 */
(function (root, factory) {
  if (typeof module !== 'undefined' && module.exports) module.exports = factory();
  else root.NocturneAnalysis = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  var ANALYSIS_VERSION = 2;
  var FRAME = 2048;
  var HOP = 512;
  var MIN_ONSET_GAP = 0.08;      // 80ms minimum onset separation
  var MAX_QUANT_ERR = 0.10;      // 100ms max snap distance
  var BPM_MIN = 60, BPM_MAX = 200;

  // dbl/dblDense/tpl/tplDense: energy-driven chord probabilities.
  // pThr: event power needed before doubles are considered at all.
  // Triples additionally require a downbeat + very high power. Never 4 lanes.
  var DIFF = {
    easy:   { maxRate: 1.75, minGap: 0.35, subs: { '1': 1 },                    dbl: 0.08, dblDense: 0.08, tpl: 0,    tplDense: 0,    pThr: 0.62 },
    normal: { maxRate: 2.75, minGap: 0.22, subs: { '1': 1, '1/2': 1 },           dbl: 0.18, dblDense: 0.36, tpl: 0.14, tplDense: 0.25, pThr: 0.50 },
    hard:   { maxRate: 3.75, minGap: 0.15, subs: { '1': 1, '1/2': 1, '1/4': 1 }, dbl: 0.18, dblDense: 0.36, tpl: 0.15, tplDense: 0.30, pThr: 0.42 },
    insane: { maxRate: 5.0,  minGap: 0.10, subs: { '1': 1, '1/2': 1, '1/4': 1 }, dbl: 0.22, dblDense: 0.38, tpl: 0.18, tplDense: 0.32, pThr: 0.35 }
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

  function frameAnalysis(data, sr, onProgress) {
    var edges = bandEdges(sr);
    var hann = new Float32Array(FRAME);
    for (var i = 0; i < FRAME; i++) hann[i] = 0.5 * (1 - Math.cos((2 * Math.PI * i) / FRAME));
    var nFrames = Math.max(1, Math.floor((data.length - FRAME) / HOP));
    var fps = sr / HOP;
    var re = new Float64Array(FRAME), im = new Float64Array(FRAME), mag = new Float64Array(FRAME / 2 + 1);
    var prev = new Float64Array(FRAME / 2 + 1);
    var C = 60; // log compression
    var nov = new Float32Array(nFrames);
    var rms = new Float32Array(nFrames);
    var lowShare = new Float32Array(nFrames);
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
      for (b = 0; b <= FRAME / 2; b++) prev[b] = mag[b];
      nov[fr] = 0.40 * fL + 0.30 * fM + 0.60 * fH;
      var tot = 0;
      for (b = 1; b <= FRAME / 2; b++) tot += mag[b] * mag[b];
      lowShare[fr] = eL / Math.max(1e-12, tot);
      if (onProgress && (fr & 2047) === 0) onProgress(fr / nFrames);
    }
    // normalize novelty by 95th percentile
    var cp = Array.prototype.slice.call(nov).sort(function (a, b) { return a - b; });
    var p95 = cp[Math.floor(cp.length * 0.95)] || 1;
    for (var q = 0; q < nFrames; q++) nov[q] /= Math.max(1e-9, p95);
    return { novelty: nov, rms: rms, peakRms: peakRms, lowShare: lowShare, nFrames: nFrames, fps: fps };
  }

  function isSilent(rms, peakRms) {
    var floor = Math.max(1e-4, peakRms * 0.02);
    return rms < floor;
  }

  /* ---------- step 3: adaptive peaks ---------- */
  function detectOnsets(nov, rms, peakRms, fps, thresholdFactor) {
    var n = nov.length;
    var win = Math.max(8, Math.round(fps * 0.5)); // ±0.5s local window
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
    return peaks.filter(function (p) {
      var fr = Math.max(0, Math.min(n - 1, Math.round(p.time * fps)));
      return !isSilent(rms[fr], peakRms);
    });
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

  /* ---------- step 5: beat phase + grid ----------
     Phase candidates are seeded from the STRONGEST onsets (kicks/downbeats),
     then refined locally. A blind full-period sweep locks onto hats. */
  function trackBeats(nov, fps, duration, bpm, peaks) {
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
      cands.push((((top[c].time % beat) + beat) % beat));
    }
    var bestOff = 0, bestScore = -1;
    for (var k = 0; k < cands.length; k++) {
      for (var dj = -0.04; dj <= 0.0401; dj += 0.008) {
        var off = (cands[k] + dj + beat) % beat;
        var s = gridScore(off);
        if (s > bestScore) { bestScore = s; bestOff = off; }
      }
    }
    // beats across full song
    var beats = [];
    // extend grid backwards so downbeat search is stable
    var startIdx = Math.ceil((0.3 - bestOff) / beat);
    for (var i = startIdx; ; i++) {
      var bt = bestOff + i * beat;
      if (bt > duration - 0.15) break;
      beats.push(bt);
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
    return { beatInterval: beat, beatOffset: bestOff, beats: beats, downPhase: downPhase };
  }

  /* ---------- step 6: quantize + score ---------- */
  function quantizeAndScore(peaks, grid, fps, lowShare) {
    var beat = grid.beatInterval, off = grid.beatOffset;
    var sub = beat / 4;
    var out = [];
    for (var i = 0; i < peaks.length; i++) {
      var p = peaks[i];
      var g = Math.round((p.time - off) / sub);
      var qt = off + g * sub;
      var err = Math.abs(qt - p.time);
      var division = ((g % 4) + 4) % 4; // 0 beat, 2 half, else quarter
      var subdiv = division === 0 ? '1' : division === 2 ? '1/2' : '1/4';
      var quantized = err <= MAX_QUANT_ERR;
      if (!quantized && p.str < 0.8) continue; // noise: reject
      var time = quantized ? (qt * 0.55 + p.time * 0.45) : p.time;
      var align = division === 0 ? 0.35 : division === 2 ? 0.2 : 0.08;
      var fr = Math.max(0, Math.min(lowShare.length - 1, p.frame));
      var lowBonus = lowShare[fr] > 0.35 ? 0.15 : 0;
      // downbeat bonus
      var beatIdx = Math.round((time - off) / beat);
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
    var pool = cands.filter(function (c) { return cfg.subs[c.subdivision]; });
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
     Turns each musical event into 1-3 lanes. Chord probability is driven by
     the event's own energy (strength + simultaneous voices + local density),
     never by blind duplication: quiet sections stay sparse, dense sections
     bloom into doubles and occasional triples. Lane shapes carry pattern
     memory (runs, alternation, hand changes) so sequences feel intentional. */
  // Hands: D,F (lanes 0,1) = left hand · J,K (lanes 2,3) = right hand.
  // HARD RULE: no simultaneous pair may sit on one hand — D+F and J+K
  // pairs are unplayable. Cross-hand pairs only (D+J, F+K, F+J, K+D).
  // Triples always span both hands, so any 3-lane shape is legal.
  var PAIRS = [[0, 2], [1, 3], [1, 2], [0, 3]];
  var TRIPLES = [[0, 1, 2], [1, 2, 3], [0, 1, 3], [0, 2, 3]]; // never all 4
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
    var kept = [];
    for (var i = 0; i < clusters.length; i++) {
      var cl = clusters[i];
      if (cl.time < 0.3 || cl.time > duration - 0.2) continue;
      var last = kept[kept.length - 1];
      if (last && cl.time - last.time < cfg.minGap - 1e-6) {
        var sNew = cl.str + (cl.downbeat ? 0.2 : 0);
        var sOld = last.str + (last.downbeat ? 0.2 : 0);
        if (sNew > sOld) kept[kept.length - 1] = cl;
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

      // how many lanes does this musical moment deserve?
      // triples live on strong downbeats (bar starts) and the hottest dense
      // peaks — never twice in a row, never 4 lanes.
      var tripleP = (sig && power > 0.62 && (ev.downbeat || density > 0.6))
        ? cfg.tpl + cfg.tplDense * density : 0;
      if (mem.prevCount === 3) tripleP = 0; // never two triples in a row
      var doubleP = (sig && power > cfg.pThr)
        ? cfg.dbl + cfg.dblDense * density + (ev.downbeat ? 0.18 : 0)
        : 0;
      if (mem.prevCount >= 2) doubleP *= 0.45; // break chord runs: chord-single-chord
      var roll = rng();
      var n = roll < tripleP ? 3 : (roll < tripleP + doubleP ? 2 : 1);

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
      } else {
        var tops = TRIPLES.filter(function (t) { return t.indexOf(melody) >= 0; });
        var key = tops.length ? tops.map(function (t) { return t.join('+'); }) : [];
        key = key.filter(function (kk) { return kk !== mem.lastTriple; });
        if (!key.length) key = TRIPLES.map(function (t) { return t.join('+'); });
        var shape = key[Math.floor(rng() * key.length)].split('+').map(Number);
        lanes = [melody].concat(shape.filter(function (l) { return l !== melody; }));
        mem.lastTriple = shape.join('+');
        mem.lastPair = null;
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
     Only same-lane duplicates and >3 simultaneous stacks are repaired. */
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
    // repair: same timestamp in the SAME lane is a duplicate (drop weaker).
    // Same timestamp in DIFFERENT lanes is a chord — always legal.
    // More than 3 simultaneous lanes is impossible — drop the weakest.
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
        if (live.length > 3) {
          live.sort(function (a, b) { return (fixed[b].str || 0) - (fixed[a].str || 0); });
          var cut = live.slice(3);
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
        prog(0.78);
        var grid = trackBeats(fr.novelty, fr.fps, duration, tempo.bpm, peaks);
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
