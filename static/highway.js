/**
 * Canvas-based Rocksmith highway renderer.
 * Receives note data via WebSocket, renders on requestAnimationFrame.
 */
function createHighway() {
    let canvas, ctx, ws;
    let currentTime = 0;
    let animFrame = null;

    // Song data (populated via WebSocket)
    let songInfo = {};
    let notes = [];
    let chords = [];
    let beats = [];
    let sections = [];
    let anchors = [];
    let chordTemplates = [];
    /** Timeline for “direct predecessor” chord repeat detection (rebuilt on ready). */
    let _eventTimesSorted = [];
    let _slotByTime = new Map();
    let lyrics = [];
    let toneChanges = [];
    let toneBase = "";
    let ready = false;
    let showLyrics = true;
    let _drawHooks = [];  // plugin draw callbacks: fn(ctx, W, H)
    let _renderScale = parseFloat(localStorage.getItem('renderScale') || '1');  // 1 = full, 0.5 = half res
    let _inverted = localStorage.getItem('invertHighway') === 'true';
    function si(s) { return _inverted ? 5 - s : s; }  // string index mapper for inversion
    let _lefty = localStorage.getItem('lefty') === '1';

    // Rendering config
    const VISIBLE_SECONDS = 3.0;
    const Z_CAM = 2.2;
    const Z_MAX = 10.0;
    const BG = '#080810';

    const STRING_COLORS = [
        '#cc0000', '#cca800', '#0066cc',
        '#cc6600', '#00cc66', '#9900cc',
    ];
    const STRING_DIM = [
        '#520000', '#524200', '#002952',
        '#522900', '#005229', '#3d0052',
    ];
    const STRING_BRIGHT = [
        '#ff3c3c', '#ffe040', '#3c9cff',
        '#ff9c3c', '#3cff9c', '#cc3cff',
    ];

    // ── Projection ───────────────────────────────────────────────────────
    function project(tOffset) {
        if (tOffset > VISIBLE_SECONDS || tOffset < -0.05) return null;
        if (tOffset < 0) return { y: 0.82 + Math.abs(tOffset) * 0.3, scale: 1.0 };

        const z = tOffset * (Z_MAX / VISIBLE_SECONDS);
        const denom = z + Z_CAM;
        if (denom < 0.01) return null;
        const scale = Z_CAM / denom;
        const y = 0.82 + (0.08 - 0.82) * (1.0 - scale);
        return { y, scale };
    }

    // ── Anchor / Fret mapping ────────────────────────────────────────────
    // Zoom approach: fret 0 at the left edge, fret N at the right (entire canvas mirrored when lefty).
    // The "zoom level" determines how many frets are visible.
    // When playing low frets, zoom in (fewer frets visible, bigger notes).
    // When playing high frets, zoom out (more frets visible, smaller spacing).
    let displayMaxFret = 12;  // rightmost visible fret (smoothed)

    function getAnchorAt(t) {
        let a = anchors[0] || { fret: 1, width: 4 };
        for (const anc of anchors) {
            if (anc.time > t) break;
            a = anc;
        }
        return a;
    }

    function getMaxFretInWindow(t) {
        // Find the highest fret needed across all anchors visible on screen
        let maxFret = 0;
        for (const anc of anchors) {
            if (anc.time > t + VISIBLE_SECONDS) break;
            if (anc.time + 2 < t) continue;  // skip anchors well in the past
            const top = anc.fret + anc.width;
            if (top > maxFret) maxFret = top;
        }
        return maxFret;
    }

    function updateSmoothAnchor(anchor, dt) {
        const rate = Math.min(1.0 * dt, 1.0);
        // Look ahead: use the widest fret range across all visible anchors
        const lookAheadMax = getMaxFretInWindow(currentTime);
        const currentMax = anchor.fret + anchor.width;
        const needed = Math.max(currentMax, lookAheadMax);
        const targetMax = Math.max(needed + 3, 8);
        displayMaxFret += (targetMax - displayMaxFret) * rate;
    }

    function fretX(fret, scale, w) {
        const hw = w * 0.52 * scale;
        const margin = hw * 0.06;
        const usable = hw * 2 - 2 * margin;
        const t = fret / Math.max(1, displayMaxFret);
        return w / 2 - hw + margin + t * usable;
    }

    /** Open-chord line starts at minF (lowest fretted note); extends right so high - low >= minSpan. */
    function expandFretSpan(minF, maxF, minSpan) {
        const low = minF;
        const high = Math.max(maxF, minF + minSpan);
        return { low, high };
    }

    /** Note gem size from perspective scale (matches drawNote). */
    function noteGemSize(scale, H) {
        return Math.max(12, 80 * scale * (H / 900));
    }

    /**
     * Lane y is the highway track center. Gems are drawn above it so fret labels can sit on the track / fret grid.
     */
    function gemLiftFromSize(sz) {
        const half = sz / 2;
        return half + Math.max(6, sz * 0.2);
    }

    function gemCenterYFromLane(laneY, scale, H) {
        return laneY - gemLiftFromSize(noteGemSize(scale, H));
    }

    /** Pitched slide target (`slideTo`), else unpitched (`slideUnpitchTo`). */
    function slideTargetFret(n) {
        const sl = n.sl != null ? n.sl : -1;
        const slu = n.slu != null ? n.slu : -1;
        if (sl >= 0) return sl;
        if (slu >= 0) return slu;
        return -1;
    }

    /** Start/end gems + connector replace the in-gem diagonal slide arrow when sustain defines slide length. */
    function slideUsesConnectorStyle(n) {
        const t = slideTargetFret(n);
        return t >= 0 && t !== n.f && (n.sus || 0) > 0.01;
    }

    /** Lane Y (track) and scale for a single-note row at `tEvent` (with hold-at-now behaviour for the attack). */
    function projectLaneForNoteRow(n, tEvent, useStartHold, H) {
        const tOff = tEvent - currentTime;
        let p;
        if (useStartHold && tOff < -0.05 && n.sus > 0 && n.t + n.sus > currentTime) {
            p = { y: 0.82, scale: 1.0 };
        } else {
            p = project(tOff);
        }
        if (!p) return null;
        return { laneY: p.y * H, scale: p.scale };
    }

    /** Same layout as drawChords for one chord at perspective `p`. */
    function chordLayoutAndOpenBounds(sorted, p, W, H) {
        const sz = Math.max(10, 28 * p.scale * (H / 900));
        const spread = sz * 0.85;
        const minSpread = sz + 16;
        const actualSpread = Math.max(spread, minSpread);
        const actualTotalH = actualSpread * (sorted.length - 1);
        const fretted = sorted.filter((cn) => cn.f > 0).map((cn) => cn.f);
        const gemSz = noteGemSize(p.scale, H);
        const gemHalf = gemSz / 2;
        const gemPad = gemSz * 0.22;
        let chordOpenX0 = null;
        let chordOpenX1 = null;
        if (fretted.length) {
            const minF = Math.min(...fretted);
            const maxF = Math.max(...fretted);
            const { low, high } = expandFretSpan(minF, maxF, 4);
            chordOpenX0 = fretX(low, p.scale, W) - gemHalf - gemPad;
            chordOpenX1 = fretX(high, p.scale, W) + gemHalf + gemPad;
        } else {
            chordOpenX0 = fretX(1, p.scale, W) - gemHalf - gemPad;
            chordOpenX1 = fretX(5, p.scale, W) + gemHalf + gemPad;
        }
        return { sz, actualSpread, actualTotalH, chordOpenX0, chordOpenX1 };
    }

    /**
     * Horizontal span for open strings in a chord on the static fretboard strip.
     * `layoutScale` must match `fretX` used for the bottom grid (same as drawFretNumbers: 1.0).
     * `gemScale` is only for gem size when computing padding (small fretboard dots).
     */
    function fretboardChordOpenBounds(sorted, W, H, layoutScale, gemScale) {
        const fretted = sorted.filter((cn) => cn.f > 0).map((cn) => cn.f);
        const gemSz = noteGemSize(gemScale, H);
        const gemHalf = gemSz / 2;
        const gemPad = gemSz * 0.22;
        let chordOpenX0 = null;
        let chordOpenX1 = null;
        if (fretted.length) {
            const minF = Math.min(...fretted);
            const maxF = Math.max(...fretted);
            const { low, high } = expandFretSpan(minF, maxF, 4);
            chordOpenX0 = fretX(low, layoutScale, W) - gemHalf - gemPad;
            chordOpenX1 = fretX(high, layoutScale, W) + gemHalf + gemPad;
        } else {
            chordOpenX0 = fretX(1, layoutScale, W) - gemHalf - gemPad;
            chordOpenX1 = fretX(5, layoutScale, W) + gemHalf + gemPad;
        }
        return { chordOpenX0, chordOpenX1 };
    }

    function chordSlideGemCenterX(fret, p, W, chordOpenX0, chordOpenX1) {
        if (fret === 0 && chordOpenX0 != null && chordOpenX1 != null) {
            return (chordOpenX0 + chordOpenX1) / 2;
        }
        return fretX(fret, p.scale, W);
    }

    /**
     * Fret digit on the highway below the gem (not inside). Returns y below the text for stacking (e.g. PM).
     */
    function drawHighwayFretLabelBelow(x, fret, shapeBottomY, sz) {
        // Open strings: no digit (line / bar shape is enough).
        if (fret === 0) return shapeBottomY;
        const fontSize = Math.max(14, Math.min(26, sz * 0.52)) | 0;
        const gap = Math.max(3, sz * 0.1);
        const anchor = getAnchorAt(currentTime);
        const inAnchor = fret >= anchor.fret && fret <= anchor.fret + anchor.width;
        ctx.fillStyle = inAnchor ? '#e8c040' : '#b8b8d8';
        ctx.font = `bold ${fontSize}px sans-serif`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'top';
        const yText = shapeBottomY + gap;
        fillTextReadable(String(fret), x, yText);
        return yText + fontSize;
    }

    /** Fret digit centered inside a gem (front fretboard only). */
    function drawFretLabelInsideGem(x, y, fret, sz) {
        if (fret === 0) return;
        const fontSize = Math.max(9, Math.min(sz * 0.5, (sz * 0.85) | 0)) | 0;
        ctx.save();
        ctx.font = `bold ${fontSize}px sans-serif`;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillStyle = '#fff';
        ctx.shadowColor = 'rgba(0,0,0,0.75)';
        ctx.shadowBlur = 3;
        ctx.shadowOffsetY = 1;
        fillTextReadable(String(fret), x, y);
        ctx.restore();
    }

    /** Call while lefty mirror transform is active; keeps glyphs readable. */
    function fillTextReadable(text, x, y) {
        if (!canvas) return;
        const W = canvas.width;
        if (!_lefty) {
            ctx.fillText(text, x, y);
            return;
        }
        ctx.save();
        ctx.setTransform(1, 0, 0, 1, 0, 0);
        ctx.fillText(text, W - x, y);
        ctx.restore();
    }

    // ── Drawing ──────────────────────────────────────────────────────────
    let _drawCount = 0;
    function draw() {
        animFrame = requestAnimationFrame(draw);
        if (!canvas || !ready) return;
        try {
        const W = canvas.width;
        const H = canvas.height;
        if (_drawCount++ < 3) console.log(`draw: W=${W} H=${H} t=${currentTime.toFixed(2)} notes=${notes.length}`);
        ctx.fillStyle = BG;
        ctx.fillRect(0, 0, W, H);

        const anchor = getAnchorAt(currentTime);
        updateSmoothAnchor(anchor, 1 / 60);

        ctx.save();
        if (_lefty) {
            ctx.translate(W, 0);
            ctx.scale(-1, 1);
        }

        drawHighway(W, H);
        drawFretLines(W, H);
        drawBeats(W, H);
        drawStrings(W, H);
        drawSustains(W, H);
        drawNowLine(W, H);
        drawSlideConnectorLines(W, H);
        drawNotes(W, H);
        drawChords(W, H);
        drawSlideEndMarkers(W, H);
        drawFretNumbers(W, H);
        drawChordOnFretboard(W, H);

        // Plugin draw hooks (same coordinate system as the highway)
        for (const hook of _drawHooks) {
            try { hook(ctx, W, H); } catch (e) { /* ignore */ }
        }

        ctx.restore();

        // Lyrics: drawn unmirrored so lines stay left-to-right readable (layout is center-symmetric)
        if (showLyrics) drawLyrics(W, H);

        } catch (e) {
            console.error('draw error:', e);
        }
    }

    function drawHighway(W, H) {
        const strips = 40;
        for (let i = 0; i < strips; i++) {
            const t0 = (i / strips) * VISIBLE_SECONDS;
            const t1 = ((i + 1) / strips) * VISIBLE_SECONDS;
            const p0 = project(t0), p1 = project(t1);
            if (!p0 || !p1) continue;

            const hw0 = W * 0.26 * p0.scale;
            const hw1 = W * 0.26 * p1.scale;
            const bright = 18 + 10 * p0.scale;

            ctx.fillStyle = `rgb(${bright|0},${bright|0},${(bright+14)|0})`;
            ctx.beginPath();
            ctx.moveTo(W/2 - hw0, p0.y * H);
            ctx.lineTo(W/2 + hw0, p0.y * H);
            ctx.lineTo(W/2 + hw1, p1.y * H);
            ctx.lineTo(W/2 - hw1, p1.y * H);
            ctx.fill();
        }
    }

    function drawFretLines(W, H) {
        const pad = 3;
        const lo = 0;
        const hi = Math.ceil(displayMaxFret);
        ctx.strokeStyle = '#2d2d45';
        ctx.lineWidth = 1;

        for (let fret = lo; fret <= hi; fret++) {
            if (fret < 0) continue;
            ctx.beginPath();
            for (let i = 0; i <= 40; i++) {
                const t = (i / 40) * VISIBLE_SECONDS;
                const p = project(t);
                if (!p) continue;
                const x = fretX(fret, p.scale, W);
                if (i === 0) ctx.moveTo(x, p.y * H);
                else ctx.lineTo(x, p.y * H);
            }
            ctx.stroke();
        }
    }

    function drawBeats(W, H) {
        for (const beat of beats) {
            const tOff = beat.time - currentTime;
            const p = project(tOff);
            if (!p || p.scale < 0.06) continue;
            const hw = W * 0.26 * p.scale;
            const isMeasure = beat.measure >= 0;
            ctx.strokeStyle = isMeasure ? '#343450' : '#202038';
            ctx.lineWidth = isMeasure ? 2 : 1;
            ctx.beginPath();
            ctx.moveTo(W/2 - hw, p.y * H);
            ctx.lineTo(W/2 + hw, p.y * H);
            ctx.stroke();
        }
    }

    function drawStrings(W, H) {
        const strTop = H * 0.83;
        const strBot = H * 0.95;
        const margin = W * 0.03;
        // Same vertical order as chord gems on the highway: string 0 at top, 5 at bottom
        // (sorted notes use ascending string index from top of stack downward).
        for (let i = 0; i < 6; i++) {
            const yi = _inverted ? 5 - i : i;
            const y = strTop + (yi / 5) * (strBot - strTop);
            ctx.strokeStyle = STRING_COLORS[i];
            ctx.lineWidth = 3;
            ctx.beginPath();
            ctx.moveTo(margin, y);
            ctx.lineTo(W - margin, y);
            ctx.stroke();
        }
    }

    function drawNowLine(W, H) {
        const y = H * 0.82;
        const hw = W * 0.26;
        // Glow
        for (let i = 1; i < 5; i++) {
            const a = Math.max(0, 70 - i * 15);
            ctx.strokeStyle = `rgba(${a},${a},${a+8},1)`;
            ctx.lineWidth = 1;
            ctx.beginPath();
            ctx.moveTo(W/2 - hw, y - i);
            ctx.lineTo(W/2 + hw, y - i);
            ctx.stroke();
            ctx.beginPath();
            ctx.moveTo(W/2 - hw, y + i);
            ctx.lineTo(W/2 + hw, y + i);
            ctx.stroke();
        }
        ctx.strokeStyle = '#dce0f0';
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(W/2 - hw, y);
        ctx.lineTo(W/2 + hw, y);
        ctx.stroke();
    }

    function drawNote(W, H, x, yLane, scale, string, fret, opts) {
        const isHarmonic = opts?.hm || opts?.hp || false;
        const isPinchHarmonic = opts?.hp || false;
        const isChord = opts?.chord || false;
        const bend = opts?.bn || 0;
        const slide = opts?.sl || -1;
        const hammerOn = opts?.ho || false;
        const pullOff = opts?.po || false;
        const tap = opts?.tp || false;
        const palmMute = opts?.pm || false;
        const fretHandMute = opts?.fhm || false;
        const tremolo = opts?.tr || false;
        const accent = opts?.ac || false;
        const sz = noteGemSize(scale, H);
        const half = sz / 2;
        const color = STRING_COLORS[string] || '#888';
        const dark = STRING_DIM[string] || '#222';
        const lift = gemLiftFromSize(sz);
        const y = yLane - lift;

        if (sz < 6 && !(fret === 0 && isChord && opts.chordOpenX0 != null)) {
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.arc(x, y, 2, 0, Math.PI * 2);
            ctx.fill();
            if (fret !== 0) {
                if (opts?.fretLabelInside) drawFretLabelInsideGem(x, y, fret, sz);
                else drawHighwayFretLabelBelow(x, fret, y + 3, Math.max(8, sz));
            }
            return;
        }

        // Open string inside a chord: horizontal line over the fretted span (≥4 frets)
        if (fret === 0 && isChord && opts.chordOpenX0 != null && opts.chordOpenX1 != null) {
            const xL = Math.min(opts.chordOpenX0, opts.chordOpenX1);
            const xR = Math.max(opts.chordOpenX0, opts.chordOpenX1);
            const lw = Math.max(3, sz * 0.38);
            ctx.strokeStyle = dark;
            ctx.lineWidth = lw + 2;
            ctx.lineCap = 'round';
            ctx.beginPath();
            ctx.moveTo(xL, y + 1);
            ctx.lineTo(xR, y + 1);
            ctx.stroke();
            ctx.strokeStyle = color;
            ctx.lineWidth = lw;
            ctx.beginPath();
            ctx.moveTo(xL, y);
            ctx.lineTo(xR, y);
            ctx.stroke();
            ctx.lineCap = 'butt';
            if (opts?.fretLabelInside) {
                const cx = (xL + xR) / 2;
                const fontSize = Math.max(8, Math.min(sz * 0.42, lw * 1.8)) | 0;
                ctx.save();
                ctx.font = `bold ${fontSize}px sans-serif`;
                ctx.textAlign = 'center';
                ctx.textBaseline = 'middle';
                ctx.fillStyle = '#fff';
                ctx.shadowColor = 'rgba(0,0,0,0.75)';
                ctx.shadowBlur = 2;
                ctx.shadowOffsetY = 1;
                fillTextReadable('0', cx, y);
                ctx.restore();
            }
            return;
        }

        // Open string: wide bar spanning the highway (only for standalone notes)
        if (fret === 0 && !isChord) {
            const hw = W * 0.26 * scale;
            const barH = Math.max(6, sz * 0.45);
            // Shadow
            ctx.fillStyle = dark;
            roundRect(ctx, W/2 - hw - 1, y - barH/2 - 1, hw * 2 + 2, barH + 2, 3);
            ctx.fill();
            // Body
            ctx.fillStyle = color;
            roundRect(ctx, W/2 - hw, y - barH/2, hw * 2, barH, 2);
            ctx.fill();
            return;
        }

        let shapeBottom = y + half;
        if (isHarmonic) {
            // Diamond shape for harmonics
            const dh = half * 1.15;
            shapeBottom = y + dh;
            // Glow
            ctx.fillStyle = dark;
            ctx.beginPath();
            ctx.moveTo(x, y - dh - 3); ctx.lineTo(x + half + 3, y);
            ctx.lineTo(x, y + dh + 3); ctx.lineTo(x - half - 3, y);
            ctx.closePath(); ctx.fill();
            // Body
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.moveTo(x, y - dh); ctx.lineTo(x + half, y);
            ctx.lineTo(x, y + dh); ctx.lineTo(x - half, y);
            ctx.closePath(); ctx.fill();
            // Bright outline
            ctx.strokeStyle = STRING_BRIGHT[string] || '#fff';
            ctx.lineWidth = 2;
            ctx.beginPath();
            ctx.moveTo(x, y - dh); ctx.lineTo(x + half, y);
            ctx.lineTo(x, y + dh); ctx.lineTo(x - half, y);
            ctx.closePath(); ctx.stroke();
            // PH label for pinch harmonics
            if (isPinchHarmonic && sz >= 14) {
                ctx.fillStyle = '#ff0';
                const phPx = Math.max(8, sz * 0.25) | 0;
                ctx.font = `bold ${phPx}px sans-serif`;
                ctx.textAlign = 'center';
                ctx.textBaseline = 'top';
                fillTextReadable('PH', x, y + dh + 2);
                shapeBottom = y + dh + 2 + phPx + 2;
            }
        } else {
            // Glow
            ctx.fillStyle = dark;
            roundRect(ctx, x - half - 4, y - half - 4, sz + 8, sz + 8, sz / 3);
            ctx.fill();
            // Body
            ctx.fillStyle = color;
            roundRect(ctx, x - half, y - half, sz, sz, sz / 5);
            ctx.fill();
        }

        // Palm mute: black X; fret-hand mute: white X (under pull-off / hammer-on triangles)
        function strokeMuteX(strokeColor) {
            ctx.save();
            if (strokeColor === '#fff') {
                ctx.shadowColor = 'rgba(0,0,0,0.55)';
                ctx.shadowBlur = 2;
            }
            ctx.beginPath();
            if (isHarmonic) {
                const dh = half * 1.15;
                ctx.moveTo(x, y - dh);
                ctx.lineTo(x + half, y);
                ctx.lineTo(x, y + dh);
                ctx.lineTo(x - half, y);
                ctx.closePath();
            } else {
                roundRect(ctx, x - half, y - half, sz, sz, sz / 5);
            }
            ctx.clip();
            ctx.strokeStyle = strokeColor;
            ctx.lineWidth = Math.max(2, sz / 7);
            ctx.lineCap = 'square';
            ctx.lineJoin = 'miter';
            ctx.beginPath();
            if (isHarmonic) {
                const dh = half * 1.15;
                ctx.moveTo(x - half, y - dh);
                ctx.lineTo(x + half, y + dh);
                ctx.moveTo(x + half, y - dh);
                ctx.lineTo(x - half, y + dh);
            } else {
                ctx.moveTo(x - half, y - half);
                ctx.lineTo(x + half, y + half);
                ctx.moveTo(x + half, y - half);
                ctx.lineTo(x - half, y + half);
            }
            ctx.stroke();
            ctx.restore();
        }
        if (palmMute) strokeMuteX('#000');
        if (fretHandMute) strokeMuteX('#fff');

        // Pull-off: white upward-pointing equilateral triangle inscribed in the gem (replaces "P" above)
        if (pullOff) {
            ctx.fillStyle = '#fff';
            ctx.beginPath();
            if (isHarmonic) {
                // Diamond: apex at top vertex, base on lower sides (touches left/right borders)
                const dh = half * 1.15;
                const v =
                    (half * Math.sqrt(3) * dh - dh * dh) /
                    (dh + half * Math.sqrt(3));
                const yTop = y - dh;
                const yBot = y + v;
                const H = yBot - yTop;
                const halfW = H / Math.sqrt(3);
                ctx.moveTo(x, yTop);
                ctx.lineTo(x - halfW, yBot);
                ctx.lineTo(x + halfW, yBot);
            } else {
                // Round-rect gem (radius sz/5): largest equilateral with apex on inner top, base spanning inner width
                const r = sz / 5;
                const innerTop = y - half + r;
                const innerBot = y + half - r;
                const innerHalfW = half - r;
                const maxHVert = innerBot - innerTop;
                const maxHWidth = innerHalfW * Math.sqrt(3);
                const H = Math.min(maxHVert, maxHWidth);
                const halfW = H / Math.sqrt(3);
                const yTop = innerTop;
                const yBot = innerTop + H;
                ctx.moveTo(x, yTop);
                ctx.lineTo(x - halfW, yBot);
                ctx.lineTo(x + halfW, yBot);
            }
            ctx.closePath();
            ctx.fill();
        } else if (hammerOn) {
            // Hammer-on: white downward-pointing equilateral triangle (mirror of pull-off; replaces "H" above)
            ctx.fillStyle = '#fff';
            ctx.beginPath();
            if (isHarmonic) {
                const dh = half * 1.15;
                const v =
                    (half * Math.sqrt(3) * dh - dh * dh) /
                    (dh + half * Math.sqrt(3));
                const yBot = y + dh;
                const yTop = y - v;
                const H = yBot - yTop;
                const halfW = H / Math.sqrt(3);
                ctx.moveTo(x, yBot);
                ctx.lineTo(x - halfW, yTop);
                ctx.lineTo(x + halfW, yTop);
            } else {
                const r = sz / 5;
                const innerTop = y - half + r;
                const innerBot = y + half - r;
                const innerHalfW = half - r;
                const maxHVert = innerBot - innerTop;
                const maxHWidth = innerHalfW * Math.sqrt(3);
                const H = Math.min(maxHVert, maxHWidth);
                const halfW = H / Math.sqrt(3);
                const yBot = innerBot;
                const yTop = innerBot - H;
                ctx.moveTo(x, yBot);
                ctx.lineTo(x - halfW, yTop);
                ctx.lineTo(x + halfW, yTop);
            }
            ctx.closePath();
            ctx.fill();
        }

        // Bend notation
        if (bend && bend > 0 && sz >= 12) {
            const lw = Math.max(2, sz / 10);
            const arrowH = sz * 0.55 * Math.min(bend, 2);  // taller for bigger bends
            const ay = y - half - 4;
            const tipY = ay - arrowH;

            ctx.strokeStyle = '#fff';
            ctx.lineWidth = lw;

            // Curved arrow
            ctx.beginPath();
            ctx.moveTo(x, ay);
            ctx.quadraticCurveTo(x + sz * 0.2, ay - arrowH * 0.5, x, tipY);
            ctx.stroke();

            // Arrowhead
            ctx.beginPath();
            ctx.moveTo(x - sz * 0.12, tipY + sz * 0.12);
            ctx.lineTo(x, tipY);
            ctx.lineTo(x + sz * 0.12, tipY + sz * 0.12);
            ctx.stroke();

            // Bend label: "full", "1/2", "1 1/2", "2"
            let label;
            if (bend === 0.5) label = '½';
            else if (bend === 1) label = 'full';
            else if (bend === 1.5) label = '1½';
            else if (bend === 2) label = '2';
            else label = bend.toFixed(1);

            ctx.fillStyle = '#fff';
            ctx.font = `bold ${Math.max(9, sz * 0.28) | 0}px sans-serif`;
            ctx.textAlign = 'center';
            ctx.textBaseline = 'bottom';
            fillTextReadable(label, x, tipY - 2);
        }

        if (opts?.fretLabelInside) {
            drawFretLabelInsideGem(x, y, fret, sz);
        } else {
            drawHighwayFretLabelBelow(x, fret, shapeBottom, sz);
        }

        if (sz < 14) return;  // Skip small technique labels

        // Slide indicator (diagonal arrow) — not when start/end connector + destination gem is used
        if (slide >= 0 && !slideUsesConnectorStyle(opts)) {
            const dir = slide > fret ? -1 : 1;  // arrow direction (up or down the neck); mirror handles lefty
            ctx.strokeStyle = '#fff';
            ctx.lineWidth = Math.max(2, sz / 10);
            ctx.beginPath();
            ctx.moveTo(x - sz * 0.3, y + dir * sz * 0.3);
            ctx.lineTo(x + sz * 0.3, y - dir * sz * 0.3);
            ctx.stroke();
            // Arrowhead
            ctx.beginPath();
            ctx.moveTo(x + sz * 0.3, y - dir * sz * 0.3);
            ctx.lineTo(x + sz * 0.15, y - dir * sz * 0.15);
            ctx.stroke();
        }

        // T label above note (hammer-on / pull-off use in-gem triangles; pull-off points up, hammer-on down)
        if (tap) {
            const label = 'T';
            const ly = y - half - (bend > 0 ? sz * 0.6 : 4);
            ctx.fillStyle = '#fff';
            ctx.font = `bold ${Math.max(9, sz * 0.3) | 0}px sans-serif`;
            ctx.textAlign = 'center';
            ctx.textBaseline = 'bottom';
            fillTextReadable(label, x, ly);
        }

        // Tremolo (wavy line above)
        if (tremolo) {
            const ty = y - half - (bend > 0 ? sz * 0.7 : 6);
            ctx.strokeStyle = '#ff0';
            ctx.lineWidth = 1.5;
            ctx.beginPath();
            for (let i = -3; i <= 3; i++) {
                const wx = x + i * sz * 0.08;
                const wy = ty + Math.sin(i * 2) * 3;
                if (i === -3) ctx.moveTo(wx, wy);
                else ctx.lineTo(wx, wy);
            }
            ctx.stroke();
        }

        // Accent (> marker)
        if (accent) {
            const ay2 = y - half - 4;
            ctx.strokeStyle = '#fff';
            ctx.lineWidth = 2;
            ctx.beginPath();
            ctx.moveTo(x - sz * 0.2, ay2 + 3);
            ctx.lineTo(x, ay2 - 2);
            ctx.lineTo(x + sz * 0.2, ay2 + 3);
            ctx.stroke();
        }
    }

    function drawSustains(W, H) {
        for (const n of notes) {
            if (n.sus <= 0.01) continue;
            const end = n.t + n.sus;
            if (end < currentTime || n.t > currentTime + VISIBLE_SECONDS) continue;

            const t0 = Math.max(n.t - currentTime, 0);
            const t1 = Math.min(end - currentTime, VISIBLE_SECONDS);
            if (t0 >= t1) continue;

            const p0 = project(t0), p1 = project(t1);
            if (!p0 || !p1) continue;

            const x0 = fretX(n.f, p0.scale, W);
            const x1 = fretX(n.f, p1.scale, W);
            const sw0 = Math.max(2, 6 * p0.scale);
            const sw1 = Math.max(2, 6 * p1.scale);

            ctx.fillStyle = STRING_DIM[n.s] || '#333';
            ctx.beginPath();
            ctx.moveTo(x0 - sw0, p0.y * H);
            ctx.lineTo(x0 + sw0, p0.y * H);
            ctx.lineTo(x1 + sw1, p1.y * H);
            ctx.lineTo(x1 - sw1, p1.y * H);
            ctx.fill();
        }
    }

    /** Notes at the same time (within 0.01s), each group length ≥ 2 */
    function groupNotesByTime(drawnNotes) {
        const groups = [];
        const used = new Set();
        for (let i = 0; i < drawnNotes.length; i++) {
            if (used.has(i)) continue;
            const group = [drawnNotes[i]];
            used.add(i);
            for (let j = i + 1; j < drawnNotes.length; j++) {
                if (used.has(j)) continue;
                if (Math.abs(drawnNotes[j].t - drawnNotes[i].t) < 0.01) {
                    group.push(drawnNotes[j]);
                    used.add(j);
                }
            }
            if (group.length >= 2) groups.push(group);
        }
        return groups;
    }

    /** U-shaped outline open at top; drawn behind note gems */
    function strokeSimultaneousOutline(W, H, group) {
        let xMin = Infinity;
        let xMax = -Infinity;
        let yTop = Infinity;
        let yBot = -Infinity;
        for (const n of group) {
            const noteSz = noteGemSize(n.scale, H);
            const half = noteSz / 2;
            const pad = noteSz * 0.22;
            const yG = gemCenterYFromLane(n.y, n.scale, H);
            yTop = Math.min(yTop, yG - half - pad);
            yBot = Math.max(yBot, yG + half + pad);
            if (n.f === 0 && n.xL != null && n.xR != null) {
                // xL/xR are outer horizontal bounds (same as fretted n.x ± half ± pad)
                const xL = Math.min(n.xL, n.xR);
                const xR = Math.max(n.xL, n.xR);
                xMin = Math.min(xMin, xL);
                xMax = Math.max(xMax, xR);
            } else if (n.f === 0) {
                const hw = W * 0.26 * n.scale;
                xMin = Math.min(xMin, W / 2 - hw - pad);
                xMax = Math.max(xMax, W / 2 + hw + pad);
            } else {
                xMin = Math.min(xMin, n.x - half - pad);
                xMax = Math.max(xMax, n.x + half + pad);
            }
        }
        const noteSz0 = noteGemSize(group[0].scale, H);
        const lw = Math.max(1, Math.min(1.5, noteSz0 * 0.026));
        ctx.save();
        ctx.strokeStyle = 'rgba(255,255,255,0.9)';
        ctx.lineWidth = lw;
        ctx.lineJoin = 'miter';
        ctx.beginPath();
        ctx.moveTo(xMin, yTop);
        ctx.lineTo(xMin, yBot);
        ctx.lineTo(xMax, yBot);
        ctx.lineTo(xMax, yTop);
        ctx.stroke();
        ctx.restore();
    }

    function drawNotes(W, H) {
        // Binary search for visible range
        const tMin = currentTime - 0.25;
        const tMax = currentTime + VISIBLE_SECONDS;
        let lo = bsearch(notes, tMin);
        let hi = bsearch(notes, tMax);

        // Include sustained notes
        while (lo > 0 && notes[lo-1].t + notes[lo-1].sus > currentTime) lo--;

        const drawnNotes = [];

        for (let i = hi - 1; i >= lo; i--) {
            const n = notes[i];
            let tOff = n.t - currentTime;

            // Hold sustained notes at now line
            let p;
            if (tOff < -0.05 && n.sus > 0 && n.t + n.sus > currentTime) {
                p = { y: 0.82, scale: 1.0 };
            } else {
                p = project(tOff);
            }
            if (!p) continue;

            const x = fretX(n.f, p.scale, W);
            drawnNotes.push({ t: n.t, s: n.s, f: n.f, bn: n.bn || 0, x, y: p.y * H, scale: p.scale, _n: n });
        }

        for (const g of groupNotesByTime(drawnNotes)) {
            strokeSimultaneousOutline(W, H, g);
        }
        for (const dn of drawnNotes) {
            const n = dn._n;
            drawNote(W, H, dn.x, dn.y, dn.scale, n.s, n.f, n);
        }

        drawUnisonBends(W, H, drawnNotes);
    }

    function drawUnisonBends(W, H, drawnNotes) {
        for (const group of groupNotesByTime(drawnNotes)) {
            // Find pairs: one with bend, one without (or both with different bends)
            const bent = group.filter(n => n.bn > 0);
            const unbent = group.filter(n => n.bn === 0);
            if (bent.length === 0 || unbent.length === 0) continue;

            // Draw connector between each bent-unbent pair
            for (const bn of bent) {
                // Find the closest unbent note by string
                let closest = unbent[0];
                for (const ub of unbent) {
                    if (Math.abs(ub.s - bn.s) < Math.abs(closest.s - bn.s)) closest = ub;
                }

                const sz = noteGemSize(bn.scale, H);
                if (sz < 14) continue;

                // Draw a curved dashed line connecting bent note to target note
                const x1 = bn.x, y1 = gemCenterYFromLane(bn.y, bn.scale, H);
                const x2 = closest.x, y2 = gemCenterYFromLane(closest.y, closest.scale, H);
                const midX = (x1 + x2) / 2 + sz * 0.5;
                const midY = (y1 + y2) / 2;

                ctx.save();
                ctx.strokeStyle = '#60d0ff';
                ctx.lineWidth = Math.max(2, sz / 12);
                ctx.setLineDash([4, 4]);
                ctx.beginPath();
                ctx.moveTo(x1, y1);
                ctx.quadraticCurveTo(midX, midY, x2, y2);
                ctx.stroke();
                ctx.setLineDash([]);
                ctx.restore();

                // "U" label at midpoint
                const labelSz = Math.max(10, sz * 0.3) | 0;
                ctx.fillStyle = '#60d0ff';
                ctx.font = `bold ${labelSz}px sans-serif`;
                ctx.textAlign = 'center';
                ctx.textBaseline = 'middle';
                const cpX = (x1 + 2 * midX + x2) / 4;
                const cpY = (y1 + 2 * midY + y2) / 4;
                fillTextReadable('U', cpX + sz * 0.3, cpY);
            }
        }
    }

    /** White connector from slide start gem to end gem (drawn under note sprites). */
    function drawSlideConnectorLines(W, H) {
        const tMin = currentTime - 0.25;
        const tMax = currentTime + VISIBLE_SECONDS;
        ctx.save();
        ctx.strokeStyle = 'rgba(255,255,255,0.88)';
        ctx.lineWidth = Math.max(2, 2.5 * (H / 900));
        ctx.lineCap = 'round';

        let lo = bsearch(notes, tMin);
        let hi = bsearch(notes, tMax);
        while (lo > 0 && notes[lo - 1].t + notes[lo - 1].sus > currentTime) lo--;

        for (let i = hi - 1; i >= lo; i--) {
            const n = notes[i];
            if (!slideUsesConnectorStyle(n)) continue;
            const target = slideTargetFret(n);
            const t1 = n.t + n.sus;
            if (t1 < tMin || n.t > tMax) continue;

            const lane0 = projectLaneForNoteRow(n, n.t, true, H);
            const lane1 = projectLaneForNoteRow(n, t1, false, H);
            if (!lane0 || !lane1) continue;

            const x0 = fretX(n.f, lane0.scale, W);
            const x1 = fretX(target, lane1.scale, W);
            const cy0 = gemCenterYFromLane(lane0.laneY, lane0.scale, H);
            const cy1 = gemCenterYFromLane(lane1.laneY, lane1.scale, H);

            ctx.beginPath();
            ctx.moveTo(x0, cy0);
            ctx.lineTo(x1, cy1);
            ctx.stroke();
        }

        lo = bsearchChords(chords, tMin);
        hi = bsearchChords(chords, tMax);
        for (let i = hi - 1; i >= lo; i--) {
            const ch = chords[i];
            const p0 = project(ch.t - currentTime);
            if (!p0) continue;
            const sorted = [...ch.notes].sort((a, b) => a.s - b.s);
            const showFullChord = sorted.length < 2 || chordShowsFullAfterPredecessor(ch);
            if (!showFullChord) continue;

            const lay0 = chordLayoutAndOpenBounds(sorted, p0, W, H);
            for (let j = 0; j < sorted.length; j++) {
                const cn = sorted[j];
                if (!slideUsesConnectorStyle(cn)) continue;
                const target = slideTargetFret(cn);
                const t1 = ch.t + cn.sus;
                const p1 = project(t1 - currentTime);
                if (!p1) continue;

                const lay1 = chordLayoutAndOpenBounds(sorted, p1, W, H);
                const y0 = p0.y * H - lay0.actualTotalH / 2 + j * lay0.actualSpread;
                const y1 = p1.y * H - lay1.actualTotalH / 2 + j * lay1.actualSpread;
                const x0 = chordSlideGemCenterX(cn.f, p0, W, lay0.chordOpenX0, lay0.chordOpenX1);
                const x1 = chordSlideGemCenterX(target, p1, W, lay1.chordOpenX0, lay1.chordOpenX1);
                const cy0 = gemCenterYFromLane(y0, p0.scale, H);
                const cy1 = gemCenterYFromLane(y1, p1.scale, H);

                ctx.beginPath();
                ctx.moveTo(x0, cy0);
                ctx.lineTo(x1, cy1);
                ctx.stroke();
            }
        }

        ctx.restore();
    }

    /** Destination fret gem for slides (after start notes / chords are drawn). */
    function drawSlideEndMarkers(W, H) {
        const tMin = currentTime - 0.25;
        const tMax = currentTime + VISIBLE_SECONDS;
        const neutral = {
            hm: false, hp: false, bn: 0, ho: false, po: false, tp: false,
            pm: false, tr: false, ac: false, mt: false,
            sl: -1, slu: -1, sus: 0,
        };

        let lo = bsearch(notes, tMin);
        let hi = bsearch(notes, tMax);
        while (lo > 0 && notes[lo - 1].t + notes[lo - 1].sus > currentTime) lo--;

        for (let i = hi - 1; i >= lo; i--) {
            const n = notes[i];
            if (!slideUsesConnectorStyle(n)) continue;
            const target = slideTargetFret(n);
            const t1 = n.t + n.sus;
            if (t1 - currentTime < -0.05) continue;

            const lane1 = projectLaneForNoteRow(n, t1, false, H);
            if (!lane1) continue;

            const x1 = fretX(target, lane1.scale, W);
            drawNote(W, H, x1, lane1.laneY, lane1.scale, n.s, target, { ...n, ...neutral });
        }

        lo = bsearchChords(chords, tMin);
        hi = bsearchChords(chords, tMax);
        for (let i = hi - 1; i >= lo; i--) {
            const ch = chords[i];
            if (!project(ch.t - currentTime)) continue;
            const sorted = [...ch.notes].sort((a, b) => a.s - b.s);
            const showFullChord = sorted.length < 2 || chordShowsFullAfterPredecessor(ch);
            if (!showFullChord) continue;

            for (let j = 0; j < sorted.length; j++) {
                const cn = sorted[j];
                if (!slideUsesConnectorStyle(cn)) continue;
                const target = slideTargetFret(cn);
                const t1 = ch.t + cn.sus;
                if (t1 - currentTime < -0.05) continue;

                const p1 = project(t1 - currentTime);
                if (!p1) continue;

                const lay1 = chordLayoutAndOpenBounds(sorted, p1, W, H);
                const ny = p1.y * H - lay1.actualTotalH / 2 + j * lay1.actualSpread;
                const opts = { ...cn, ...neutral, chord: true };
                if (target === 0) {
                    opts.chordOpenX0 = lay1.chordOpenX0;
                    opts.chordOpenX1 = lay1.chordOpenX1;
                }
                const xBase = fretX(target, p1.scale, W);
                drawNote(W, H, xBase, ny, p1.scale, cn.s, target, opts);
            }
        }
    }

    function drawChords(W, H) {
        const tMin = currentTime - 0.25;
        const tMax = currentTime + VISIBLE_SECONDS;
        let lo = bsearchChords(chords, tMin);
        let hi = bsearchChords(chords, tMax);

        for (let i = hi - 1; i >= lo; i--) {
            const ch = chords[i];
            const p = project(ch.t - currentTime);
            if (!p) continue;

            const sorted = [...ch.notes].sort((a, b) => _inverted ? b.s - a.s : a.s - b.s);
            const showFullChord = sorted.length < 2 || chordShowsFullAfterPredecessor(ch);
            const sz = Math.max(10, 28 * p.scale * (H / 900));
            const spread = sz * 0.85;
            const minSpread = sz + 16;  // full note size + gap (accounts for glow)
            const actualSpread = Math.max(spread, minSpread);
            const actualTotalH = actualSpread * (sorted.length - 1);

            const fretted = sorted.filter((cn) => cn.f > 0).map((cn) => cn.f);
            let chordOpenX0 = null;
            let chordOpenX1 = null;
            // Match strokeSimultaneousOutline / chord gem bounds: center ± half ± pad (not fret centers).
            const gemSz = noteGemSize(p.scale, H);
            const gemHalf = gemSz / 2;
            const gemPad = gemSz * 0.22;
            if (fretted.length) {
                const minF = Math.min(...fretted);
                const maxF = Math.max(...fretted);
                const { low, high } = expandFretSpan(minF, maxF, 4);
                chordOpenX0 = fretX(low, p.scale, W) - gemHalf - gemPad;
                chordOpenX1 = fretX(high, p.scale, W) + gemHalf + gemPad;
            } else {
                chordOpenX0 = fretX(1, p.scale, W) - gemHalf - gemPad;
                chordOpenX1 = fretX(5, p.scale, W) + gemHalf + gemPad;
            }

            if (sorted.length >= 2) {
                const outlineGroup = sorted.map((cn, j) => {
                    const xBase = fretX(cn.f, p.scale, W);
                    const ny = p.y * H - actualTotalH / 2 + j * actualSpread;
                    const o = {
                        x: xBase, y: ny, scale: p.scale, f: cn.f,
                        s: cn.s, bn: cn.bn || 0, t: ch.t,
                    };
                    if (cn.f === 0 && chordOpenX0 != null && chordOpenX1 != null) {
                        o.xL = chordOpenX0;
                        o.xR = chordOpenX1;
                    }
                    return o;
                });
                strokeSimultaneousOutline(W, H, outlineGroup);
            }

            // Chord name label (hidden when outline-only repeat: same chord directly before)
            if (showFullChord && !ch.hd && p.scale > 0.15) {
                const tmpl = chordTemplates[ch.id];
                if (tmpl && tmpl.name) {
                    const labelY = (sorted.length >= 2)
                        ? (p.y * H - actualTotalH / 2 - sz * 0.7 - sz * 0.4)
                        : (p.y * H - sz * 0.8);
                    const labelX = (sorted.length >= 2)
                        ? (Math.min(...sorted.map(cn => fretX(cn.f, p.scale, W))) + Math.max(...sorted.map(cn => fretX(cn.f, p.scale, W)))) / 2
                        : fretX(sorted[0].f, p.scale, W);
                    ctx.fillStyle = '#fff';
                    ctx.font = `bold ${Math.max(14, sz * 0.45) | 0}px sans-serif`;
                    ctx.textAlign = 'center';
                    ctx.textBaseline = 'bottom';
                    fillTextReadable(tmpl.name, labelX, labelY);
                }
            }

            // Notes — outline-only when previous event matched this chord exactly (shape + techniques)
            const chordPositions = [];
            if (showFullChord) {
                sorted.forEach((cn, j) => {
                    const xBase = fretX(cn.f, p.scale, W);
                    const ny = p.y * H - actualTotalH / 2 + j * actualSpread;
                    const opts = { ...cn, chord: true };
                    if (cn.f === 0) {
                        opts.chordOpenX0 = chordOpenX0;
                        opts.chordOpenX1 = chordOpenX1;
                    }
                    const x = cn.f === 0 ? (chordOpenX0 + chordOpenX1) / 2 : xBase;
                    drawNote(W, H, xBase, ny, p.scale, cn.s, cn.f, opts);
                    chordPositions.push({ s: cn.s, f: cn.f, bn: cn.bn || 0, x, y: ny, scale: p.scale });
                });
            }

            // Unison bend within chord
            const bent = chordPositions.filter(n => n.bn > 0);
            const unbent = chordPositions.filter(n => n.bn === 0);
            const ng = noteGemSize(p.scale, H);
            if (bent.length > 0 && unbent.length > 0 && ng >= 14) {
                for (const bn of bent) {
                    let closest = unbent[0];
                    for (const ub of unbent) {
                        if (Math.abs(ub.s - bn.s) < Math.abs(closest.s - bn.s)) closest = ub;
                    }
                    const x1 = bn.x, y1 = gemCenterYFromLane(bn.y, bn.scale, H);
                    const x2 = closest.x, y2 = gemCenterYFromLane(closest.y, closest.scale, H);
                    const midX = (x1 + x2) / 2 + ng * 0.5;
                    const midY = (y1 + y2) / 2;

                    ctx.save();
                    ctx.strokeStyle = '#60d0ff';
                    ctx.lineWidth = Math.max(2, ng / 12);
                    ctx.setLineDash([4, 4]);
                    ctx.beginPath();
                    ctx.moveTo(x1, y1);
                    ctx.quadraticCurveTo(midX, midY, x2, y2);
                    ctx.stroke();
                    ctx.setLineDash([]);
                    ctx.restore();

                    const labelSz = Math.max(10, ng * 0.3) | 0;
                    ctx.fillStyle = '#60d0ff';
                    ctx.font = `bold ${labelSz}px sans-serif`;
                    ctx.textAlign = 'center';
                    ctx.textBaseline = 'middle';
                    const cpX = (x1 + 2 * midX + x2) / 4;
                    const cpY = (y1 + 2 * midY + y2) / 4;
                    fillTextReadable('U', cpX + ng * 0.3, cpY);
                }
            }
        }
    }

    /**
     * Current chord voicing on the bottom string strip (same time-slice pick as other “closest” UI).
     * Shows for every chord shape, not only outline-only repeats on the highway.
     */
    function drawChordOnFretboard(W, H) {
        const tMin = currentTime - 0.25;
        const tMax = currentTime + VISIBLE_SECONDS;
        const lo = bsearchChords(chords, tMin);
        const hi = bsearchChords(chords, tMax);

        let bestSorted = null;
        let bestDt = Infinity;

        for (let i = hi - 1; i >= lo; i--) {
            const ch = chords[i];
            if (!project(ch.t - currentTime)) continue;
            const sorted = [...ch.notes].sort((a, b) => a.s - b.s);
            if (!sorted.length) continue;

            const dt = Math.abs(ch.t - currentTime);
            if (dt < bestDt) {
                bestDt = dt;
                bestSorted = sorted;
            }
        }

        if (!bestSorted) return;

        const strTop = H * 0.83;
        const strBot = H * 0.95;
        // Large dots on the strip; may overlap adjacent strings (2× previous size).
        const stringGap = (strBot - strTop) / 5;
        const targetGem = stringGap * 0.36 * 4;
        let gemScale = targetGem / (80 * (H / 900));
        gemScale = Math.min(1.1, Math.max(0.14, gemScale));

        const layoutScale = 1.0;
        const lay = fretboardChordOpenBounds(bestSorted, W, H, layoutScale, gemScale);

        bestSorted.forEach((cn) => {
            const yStr = strTop + (cn.s / 5) * (strBot - strTop);
            const lift = gemLiftFromSize(noteGemSize(gemScale, H));
            const yLane = yStr + lift;
            const xBase = fretX(cn.f, layoutScale, W);
            const opts = { ...cn, chord: true, fretLabelInside: true };
            if (cn.f === 0) {
                opts.chordOpenX0 = lay.chordOpenX0;
                opts.chordOpenX1 = lay.chordOpenX1;
            }
            drawNote(W, H, xBase, yLane, gemScale, cn.s, cn.f, opts);
        });
    }

    function drawFretNumbers(W, H) {
        // Along the vertical fret grid, below the strings — gems float above this band.
        const y = H * 0.945;
        const lo = 0;
        const hi = Math.ceil(displayMaxFret);
        const anchor = getAnchorAt(currentTime);

        ctx.font = 'bold 20px sans-serif';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';

        for (let fret = lo; fret <= hi; fret++) {
            if (fret < 0) continue;
            const x = fretX(fret, 1.0, W);
            const inAnchor = fret >= anchor.fret && fret <= anchor.fret + anchor.width;
            ctx.fillStyle = inAnchor ? '#e8c040' : '#8a6830';
            fillTextReadable(String(fret), x, y);
        }
    }

    // ── Helpers ───────────────────────────────────────────────────────────
    function drawLyrics(W, H) {
        if (!lyrics.length) return;

        const fontSize = Math.max(18, H * 0.028) | 0;
        const lineY = H * 0.04;

        // Find phrases: groups of words separated by gaps > 2s or "+" endings
        // Pre-build phrases once (cache)
        if (!lyrics._phrases) {
            lyrics._phrases = [];
            let phrase = [];
            for (let i = 0; i < lyrics.length; i++) {
                const l = lyrics[i];
                if (phrase.length > 0) {
                    const prev = phrase[phrase.length - 1];
                    const gap = l.t - (prev.t + prev.d);
                    if (gap > 2.0) {
                        lyrics._phrases.push(phrase);
                        phrase = [];
                    }
                }
                phrase.push(l);
            }
            if (phrase.length) lyrics._phrases.push(phrase);
        }

        // Find the current phrase
        let currentPhrase = null;
        for (const p of lyrics._phrases) {
            const start = p[0].t;
            const end = p[p.length - 1].t + p[p.length - 1].d;
            if (currentTime >= start - 0.5 && currentTime <= end + 1.0) {
                currentPhrase = p;
                break;
            }
        }

        if (!currentPhrase) return;

        // Split phrase into rows that fit within maxWidth
        const maxWidth = W * 0.8;
        ctx.font = `bold ${fontSize}px sans-serif`;

        const rows = [];
        let currentRow = [];
        let currentRowWidth = 0;

        for (let i = 0; i < currentPhrase.length; i++) {
            const word = currentPhrase[i].w.replace(/\+$/, '') + ' ';
            const wordWidth = ctx.measureText(word).width;

            if (currentRow.length > 0 && currentRowWidth + wordWidth > maxWidth) {
                rows.push(currentRow);
                currentRow = [];
                currentRowWidth = 0;
            }
            currentRow.push({ lyric: currentPhrase[i], text: word, width: wordWidth });
            currentRowWidth += wordWidth;
        }
        if (currentRow.length) rows.push(currentRow);

        // Draw background
        const rowHeight = fontSize + 6;
        const totalHeight = rows.length * rowHeight + 10;
        let bgWidth = 0;
        for (const row of rows) {
            const rw = row.reduce((s, w) => s + w.width, 0);
            if (rw > bgWidth) bgWidth = rw;
        }
        bgWidth = Math.min(bgWidth + 30, W * 0.85);

        ctx.fillStyle = 'rgba(0,0,0,0.7)';
        roundRect(ctx, W/2 - bgWidth/2, lineY - 4, bgWidth, totalHeight, 8);
        ctx.fill();

        // Draw each row
        ctx.textAlign = 'left';
        ctx.textBaseline = 'top';

        for (let r = 0; r < rows.length; r++) {
            const row = rows[r];
            const rowWidth = row.reduce((s, w) => s + w.width, 0);
            let xPos = W/2 - rowWidth/2;
            const yPos = lineY + r * rowHeight + 2;

            for (const w of row) {
                const l = w.lyric;
                const isActive = currentTime >= l.t && currentTime < l.t + l.d;
                const isPast = currentTime >= l.t + l.d;

                if (isActive) {
                    ctx.fillStyle = '#4ae0ff';
                    ctx.font = `bold ${fontSize}px sans-serif`;
                } else if (isPast) {
                    ctx.fillStyle = '#8899aa';
                    ctx.font = `normal ${fontSize}px sans-serif`;
                } else {
                    ctx.fillStyle = '#556677';
                    ctx.font = `normal ${fontSize}px sans-serif`;
                }

                ctx.fillText(w.text, xPos, yPos);
                xPos += w.width;
            }
        }
    }

    function roundRect(ctx, x, y, w, h, r) {
        ctx.beginPath();
        ctx.moveTo(x + r, y);
        ctx.lineTo(x + w - r, y);
        ctx.quadraticCurveTo(x + w, y, x + w, y + r);
        ctx.lineTo(x + w, y + h - r);
        ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
        ctx.lineTo(x + r, y + h);
        ctx.quadraticCurveTo(x, y + h, x, y + h - r);
        ctx.lineTo(x, y + r);
        ctx.quadraticCurveTo(x, y, x + r, y);
        ctx.closePath();
    }

    function bsearch(arr, time) {
        let lo = 0, hi = arr.length;
        while (lo < hi) {
            const mid = (lo + hi) >> 1;
            if (arr[mid].t < time) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }
    function bsearchChords(arr, time) {
        let lo = 0, hi = arr.length;
        while (lo < hi) {
            const mid = (lo + hi) >> 1;
            if (arr[mid].t < time) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    /** One chord note: position + technique fields that affect `drawNote` / unison-bend UI (not sustain). */
    function chordNoteIdentitySegment(n) {
        const bn = Math.round((Number(n.bn) || 0) * 10) / 10;
        const sl = n.sl != null ? n.sl : -1;
        const slu = n.slu != null ? n.slu : -1;
        const b = (v) => (v ? 1 : 0);
        return [
            n.s,
            n.f,
            bn,
            sl,
            slu,
            b(n.ho),
            b(n.po),
            b(n.hm),
            b(n.hp),
            b(n.pm),
            b(n.mt),
            b(n.fhm),
            b(n.tr),
            b(n.ac),
            b(n.tp),
        ].join(':');
    }

    /** Stable id for chord voicing (positions + matching techniques) — repeat outline only when identical. */
    function chordShapeKey(ch) {
        if (!ch.notes || !ch.notes.length) return '';
        return [...ch.notes]
            .sort((a, b) => a.s - b.s)
            .map(chordNoteIdentitySegment)
            .join('|');
    }

    /** Latest event time strictly before `t` (union of note and chord attack times). */
    function previousEventTimeStrictlyBefore(t) {
        const arr = _eventTimesSorted;
        if (!arr.length) return null;
        let lo = 0;
        let hi = arr.length;
        while (lo < hi) {
            const mid = (lo + hi) >> 1;
            if (arr[mid] < t) lo = mid + 1;
            else hi = mid;
        }
        if (lo === 0) return null;
        return arr[lo - 1];
    }

    /**
     * Full chord (gems + label) unless the immediately preceding time slice was only this same voicing
     * including techniques (bend, mutes, slides, etc.) — same as `chordShapeKey`.
     * Requires: no single-note attacks, no other chord shape at that time.
     */
    function chordShowsFullAfterPredecessor(ch) {
        const notesInChord = ch.notes || [];
        if (notesInChord.length < 2) return true;
        const K = chordShapeKey(ch);
        if (!K) return true;
        const tPrev = previousEventTimeStrictlyBefore(ch.t);
        if (tPrev === null) return true;
        const slot = _slotByTime.get(tPrev);
        if (!slot) return true;
        if (slot.hasNotes) return true;
        const { chordShapes } = slot;
        if (chordShapes.size === 1 && chordShapes.has(K)) return false;
        return true;
    }

    function rebuildChordTimeline() {
        _slotByTime.clear();
        const timesSet = new Set();
        for (const n of notes) {
            timesSet.add(n.t);
            const s = _slotByTime.get(n.t) || { hasNotes: false, chordShapes: new Set() };
            s.hasNotes = true;
            _slotByTime.set(n.t, s);
        }
        for (const ch of chords) {
            timesSet.add(ch.t);
            const s = _slotByTime.get(ch.t) || { hasNotes: false, chordShapes: new Set() };
            const key = chordShapeKey(ch);
            if (key) s.chordShapes.add(key);
            _slotByTime.set(ch.t, s);
        }
        _eventTimesSorted = Array.from(timesSet).sort((a, b) => a - b);
    }

    // ── Public API ───────────────────────────────────────────────────────
    return {
        init(canvasEl) {
            canvas = canvasEl;
            ctx = canvas.getContext('2d');
            this.resize();
            window.addEventListener('resize', () => this.resize());
            ready = false;
            notes = []; chords = []; _slotByTime.clear(); _eventTimesSorted = []; beats = []; sections = []; anchors = []; lyrics = []; toneChanges = []; toneBase = "";
        },

        resize() {
            if (!canvas) return;
            const controls = document.getElementById('player-controls');
            const controlsH = controls ? controls.offsetHeight : 50;
            const w = document.documentElement.clientWidth;
            const h = document.documentElement.clientHeight - controlsH;
            canvas.style.width = w + 'px';
            canvas.style.height = h + 'px';
            canvas.width = Math.round(w * _renderScale);
            canvas.height = Math.round(h * _renderScale);
        },

        setRenderScale(scale) {
            _renderScale = Math.max(0.25, Math.min(1, scale));
            localStorage.setItem('renderScale', _renderScale);
            this.resize();
        },

        getRenderScale() { return _renderScale; },

        getInverted() { return _inverted; },
        setInverted(v) { _inverted = v; localStorage.setItem('invertHighway', v); },
        setLefty(on) {
            _lefty = !!on;
            localStorage.setItem('lefty', _lefty ? '1' : '0');
        },

        getLefty() { return _lefty; },

        connect(wsUrl) {
            ws = new WebSocket(wsUrl);
            ws.onclose = () => { console.log('WS closed'); };
            ws.onerror = (e) => { console.error('WS error', e); };
            ws.onmessage = (ev) => {
                const msg = JSON.parse(ev.data);
                if (msg.error) {
                    console.error('Server error:', msg.error);
                    alert('Error: ' + msg.error);
                    return;
                }
                switch (msg.type) {
                    case 'loading':
                        console.log('Loading:', msg.stage);
                        break;
                    case 'song_info':
                        songInfo = msg;
                        document.getElementById('hud-artist').textContent = msg.artist;
                        document.getElementById('hud-title').textContent = msg.title;
                        document.getElementById('hud-arrangement').textContent = msg.arrangement;
                        if (msg.audio_url) {
                            const audio = document.getElementById('audio');
                            if (!audio.src || !audio.src.includes(msg.audio_url.split('/').pop())) {
                                audio.src = msg.audio_url;
                                audio.load();

                                // Show buffering overlay
                                let overlay = document.getElementById('audio-buffer-overlay');
                                if (!overlay) {
                                    overlay = document.createElement('div');
                                    overlay.id = 'audio-buffer-overlay';
                                    overlay.className = 'fixed inset-0 z-[200] flex items-center justify-center bg-black/60 backdrop-blur-sm';
                                    overlay.innerHTML = `
                                        <div class="bg-dark-700 border border-gray-700 rounded-2xl p-6 w-72 text-center shadow-2xl">
                                            <div class="text-sm text-gray-300 mb-3">Loading audio...</div>
                                            <div style="height:6px;background:#1a1a2e;border-radius:999px;overflow:hidden">
                                                <div id="audio-buffer-bar" style="height:100%;background:linear-gradient(90deg,#4080e0,#60a0ff);border-radius:999px;width:0%;transition:width 0.3s"></div>
                                            </div>
                                            <div class="text-xs text-gray-500 mt-2" id="audio-buffer-pct">0%</div>
                                        </div>`;
                                    document.body.appendChild(overlay);
                                }

                                const bar = document.getElementById('audio-buffer-bar');
                                const pct = document.getElementById('audio-buffer-pct');

                                const MIN_BUFFER_SECS = 30;

                                function onProgress() {
                                    if (audio.buffered.length > 0 && audio.duration > 0) {
                                        const loaded = audio.buffered.end(audio.buffered.length - 1);
                                        const p = Math.round((loaded / audio.duration) * 100);
                                        if (bar) bar.style.width = p + '%';
                                        if (pct) pct.textContent = p + '%';
                                        // Dismiss when enough is buffered
                                        if (loaded >= MIN_BUFFER_SECS || loaded >= audio.duration) {
                                            cleanup();
                                        }
                                    }
                                }

                                function cleanup() {
                                    audio.removeEventListener('progress', onProgress);
                                    audio.removeEventListener('canplaythrough', cleanup);
                                    const ol = document.getElementById('audio-buffer-overlay');
                                    if (ol) ol.remove();
                                }

                                audio.addEventListener('progress', onProgress);
                                // Fallback: also dismiss on canplaythrough
                                audio.addEventListener('canplaythrough', cleanup, { once: true });
                            }
                        }
                        // Populate arrangement dropdown
                        if (msg.arrangements) {
                            const sel = document.getElementById('arr-select');
                            sel.innerHTML = msg.arrangements.map(a =>
                                `<option value="${a.index}" ${a.index === msg.arrangement_index ? 'selected' : ''}>${a.name} (${a.notes})</option>`
                            ).join('');
                        }
                        break;
                    case 'beats': beats = msg.data; break;
                    case 'sections': sections = msg.data; break;
                    case 'anchors':
                        anchors = msg.data;
                        if (anchors.length) {
                            displayMaxFret = Math.max(anchors[0].fret + anchors[0].width + 3, 8);
                        }
                        break;
                    case 'chord_templates': chordTemplates = msg.data; break;
                    case 'lyrics': lyrics = msg.data; break;
                    case 'tone_changes': toneChanges = msg.data; toneBase = msg.base || ""; break;
                    case 'notes': notes = notes.concat(msg.data); break;
                    case 'chords': chords = chords.concat(msg.data); break;
                    case 'ready':
                        ready = true;
                        rebuildChordTimeline();
                        console.log(`Highway ready: ${notes.length} notes, ${chords.length} chords`);
                        if (!animFrame) draw();
                        if (highway._onReady) highway._onReady();
                        break;
                }
            };
        },

        setTime(t) { currentTime = t; },

        getBPM(t) {
            // Calculate BPM from beat intervals near time t
            if (beats.length < 2) return 120;
            let closest = 0;
            for (let i = 1; i < beats.length; i++) {
                if (Math.abs(beats[i].time - t) < Math.abs(beats[closest].time - t)) closest = i;
            }
            // Average interval from nearby beats
            const start = Math.max(0, closest - 2);
            const end = Math.min(beats.length - 1, closest + 2);
            let sum = 0, count = 0;
            for (let i = start; i < end; i++) {
                sum += beats[i + 1].time - beats[i].time;
                count++;
            }
            return count > 0 ? 60 / (sum / count) : 120;
        },

        getBeats() { return beats; },
        getTime() { return currentTime; },
        getNotes() { return notes; },
        getChords() { return chords; },
        getToneChanges() { return toneChanges; },
        getToneBase() { return toneBase; },
        getSections() { return sections; },
        getSongInfo() { return songInfo; },
        addDrawHook(fn) { _drawHooks.push(fn); },
        project(tOffset) { return project(tOffset); },
        fretX(fret, scale, w) { return fretX(fret, scale, w); },

        /** Use when drawing text inside the lefty mirror; noop when not lefty. */
        fillTextUnmirrored(text, x, y) { fillTextReadable(text, x, y); },

        toggleLyrics() {
            showLyrics = !showLyrics;
            const btn = document.getElementById('btn-lyrics');
            if (btn) {
                btn.textContent = showLyrics ? 'Lyrics ✓' : 'Lyrics ✗';
                btn.className = showLyrics
                    ? 'px-3 py-1.5 bg-purple-900/40 hover:bg-purple-900/60 rounded-lg text-xs text-purple-300 transition'
                    : 'px-3 py-1.5 bg-dark-600 hover:bg-dark-500 rounded-lg text-xs text-gray-500 transition';
            }
        },

        reconnect(filename, arrangement) {
            // Close old WS but keep audio + animation running
            if (ws) { ws.close(); ws = null; }
            ready = false;
            notes = []; chords = []; _slotByTime.clear(); _eventTimesSorted = []; beats = []; sections = []; anchors = []; lyrics = []; toneChanges = []; toneBase = "";
            const arrParam = arrangement !== undefined ? `?arrangement=${arrangement}` : '';
            // filename might already be encoded from data-play attribute
            const decoded = decodeURIComponent(filename);
            const wsUrl = `${location.protocol === 'https:' ? 'wss:' : 'ws:'}//${location.host}/ws/highway/${decoded}${arrParam}`;
            console.log('reconnect:', wsUrl);
            this.connect(wsUrl);
        },

        stop() {
            if (animFrame) { cancelAnimationFrame(animFrame); animFrame = null; }
            if (ws) { ws.close(); ws = null; }
            ready = false;
            const audio = document.getElementById('audio');
            audio.pause();
            audio.src = '';
            isPlaying = false;
            document.getElementById('btn-play').textContent = '▶ Play';
        },
    };
}
const highway = createHighway();
