/* ============================================================
   蒙版工坊 · 逻辑
   ------------------------------------------------------------
   做什么：把两张图叠在一起，只让「上层图」露出被涂抹到的部分。
   本质 = 给上层图加一张 PS 蒙版；底层图始终完整保留。

   为什么不用「高斯圆点一颗颗盖章」画柔边笔刷：
   柔边笔刷如果沿路径一颗颗盖半透明圆点，同一处会被反复叠加，
   叠加公式是 1-(1-a)^n，盖几十颗之后柔边会被"顶"成硬边 —— 柔度滑块就废了。
   本项目的做法是把一整笔当成**一条路径**，然后：
     1) 用 N 层不同宽度的描边描同一条路径（外层宽而淡、内层窄而浓）；
     2) 第 j 层的透明度反解自目标剖面 A(d)，使叠加后的结果恰好等于
        「沿路径扫过的最大覆盖」，也就是 PS 里一笔刷过去的实际效果。
   这样柔边是真的柔，且完全可复现（不依赖 ctx.filter 的模糊实现）。
   ============================================================ */
(function () {
  'use strict';

  /* ---------------- 常量 ---------------- */

  /* 画布尺寸 = 底层图的原始尺寸，导出也严格是这个尺寸 —— 不存在"换分辨率"。
     下面两个常量**不是**设计上的上限，只是防止浏览器 canvas 分配失败的极端安全网：
     长边 16000 / 总像素 5000 万，常规相机图片（含 5000 万像素）都不会触发；
     一旦触发会按比例下采样并明确告知用户。 */
  const MAX_DOC_SIDE = 16000;
  const MAX_DOC_PIXELS = 50e6;

  const MAX_UNDO = 80;                // 撤销步数上限
  const DEFAULT_DOC = { w: 1920, h: 1080 };
  const CHECKER_CELL = 8;             // 透明棋盘格边长（CSS px）

  /* ---------------- 工具函数 ---------------- */
  const $ = (id) => document.getElementById(id);
  const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
  const smoothstep = (u) => u * u * (3 - 2 * u);

  /* ---------------- DOM ---------------- */
  const wrap = $('canvasWrap');
  const viewCanvas = $('viewCanvas');
  const viewCtx = viewCanvas.getContext('2d');
  const brushCursor = $('brushCursor');
  const bcCore = $('bcCore');
  const stageHint = $('stageHint');
  const toastEl = $('toast');
  const dragOverlay = $('dragDropOverlay');
  const zoomValEl = $('zoomVal');

  /* ---------------- 离屏画布（均按视口分辨率，供显示合成） ---------------- */
  const vmask = document.createElement('canvas');    const vmaskCtx = vmask.getContext('2d');
  const vbuf = document.createElement('canvas');     const vbufCtx = vbuf.getContext('2d');
  const vstroke = document.createElement('canvas');  const vstrokeCtx = vstroke.getContext('2d');
  const vtint = document.createElement('canvas');    const vtintCtx = vtint.getContext('2d');

  /* 蒙版本体：**按画布原始分辨率**存，保证导出时笔迹细节不糊 */
  let mask = null;
  let maskCtx = null;

  /* ---------------- 状态 ---------------- */
  const state = {
    base: null,           // { img, name }
    top: null,            // { img, name }
    doc: { ...DEFAULT_DOC },
    topFit: 'cover',      // cover | contain | stretch
    tool: 'paint',        // paint | erase
    /* softness = 「边缘柔度」：0 = 硬边（实心圆），1 = 从圆心一路羽化到边缘。
       笔刷数学层用的是 hardness（1 = 硬边），转换只在一处（passesFor）发生。 */
    brush: { size: 240, softness: 0.6, opacity: 1 },
    showMask: false,
    strokes: [],          // 已提交的笔画（矢量，用于撤销与重建）
    history: [],          // 撤销栈：存 strokes 的浅拷贝
    redo: [],             // 重做栈
    stroke: null,         // 正在画的那一笔
    zoom: 1,              // 相对「适应窗口」的倍率
    pan: { x: 0, y: 0 },  // 相对居中位置的平移（CSS px）
    spaceDown: false,
    panning: false,
  };

  let wrapW = 0, wrapH = 0, dpr = 1, viewW = 0, viewH = 0;
  /* 容器内容盒相对边框盒的内缩量（= 1px 边框宽）。指针换算一律以内容盒为基准。 */
  let borderL = 0, borderT = 0;
  let checkerPat = null;
  let panStart = null;
  let rafId = 0;

  /* ============================================================
     笔刷：把 (大小, 柔度, 不透明度) 解成一组描边层
     ------------------------------------------------------------
     目标剖面 A(d)：d <= h·R 处为 o（实心），随后平滑过渡到 d = R 处为 0。
     第 j 层的累计透过率 C_j = 1 - A_j，则该层自身的 alpha 为
        a_j = 1 - C_j / C_{j-1}
     如此逐层叠加后，最终 alpha 恰好等于 A_j。erase 模式用 destination-out
     走同一套 alpha，擦除量同样是 A_j。
     ============================================================ */
  function brushPasses(size, hardness, opacity) {
    const R = Math.max(0.5, size / 2);
    const h = clamp(hardness, 0, 1);
    const o = clamp(opacity, 0.004, 1);

    // 硬边笔刷：单层实心圆即可
    if (h >= 0.995) return [{ w: R, a: o }];

    // 柔边越柔，需要的层数越多（层数 = 羽化过渡的阶梯数）
    const N = clamp(Math.round(28 * (1 - h)), 2, 28);
    const dAt = (j) => R * (1 - (1 - h) * (j / N));   // d_0 = R（外沿）→ d_N = h·R（硬芯边）

    const passes = [];
    let prevC = 1;   // C_0 = 1（A_0 = 0）
    for (let j = 1; j <= N; j++) {
      const hi = dAt(j - 1);          // 本层半宽（= 本层外沿）
      const lo = dAt(j);
      const mid = (lo + hi) / 2;
      const u = clamp((R - mid) / (R - h * R), 0, 1);  // 0 = 最外沿，1 = 硬芯边
      const A = o * smoothstep(u);
      const C = 1 - A;
      let a = 1 - C / prevC;
      a = clamp(a, 0, 1);
      prevC = C;
      if (a > 0.002) passes.push({ w: hi, a });
    }
    if (!passes.length) passes.push({ w: R, a: o });
    return passes;
  }

  /* 对外统一用「柔度」这一个概念，避免标签和数值方向打架：
       softness 0 = 硬边，softness 1 = 完全羽化
     内部数学层的 hardness 恰好相反（1 = 硬边），翻转只在这一个地方发生。 */
  function passesFor(size, softness, opacity) {
    return brushPasses(size, 1 - clamp(softness, 0, 1), opacity);
  }

  /* 把一笔画进某个上下文：mode='paint' 叠加、'erase' 擦除 */
  function strokePathInto(ctx, pts, passes, mode) {
    if (!pts || !pts.length) return;
    ctx.save();
    ctx.lineJoin = 'round';
    ctx.lineCap = 'round';
    ctx.strokeStyle = '#ffffff';
    for (let i = 0; i < passes.length; i++) {
      const p = passes[i];
      ctx.globalAlpha = p.a;
      ctx.globalCompositeOperation = mode === 'erase' ? 'destination-out' : 'source-over';
      ctx.lineWidth = p.w * 2;
      ctx.beginPath();
      if (pts.length === 1) {
        // 单点 = 一个圆点：用一条极短线段借 round lineCap 生成
        ctx.moveTo(pts[0].x, pts[0].y);
        ctx.lineTo(pts[0].x + 0.001, pts[0].y + 0.001);
      } else {
        ctx.moveTo(pts[0].x, pts[0].y);
        for (let k = 1; k < pts.length; k++) ctx.lineTo(pts[k].x, pts[k].y);
      }
      ctx.stroke();
    }
    ctx.restore();
  }

  /* ============================================================
     画布尺寸 / 蒙版管理
     ============================================================ */
  /* 画布尺寸默认**就是图片的原始尺寸**（导出即此尺寸，不做任何缩放）。
     只有超过 canvas 能安全分配的极端尺寸时才按比例下采样，并返回 scaled 标记，
     由调用方告知用户。 */
  function fitDocSize(w, h) {
    w = Math.max(1, Math.round(w));
    h = Math.max(1, Math.round(h));
    let s = 1;
    const side = Math.max(w, h);
    if (side > MAX_DOC_SIDE) s = Math.min(s, MAX_DOC_SIDE / side);
    const pixels = w * h;
    if (pixels > MAX_DOC_PIXELS) s = Math.min(s, Math.sqrt(MAX_DOC_PIXELS / pixels));
    if (s >= 1) return { w, h, scaled: false };
    return { w: Math.max(1, Math.round(w * s)), h: Math.max(1, Math.round(h * s)), scaled: true };
  }

  /* 改变画布尺寸：等比缩放已有笔迹，重建蒙版（不丢用户的涂抹） */
  function setDoc(w, h) {
    w = Math.max(1, Math.round(w));
    h = Math.max(1, Math.round(h));
    if (w === state.doc.w && h === state.doc.h) return false;

    const sx = w / state.doc.w;
    const sy = h / state.doc.h;
    const ss = (sx + sy) / 2;
    for (const st of state.strokes) {
      st.pts = st.pts.map((p) => ({ x: p.x * sx, y: p.y * sy }));
      st.size *= ss;
    }
    if (state.stroke) {
      state.stroke.pts = state.stroke.pts.map((p) => ({ x: p.x * sx, y: p.y * sy }));
      state.stroke.size *= ss;
    }

    state.doc = { w, h };
    mask = document.createElement('canvas');
    mask.width = w;
    mask.height = h;
    maskCtx = mask.getContext('2d');

    state.zoom = 1;
    state.pan.x = 0;
    state.pan.y = 0;

    rebuild();
    updateExportInfo();
    return true;
  }

  function clearMaskCanvas() {
    maskCtx.setTransform(1, 0, 0, 1, 0, 0);
    maskCtx.globalAlpha = 1;
    maskCtx.globalCompositeOperation = 'source-over';
    maskCtx.clearRect(0, 0, state.doc.w, state.doc.h);
  }

  /* 依据 strokes 全量重建蒙版（撤销 / 重做 / 改尺寸时用） */
  function rebuild() {
    if (!maskCtx) return;
    clearMaskCanvas();
    for (const st of state.strokes) {
      strokePathInto(maskCtx, st.pts, passesFor(st.size, st.softness, st.opacity), st.mode);
    }
    renderView();
    updateUndoUI();
    updateStageHint();
  }

  /* 单笔增量提交（比全量重建快得多，落笔时用） */
  function commitStroke(st) {
    strokePathInto(maskCtx, st.pts, passesFor(st.size, st.softness, st.opacity), st.mode);
  }

  /* ============================================================
     视图变换：缩放 + 平移
     ============================================================ */
  function baseFitScale() {
    const pad = 32;
    const aw = Math.max(40, wrapW - pad * 2);
    const ah = Math.max(40, wrapH - pad * 2);
    return Math.min(aw / state.doc.w, ah / state.doc.h);
  }
  function viewScale() { return baseFitScale() * state.zoom; }
  function viewOrigin() {
    const s = viewScale();
    return {
      s,
      ox: (wrapW - state.doc.w * s) / 2 + state.pan.x,
      oy: (wrapH - state.doc.h * s) / 2 + state.pan.y,
    };
  }

  /* 以 (ax, ay)（容器内 CSS 坐标）为锚点缩放到 zoom 倍率 */
  function setZoom(z, ax, ay) {
    const before = viewOrigin();
    const a = { x: ax == null ? wrapW / 2 : ax, y: ay == null ? wrapH / 2 : ay };
    const dp = { x: (a.x - before.ox) / before.s, y: (a.y - before.oy) / before.s };
    state.zoom = clamp(z, 0.05, 40);
    const s2 = viewScale();
    state.pan.x = (a.x - dp.x * s2) - (wrapW - state.doc.w * s2) / 2;
    state.pan.y = (a.y - dp.y * s2) - (wrapH - state.doc.h * s2) / 2;
    renderView();
    updateZoomUI();
  }

  function resetView() {
    state.zoom = 1;
    state.pan.x = 0;
    state.pan.y = 0;
    renderView();
    updateZoomUI();
  }

  /* ============================================================
     渲染
     ============================================================ */
  function drawFit(ctx, img, mode, W, H) {
    const iw = img.naturalWidth || img.width;
    const ih = img.naturalHeight || img.height;
    if (mode === 'stretch') { ctx.drawImage(img, 0, 0, W, H); return; }
    const s = mode === 'contain' ? Math.min(W / iw, H / ih) : Math.max(W / iw, H / ih);
    const w = iw * s, h = ih * s;
    ctx.drawImage(img, (W - w) / 2, (H - h) / 2, w, h);
  }

  function checkerPattern() {
    if (checkerPat) return checkerPat;
    const cell = Math.max(2, Math.round(CHECKER_CELL * dpr));
    const c = document.createElement('canvas');
    c.width = cell * 2;
    c.height = cell * 2;
    const x = c.getContext('2d');
    x.fillStyle = '#141414';
    x.fillRect(0, 0, c.width, c.height);
    x.fillStyle = '#1f1f1f';
    x.fillRect(0, 0, cell, cell);
    x.fillRect(cell, cell, cell, cell);
    checkerPat = viewCtx.createPattern(c, 'repeat');
    return checkerPat;
  }

  function renderView() {
    if (!viewW || !viewH) return;
    const { s, ox, oy } = viewOrigin();
    const T = [dpr * s, 0, 0, dpr * s, dpr * ox, dpr * oy];
    const live = state.stroke && state.stroke.pts.length > 0;

    /* 1) 当前笔迹（视口分辨率） */
    vstrokeCtx.setTransform(1, 0, 0, 1, 0, 0);
    vstrokeCtx.globalAlpha = 1;
    vstrokeCtx.globalCompositeOperation = 'source-over';
    vstrokeCtx.clearRect(0, 0, viewW, viewH);
    if (live) {
      vstrokeCtx.setTransform(T[0], T[1], T[2], T[3], T[4], T[5]);
      strokePathInto(
        vstrokeCtx, state.stroke.pts,
        passesFor(state.stroke.size, state.stroke.softness, state.stroke.opacity),
        'paint'   // 笔迹缓冲恒为正值，擦除在下一步用 destination-out 施加
      );
    }

    /* 2) 有效蒙版 = 已提交蒙版 ⧺ 当前笔迹 */
    vmaskCtx.setTransform(1, 0, 0, 1, 0, 0);
    vmaskCtx.globalAlpha = 1;
    vmaskCtx.globalCompositeOperation = 'source-over';
    vmaskCtx.clearRect(0, 0, viewW, viewH);
    vmaskCtx.setTransform(T[0], T[1], T[2], T[3], T[4], T[5]);
    vmaskCtx.drawImage(mask, 0, 0);
    if (live) {
      vmaskCtx.setTransform(1, 0, 0, 1, 0, 0);
      vmaskCtx.globalCompositeOperation = state.stroke.mode === 'erase' ? 'destination-out' : 'source-over';
      vmaskCtx.drawImage(vstroke, 0, 0);
      vmaskCtx.globalCompositeOperation = 'source-over';
    }

    /* 3) 主画布 */
    viewCtx.setTransform(1, 0, 0, 1, 0, 0);
    viewCtx.globalAlpha = 1;
    viewCtx.globalCompositeOperation = 'source-over';
    viewCtx.clearRect(0, 0, viewW, viewH);

    // 画布范围的透明棋盘格（屏幕固定，不随缩放走）
    viewCtx.fillStyle = checkerPattern();
    viewCtx.fillRect(ox * dpr, oy * dpr, state.doc.w * s * dpr, state.doc.h * s * dpr);

    viewCtx.setTransform(T[0], T[1], T[2], T[3], T[4], T[5]);
    if (state.base) drawFit(viewCtx, state.base.img, 'cover', state.doc.w, state.doc.h);

    if (state.top) {
      // 上层图先按适配方式铺好，再用蒙版做 destination-in —— 只留涂抹到的部分
      vbufCtx.setTransform(1, 0, 0, 1, 0, 0);
      vbufCtx.globalAlpha = 1;
      vbufCtx.globalCompositeOperation = 'source-over';
      vbufCtx.clearRect(0, 0, viewW, viewH);
      vbufCtx.setTransform(T[0], T[1], T[2], T[3], T[4], T[5]);
      drawFit(vbufCtx, state.top.img, state.topFit, state.doc.w, state.doc.h);
      vbufCtx.setTransform(1, 0, 0, 1, 0, 0);
      vbufCtx.globalCompositeOperation = 'destination-in';
      vbufCtx.drawImage(vmask, 0, 0);
      vbufCtx.globalCompositeOperation = 'source-over';

      viewCtx.setTransform(1, 0, 0, 1, 0, 0);
      viewCtx.drawImage(vbuf, 0, 0);
    }

    /* 4) 蒙版预览：把有效蒙版染成红色叠上去 */
    if (state.showMask) {
      vtintCtx.setTransform(1, 0, 0, 1, 0, 0);
      vtintCtx.globalAlpha = 1;
      vtintCtx.globalCompositeOperation = 'source-over';
      vtintCtx.clearRect(0, 0, viewW, viewH);
      vtintCtx.drawImage(vmask, 0, 0);
      vtintCtx.globalCompositeOperation = 'source-in';
      vtintCtx.fillStyle = 'rgba(255, 64, 64, 0.5)';
      vtintCtx.fillRect(0, 0, viewW, viewH);
      vtintCtx.globalCompositeOperation = 'source-over';

      viewCtx.setTransform(1, 0, 0, 1, 0, 0);
      viewCtx.drawImage(vtint, 0, 0);
    }
  }

  function scheduleRender() {
    if (rafId) return;
    rafId = requestAnimationFrame(() => { rafId = 0; renderView(); });
  }

  /* ============================================================
     布局
     ============================================================ */
  function layout() {
    /* 必须用**内容盒**而不是边框盒：
       .canvas-wrap 有 1px 边框，canvas 是 width:100% 铺在内容盒里的，
       用边框盒会同时造成两个问题 ——
         a) 后备像素比 CSS 尺寸宽 2px，图像被轻微重采样（发虚）；
         b) 所有指针坐标相对内容盒整体偏 1px（画笔圈与笔迹都对不齐指针）。 */
    const cs = getComputedStyle(wrap);
    borderL = parseFloat(cs.borderLeftWidth) || 0;
    borderT = parseFloat(cs.borderTopWidth) || 0;
    wrapW = Math.max(1, wrap.clientWidth);
    wrapH = Math.max(1, wrap.clientHeight);
    const ndpr = Math.min(window.devicePixelRatio || 1, 2);
    if (ndpr !== dpr) { dpr = ndpr; checkerPat = null; }

    viewW = Math.max(1, Math.round(wrapW * dpr));
    viewH = Math.max(1, Math.round(wrapH * dpr));
    viewCanvas.width = viewW;
    viewCanvas.height = viewH;
    for (const c of [vmask, vbuf, vstroke, vtint]) { c.width = viewW; c.height = viewH; }

    renderView();
    updateZoomUI();
  }

  /* ============================================================
     坐标换算
     ============================================================ */
  function toDoc(e) {
    const r = wrap.getBoundingClientRect();
    const { s, ox, oy } = viewOrigin();
    return {
      x: (e.clientX - r.left - borderL - ox) / s,
      y: (e.clientY - r.top - borderT - oy) / s,
    };
  }

  /* ============================================================
     指针交互
     ============================================================ */
  function canPaint() { return !!state.top; }

  function startStroke(e) {
    const p = toDoc(e);
    state.stroke = {
      pts: [{ x: p.x, y: p.y }],
      size: state.brush.size,
      softness: state.brush.softness,
      opacity: state.brush.opacity,
      mode: state.tool,
    };
    try { wrap.setPointerCapture(e.pointerId); } catch (_) {}
    renderView();
    updateStageHint();
  }

  function extendStroke(e) {
    const st = state.stroke;
    if (!st) return;
    const minDist = Math.max(0.75, st.size * 0.035);
    let moved = false;
    // 用 coalesced 事件把两次 rAF 之间漏掉的采样点补回来，快速拖动也顺滑
    const evs = typeof e.getCoalescedEvents === 'function' ? e.getCoalescedEvents() : null;
    const list = evs && evs.length ? evs : [e];
    for (const ev of list) {
      const p = toDoc(ev);
      const last = st.pts[st.pts.length - 1];
      const d = Math.hypot(p.x - last.x, p.y - last.y);
      if (d < minDist) continue;
      st.pts.push({ x: p.x, y: p.y });
      moved = true;
    }
    if (moved) scheduleRender();
  }

  function endStroke() {
    const st = state.stroke;
    state.stroke = null;
    if (st && st.pts.length) {
      state.history.push(state.strokes.slice());
      if (state.history.length > MAX_UNDO) state.history.shift();
      state.redo.length = 0;
      state.strokes.push(st);
      commitStroke(st);
    }
    renderView();
    updateUndoUI();
    updateStageHint();
  }

  function startPan(e) {
    state.panning = true;
    panStart = { x: e.clientX, y: e.clientY, px: state.pan.x, py: state.pan.y };
    try { wrap.setPointerCapture(e.pointerId); } catch (_) {}
    wrap.classList.add('is-panning');
    hideBrushCursor();
  }

  function movePan(e) {
    if (!panStart) return;
    state.pan.x = panStart.px + (e.clientX - panStart.x);
    state.pan.y = panStart.py + (e.clientY - panStart.y);
    renderView();
  }

  function endPan() {
    state.panning = false;
    panStart = null;
    wrap.classList.remove('is-panning');
  }

  wrap.addEventListener('contextmenu', (e) => e.preventDefault());

  wrap.addEventListener('pointerdown', (e) => {
    if (e.button === 1 || e.button === 2 || state.spaceDown) {
      e.preventDefault();
      startPan(e);
      return;
    }
    if (e.button !== 0) return;
    if (!canPaint()) {
      toast(state.top ? '' : '请先导入「上层图」，蒙版才有作用对象');
      return;
    }
    e.preventDefault();
    positionBrushCursor(e.clientX, e.clientY);
    startStroke(e);
  });

  wrap.addEventListener('pointermove', (e) => {
    lastPointer = e;
    if (state.panning) { movePan(e); return; }
    /* 画笔圈必须**先于**所有分支更新：涂抹过程中它同样要跟着指针走。
       之前这里写成了 `if (state.stroke) { extendStroke(e); return; }`，
       于是按住拖动的全过程圈圈一次都不刷新，冻在落笔点；
       再叠加 cursor:none，体感就是"光标没了、圈也不动"。 */
    positionBrushCursor(e.clientX, e.clientY);
    if (state.stroke) extendStroke(e);
  });

  function onPointerUp(e) {
    if (state.panning) { endPan(); return; }
    if (state.stroke) { endStroke(); }
  }
  wrap.addEventListener('pointerup', onPointerUp);
  wrap.addEventListener('pointercancel', onPointerUp);

  wrap.addEventListener('pointerleave', () => {
    // 涂抹中不藏圈：指针被 setPointerCapture 抓住时可能划过边界，圈要跟着走
    if (!state.panning && !state.stroke) hideBrushCursor();
  });

  wrap.addEventListener('wheel', (e) => {
    e.preventDefault();
    const r = wrap.getBoundingClientRect();
    const factor = Math.exp(-e.deltaY * 0.0016);
    setZoom(state.zoom * factor, e.clientX - r.left - borderL, e.clientY - r.top - borderT);
    positionBrushCursor(e.clientX, e.clientY);
  }, { passive: false });

  /* ---------------- 画笔光标 ----------------
     位置按**指针坐标**实时计算，与渲染循环解耦 —— 拖动时必须跟手。
     外圈 = 笔刷直径；内圈虚线 = 硬芯（柔度 0% 时硬芯=整圈，柔度 100% 时没有硬芯）。 */
  function positionBrushCursor(clientX, clientY) {
    if (!canPaint() || state.panning || state.spaceDown) { hideBrushCursor(); return; }
    const r = wrap.getBoundingClientRect();
    const left = r.left + borderL;     // 内容盒原点：canvas 与画笔圈都铺在内容盒里
    const top = r.top + borderT;
    // 涂抹中即使指针划出画布也照样跟随（外层 overflow:hidden 会自然裁掉越界部分）
    if (!state.stroke &&
        (clientX < left || clientX > left + wrapW || clientY < top || clientY > top + wrapH)) {
      hideBrushCursor();
      return;
    }
    const s = viewScale();
    const d = Math.max(6, state.brush.size * s);
    const core = d * (1 - state.brush.softness);

    brushCursor.hidden = false;
    brushCursor.style.width = d + 'px';
    brushCursor.style.height = d + 'px';
    brushCursor.style.transform =
      'translate(' + (clientX - left) + 'px,' + (clientY - top) + 'px) translate(-50%,-50%)';
    /* 内圈是 border-box 的 1px 虚线圆环：宽度给 0 会被边框撑成 2px，
       所以硬芯小于可见阈值时直接隐藏，而不是留一个假的小圆点。 */
    if (core < 2.5) {
      bcCore.hidden = true;
    } else {
      bcCore.hidden = false;
      bcCore.style.width = core + 'px';
      bcCore.style.height = core + 'px';
    }
    wrap.classList.add('is-brush');
  }

  function hideBrushCursor() {
    brushCursor.hidden = true;
    wrap.classList.remove('is-brush');
  }

  /* ============================================================
     撤销 / 重做
     ============================================================ */
  function undo() {
    if (!state.history.length) return;
    state.redo.push(state.strokes.slice());
    state.strokes = state.history.pop();
    rebuild();
  }
  function redo() {
    if (!state.redo.length) return;
    state.history.push(state.strokes.slice());
    state.strokes = state.redo.pop();
    rebuild();
  }
  function updateUndoUI() {
    $('btnUndo').disabled = state.history.length === 0;
    $('btnRedo').disabled = state.redo.length === 0;
  }

  /* ============================================================
     图片导入
     ============================================================ */
  /* 读出图片，同时把原始 MIME 类型带出来 —— 导出格式要严格跟随底图 */
  function readImage(file) {
    return new Promise((resolve, reject) => {
      if (!file || !/^image\//.test(file.type || '')) { reject(new Error('不是图片文件')); return; }
      const fr = new FileReader();
      fr.onload = () => {
        const img = new Image();
        img.onload = () => resolve({ img, mime: file.type || 'image/png' });
        img.onerror = () => reject(new Error('图片解码失败'));
        // 必须走 dataURL：blob: 在 file:// 页面下是不透明源，会把画布污染、导出失败
        img.src = fr.result;
      };
      fr.onerror = () => reject(new Error('文件读取失败'));
      fr.readAsDataURL(file);
    });
  }

  async function importImage(file, role) {
    try {
      const { img, mime } = await readImage(file);
      const nw = img.naturalWidth || img.width;
      const nh = img.naturalHeight || img.height;
      const label = role === 'base' ? '底层图' : '上层图';

      if (role === 'base') state.base = { img, name: file.name, mime };
      else state.top = { img, name: file.name, mime };

      // 画布尺寸由底层图决定；只有上层图时，就用上层图的尺寸
      const definesDoc = role === 'base' || !state.base;
      let scaled = false;
      if (definesDoc) {
        const d = fitDocSize(nw, nh);
        scaled = d.scaled;
        if (!setDoc(d.w, d.h)) renderView();   // 尺寸没变则直接重绘
      } else {
        renderView();
      }

      updateLayerUI();
      updateStageHint();
      updateExportInfo();
      toast(scaled
        ? '图片尺寸过大（' + nw + ' × ' + nh + '），已按比例缩到 ' + state.doc.w + ' × ' + state.doc.h
        : label + '已导入 · ' + nw + ' × ' + nh);
    } catch (err) {
      toast(err.message || '导入失败');
    }
  }

  /* ============================================================
     导出
     ============================================================ */
  /* ============================================================
     导出
     ------------------------------------------------------------
     没有分辨率选项、也没有格式选项 —— **严格跟随底层图**：
       底层图多大就导出多大（不做超分、也不做压缩）；
       底层图是什么格式就导出什么格式。
     上层图只是被蒙版控制的那一层，不参与决定输出规格。
     ============================================================ */
  const EXPORT_TYPES = {
    'image/png':  { ext: 'png',  label: 'PNG',  quality: null },
    'image/jpeg': { ext: 'jpg',  label: 'JPG',  quality: 0.95 },
    'image/webp': { ext: 'webp', label: 'WEBP', quality: 0.95 },
  };

  /* 决定输出规格的"基准图"：有底层图就是底层图；只有上层图时退而用它 */
  function specSource() { return state.base || state.top || null; }

  function exportSpec() {
    const src = specSource();
    // 浏览器画布只能编码 png/jpeg/webp，其它格式（gif/bmp/avif/svg…）一律回退 PNG
    const mime = (src && src.mime && EXPORT_TYPES[src.mime]) ? src.mime : 'image/png';
    const t = EXPORT_TYPES[mime];
    return { w: state.doc.w, h: state.doc.h, mime, ext: t.ext, label: t.label, quality: t.quality };
  }

  function updateExportInfo() {
    const el = $('exportInfo');
    if (!specSource()) { el.textContent = '—'; el.removeAttribute('title'); return; }
    const s = exportSpec();
    el.textContent = s.w + ' × ' + s.h + ' · ' + s.label;
    el.title = '导出尺寸与格式严格跟随' + (state.base ? '底层图' : '上层图');
  }

  function exportImage() {
    if (!specSource()) { toast('还没有可导出的内容'); return; }
    const btn = $('btnExport');
    btn.disabled = true;
    const spec = exportSpec();
    const { w, h } = spec;

    try {
      const out = document.createElement('canvas');
      out.width = w;
      out.height = h;
      const x = out.getContext('2d');

      // 先铺底层图（完整保留，且就是它的原始尺寸，1:1 不缩放）
      if (state.base) drawFit(x, state.base.img, 'cover', w, h);

      if (state.top) {
        // 上层图在输出尺寸下重画一遍，再套**原始分辨率**的蒙版 —— 边缘质量不损失
        const t = document.createElement('canvas');
        t.width = w;
        t.height = h;
        const tx = t.getContext('2d');
        drawFit(tx, state.top.img, state.topFit, w, h);
        tx.globalCompositeOperation = 'destination-in';
        tx.drawImage(mask, 0, 0, w, h);
        tx.globalCompositeOperation = 'source-over';
        x.drawImage(t, 0, 0);
      }

      const finish = (blob) => {
        btn.disabled = false;
        if (!blob) { toast('导出失败'); return; }
        const d = new Date();
        const pad = (n) => String(n).padStart(2, '0');
        const name = '蒙版合成_' + d.getFullYear() + pad(d.getMonth() + 1) + pad(d.getDate())
          + '_' + pad(d.getHours()) + pad(d.getMinutes()) + pad(d.getSeconds()) + '.' + spec.ext;
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = name;
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        setTimeout(() => URL.revokeObjectURL(url), 2000);
        toast('已导出 ' + w + ' × ' + h + ' ' + spec.label);
      };

      if (spec.quality == null) out.toBlob(finish, spec.mime);
      else out.toBlob(finish, spec.mime, spec.quality);
    } catch (err) {
      btn.disabled = false;
      toast('导出失败：' + (err && err.message ? err.message : err));
    }
  }

  /* ============================================================
     UI 同步
     ============================================================ */
  let toastTimer = 0;
  function toast(msg) {
    if (!msg) return;
    toastEl.textContent = msg;
    toastEl.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => toastEl.classList.remove('show'), 1900);
  }

  function updateZoomUI() {
    zoomValEl.textContent = Math.round(viewScale() * 100) + '%';
  }

  function updateLayerUI() {
    const tn = $('topName'), bn = $('baseName');
    if (state.top) {
      tn.textContent = state.top.name;
      tn.classList.add('is-set');
      $('btnClearTop').hidden = false;
      $('btnPickTop').textContent = '更换上层图';
    } else {
      tn.textContent = '未导入';
      tn.classList.remove('is-set');
      $('btnClearTop').hidden = true;
      $('btnPickTop').textContent = '导入上层图';
    }
    if (state.base) {
      bn.textContent = state.base.name;
      bn.classList.add('is-set');
      $('btnClearBase').hidden = false;
      $('btnPickBase').textContent = '更换底层图';
    } else {
      bn.textContent = '未导入';
      bn.classList.remove('is-set');
      $('btnClearBase').hidden = true;
      $('btnPickBase').textContent = '导入底层图';
    }
  }

  function updateStageHint() {
    const empty = !state.base && !state.top;
    const tipMask = !empty && state.top && state.strokes.length === 0 && !state.stroke;
    if (empty) {
      stageHint.textContent = '拖入或导入两张图片开始合成';
      stageHint.hidden = false;
    } else if (tipMask) {
      stageHint.textContent = '用画笔在图上涂抹，露出上层图';
      stageHint.hidden = false;
    } else {
      stageHint.hidden = true;
    }
  }

  function updateBrushUI() {
    $('sizeSlider').value = state.brush.size;
    $('sizeVal').textContent = state.brush.size + ' px';
    $('softSlider').value = Math.round(state.brush.softness * 100);
    $('softVal').textContent = Math.round(state.brush.softness * 100) + '%';
    $('opacitySlider').value = Math.round(state.brush.opacity * 100);
    $('opacityVal').textContent = Math.round(state.brush.opacity * 100) + '%';
  }

  function setTool(tool) {
    state.tool = tool;
    document.querySelectorAll('#toolToggle .toggle-btn').forEach((b) => {
      b.classList.toggle('active', b.dataset.tool === tool);
    });
  }

  /* ============================================================
     事件绑定
     ============================================================ */
  function bind() {
    // 分组折叠
    document.querySelectorAll('.ctrl-group-head').forEach((head) => {
      head.addEventListener('click', () => head.parentElement.classList.toggle('is-collapsed'));
    });

    // 工具切换
    document.querySelectorAll('#toolToggle .toggle-btn').forEach((b) => {
      b.addEventListener('click', () => setTool(b.dataset.tool));
    });

    // 图层导入 / 移除 / 交换
    $('btnPickTop').addEventListener('click', () => $('fileTopInput').click());
    $('btnPickBase').addEventListener('click', () => $('fileBaseInput').click());
    $('fileTopInput').addEventListener('change', (e) => {
      const f = e.target.files && e.target.files[0];
      if (f) importImage(f, 'top');
      e.target.value = '';
    });
    $('fileBaseInput').addEventListener('change', (e) => {
      const f = e.target.files && e.target.files[0];
      if (f) importImage(f, 'base');
      e.target.value = '';
    });
    $('btnClearTop').addEventListener('click', () => {
      state.top = null;
      updateLayerUI();
      renderView();
      updateStageHint();
      updateExportInfo();     // 只剩底层图时，导出规格可能不变；没有图时变成 "—"
    });
    $('btnClearBase').addEventListener('click', () => {
      state.base = null;
      if (state.top) {
        const d = fitDocSize(state.top.img.naturalWidth, state.top.img.naturalHeight);
        setDoc(d.w, d.h);
      }
      updateLayerUI();
      renderView();
      updateStageHint();
      updateExportInfo();     // 基准图从底层换成上层，格式可能变
    });
    $('btnSwap').addEventListener('click', () => {
      if (!state.base || !state.top) { toast('需要同时有底层图和上层图'); return; }
      const b = state.base;
      state.base = state.top;
      state.top = b;
      const d = fitDocSize(state.base.img.naturalWidth, state.base.img.naturalHeight);
      setDoc(d.w, d.h);
      updateLayerUI();
      renderView();
      updateExportInfo();     // 交换后基准图变成原来的上层图
      toast('已交换上下层');
    });

    // 上层图适配方式
    document.querySelectorAll('#fitToggle .toggle-btn').forEach((b) => {
      b.addEventListener('click', () => {
        state.topFit = b.dataset.fit;
        document.querySelectorAll('#fitToggle .toggle-btn').forEach((x) =>
          x.classList.toggle('active', x === b));
        renderView();
      });
    });

    // 画笔参数
    $('sizeSlider').addEventListener('input', (e) => {
      state.brush.size = Number(e.target.value);
      updateBrushUI();
      refreshBrushCursor();          // 圈的外径要跟着变
    });
    $('softSlider').addEventListener('input', (e) => {
      state.brush.softness = Number(e.target.value) / 100;
      updateBrushUI();
      refreshBrushCursor();          // 圈的内径（硬芯）要跟着变
    });
    $('opacitySlider').addEventListener('input', (e) => {
      state.brush.opacity = Number(e.target.value) / 100;
      updateBrushUI();
    });
    $('btnClearMask').addEventListener('click', () => {
      if (!state.strokes.length) { toast('蒙版本来就是空的'); return; }
      state.history.push(state.strokes.slice());
      if (state.history.length > MAX_UNDO) state.history.shift();
      state.redo.length = 0;
      state.strokes = [];
      rebuild();
      toast('蒙版已清空');
    });

    // 视图
    $('showMaskToggle').addEventListener('change', (e) => {
      state.showMask = e.target.checked;
      renderView();
    });
    $('btnZoomIn').addEventListener('click', () => setZoom(state.zoom * 1.25));
    $('btnZoomOut').addEventListener('click', () => setZoom(state.zoom / 1.25));
    $('btnFit').addEventListener('click', resetView);
    $('btnActual').addEventListener('click', () => setZoom(1 / baseFitScale()));

    // 撤销 / 重做
    $('btnUndo').addEventListener('click', undo);
    $('btnRedo').addEventListener('click', redo);

    // 导出：没有任何选项，规格严格跟随底层图
    $('btnExport').addEventListener('click', exportImage);

    /* ---------------- 拖放导入 ---------------- */
    let dragDepth = 0;
    window.addEventListener('dragenter', (e) => {
      if (!e.dataTransfer || !Array.from(e.dataTransfer.types || []).includes('Files')) return;
      e.preventDefault();
      dragDepth++;
      dragOverlay.classList.add('active');
    });
    window.addEventListener('dragover', (e) => {
      if (!e.dataTransfer || !Array.from(e.dataTransfer.types || []).includes('Files')) return;
      e.preventDefault();
      e.dataTransfer.dropEffect = 'copy';
    });
    window.addEventListener('dragleave', (e) => {
      if (!e.dataTransfer || !Array.from(e.dataTransfer.types || []).includes('Files')) return;
      dragDepth = Math.max(0, dragDepth - 1);
      if (!dragDepth) dragOverlay.classList.remove('active');
    });
    window.addEventListener('drop', (e) => {
      e.preventDefault();
      dragDepth = 0;
      dragOverlay.classList.remove('active');
      const files = Array.from(e.dataTransfer ? e.dataTransfer.files : []).filter((f) => /^image\//.test(f.type || ''));
      if (!files.length) return;
      // 第一张当底层（先看见底图），其余当上层；按住 Shift 强制当底层
      const forceBase = e.shiftKey;
      if (!state.base || forceBase) {
        importImage(files[0], 'base').then(() => {
          for (let i = 1; i < files.length; i++) importImage(files[i], 'top');
        });
      } else {
        for (const f of files) importImage(f, 'top');
      }
    });

    /* ---------------- 键盘 ---------------- */
    window.addEventListener('keydown', (e) => {
      const tag = (e.target && e.target.tagName) || '';
      if (tag === 'INPUT' && e.target.type === 'text') return;

      if (e.code === 'Space' && !state.spaceDown) {
        state.spaceDown = true;
        wrap.classList.add('is-panning');
        hideBrushCursor();
        e.preventDefault();
        return;
      }
      const mod = e.ctrlKey || e.metaKey;
      if (mod && (e.key === 'z' || e.key === 'Z')) {
        e.preventDefault();
        if (e.shiftKey) redo(); else undo();
        return;
      }
      if (mod && (e.key === 'y' || e.key === 'Y')) { e.preventDefault(); redo(); return; }

      if (mod) return;
      if (e.key === '[') { state.brush.size = clamp(state.brush.size - Math.max(2, state.brush.size * 0.12), 2, 2000); updateBrushUI(); refreshBrushCursor(); }
      else if (e.key === ']') { state.brush.size = clamp(state.brush.size + Math.max(2, state.brush.size * 0.12), 2, 2000); updateBrushUI(); refreshBrushCursor(); }
      else if (e.key === 'b' || e.key === 'B') setTool('paint');
      else if (e.key === 'e' || e.key === 'E') setTool('erase');
      else if (e.key === '0') resetView();
      else if (e.key === '1') setZoom(1 / baseFitScale());
    });

    window.addEventListener('keyup', (e) => {
      if (e.code === 'Space') {
        state.spaceDown = false;
        if (!state.panning) wrap.classList.remove('is-panning');
      }
    });
  }

  /* 笔刷参数变化后，把画笔圈同步到指针当前位置（键盘 [ ] 与拖滑杆都要用）。
     lastPointer 由 pointermove 维护；这里只做一次重定位，不参与渲染循环。 */
  let lastPointer = null;
  function refreshBrushCursor() {
    if (lastPointer) positionBrushCursor(lastPointer.clientX, lastPointer.clientY);
  }

  /* ============================================================
     启动
     ============================================================ */
  function init() {
    mask = document.createElement('canvas');
    mask.width = state.doc.w;
    mask.height = state.doc.h;
    maskCtx = mask.getContext('2d');

    bind();
    updateLayerUI();
    updateBrushUI();
    updateUndoUI();
    updateExportInfo();
    setTool('paint');
    updateStageHint();

    layout();
    new ResizeObserver(() => layout()).observe(wrap);
    window.addEventListener('resize', () => layout());
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
