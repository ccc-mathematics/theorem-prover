/* 一階邏輯歸結法定理證明器 — 核心(Node.js 與瀏覽器共用) */
(function () {
'use strict';
const SYM = { '∀': ' forall ', '∃': ' exists ', '¬': '~', '∧': '&', '∨': '|', '→': '->', '↔': '<->', '⊃': '->' };

/* ── 1. 解析器 ── 優先序:<-> < -> < | < & < ~ / 量詞 */
function parse(src) {
  const T = src.replace(/[∀∃¬∧∨→↔⊃]/g, c => SYM[c]).match(/<->|->|!=|[A-Za-z_][\w']*|\S/g) || [];
  let p = 0; const bound = [];
  const err = m => new Error(`${m}(附近:${T.slice(Math.max(0, p - 3), p + 1).join(' ') || '結尾'})`);
  const peek = () => T[p];
  const expect = t => { if (T[p++] !== t) throw err(`語法錯誤:預期 "${t}"`); };
  const ident = () => { const x = T[p++]; if (!x || !/^[A-Za-z_]/.test(x)) throw err('語法錯誤:這裡不能放這個符號'); return x; };
  const args = f => { const a = []; for (a.push(f()); peek() === ','; ) { p++; a.push(f()); } expect(')'); return a; };
  const term = () => { const n = ident(); if (peek() === '(') { p++; return { f: n, a: args(term) }; } return bound.includes(n) ? { v: n } : { f: n, a: [] }; };
  const iff = () => { let l = imp(); while (peek() === '<->') { p++; l = { t: 'iff', l, r: imp() }; } return l; };
  const imp = () => { const l = or(); if (peek() === '->') { p++; return { t: 'imp', l, r: imp() }; } return l; };
  const or = () => { let l = and(); while (peek() === '|') { p++; l = { t: 'or', l, r: and() }; } return l; };
  const and = () => { let l = un(); while (peek() === '&') { p++; l = { t: 'and', l, r: un() }; } return l; };
  const un = () => {
    const x = peek();
    if (x === '~') { p++; return { t: 'not', f: un() }; }
    if (x === 'forall' || x === 'exists') {
      p++; const vs = [];
      while (peek() !== '.') { if (peek() === ',') p++; else if (peek() === undefined || peek() === '(') throw err('語法錯誤:量詞變數後面需要加上 "."'); else vs.push(ident()); }
      p++; bound.push(...vs); const f = iff(); bound.length -= vs.length;
      return vs.reduceRight((b, v) => ({ t: x === 'forall' ? 'all' : 'ex', v, f: b }), f);
    }
    if (x === '(') { p++; const f = iff(); expect(')'); return f; }
    const n = ident(); let a = [];
    if (peek() === '(') { p++; a = args(term); }
    if (peek() === '=' || peek() === '!=') { // 等式:t1 = t2 或 t1 != t2
      const neg = T[p++] === '!=', l = a.length || !bound.includes(n) ? { f: n, a } : { v: n };
      const e = { t: 'atom', n: '=', a: [l, term()] };
      return neg ? { t: 'not', f: e } : e;
    }
    return { t: 'atom', n, a };
  };
  const f = iff();
  if (p < T.length) throw err('語法錯誤:多餘的符號,請檢查括號是否成對');
  return f;
}

/* ── 2. 轉子句:NNF → Skolem 化 → CNF ── */
let uid = 0, skn = 0;
const fresh = () => '_' + (++uid);
const isV = t => t.v !== undefined;
const sub = (t, env) => isV(t) ? (env[t.v] || t) : { f: t.f, a: t.a.map(x => sub(x, env)) };

function nnf(f, pos) {
  switch (f.t) {
    case 'atom': return pos ? f : { t: 'not', f };
    case 'not': return nnf(f.f, !pos);
    case 'and': case 'or': return { t: (f.t === 'and') === pos ? 'and' : 'or', l: nnf(f.l, pos), r: nnf(f.r, pos) };
    case 'imp': return nnf({ t: 'or', l: { t: 'not', f: f.l }, r: f.r }, pos);
    case 'iff': return nnf({ t: 'and', l: { t: 'imp', l: f.l, r: f.r }, r: { t: 'imp', l: f.r, r: f.l } }, pos);
    default: return { t: (f.t === 'all') === pos ? 'all' : 'ex', v: f.v, f: nnf(f.f, pos) };
  }
}
function skolem(f, env, us) {
  switch (f.t) {
    case 'all': { const v = fresh(); return skolem(f.f, { ...env, [f.v]: { v } }, [...us, { v }]); }
    case 'ex': return skolem(f.f, { ...env, [f.v]: { f: 'sk' + (++skn), a: us } }, us);
    case 'and': case 'or': return { t: f.t, l: skolem(f.l, env, us), r: skolem(f.r, env, us) };
    default: { const a = f.t === 'not' ? f.f : f; return { t: 'lit', s: f.t !== 'not', n: a.n, a: a.a.map(x => sub(x, env)) }; }
  }
}
function cnf(f) {
  if (f.t === 'lit') return [[f]];
  const L = cnf(f.l), R = cnf(f.r);
  if (f.t === 'and') return L.concat(R);
  const o = []; for (const a of L) for (const b of R) o.push(a.concat(b)); return o;
}
const clausify = f => cnf(skolem(nnf(f, true), {}, []));

/* ── 3. 合一(含 occurs check)與匹配 ── */
const walk = (t, s) => { while (isV(t) && s[t.v]) t = s[t.v]; return t; };
const occ = (v, t, s) => { t = walk(t, s); return isV(t) ? t.v === v : t.a.some(x => occ(v, x, s)); };
function unify(a, b, s) {
  a = walk(a, s); b = walk(b, s);
  if (isV(a)) { if (isV(b) && a.v === b.v) return s; return occ(a.v, b, s) ? null : { ...s, [a.v]: b }; }
  if (isV(b)) return unify(b, a, s);
  if (a.f !== b.f || a.a.length !== b.a.length) return null;
  for (let i = 0; i < a.a.length && s; i++) s = unify(a.a[i], b.a[i], s);
  return s;
}
const unifyL = (a, b, s) => {
  if (a.n !== b.n || a.a.length !== b.a.length) return null;
  for (let i = 0; i < a.a.length && s; i++) s = unify(a.a[i], b.a[i], s);
  return s;
};
const apply = (t, s) => { t = walk(t, s); return isV(t) ? t : { f: t.f, a: t.a.map(x => apply(x, s)) }; };
const applyL = (l, s) => ({ s: l.s, n: l.n, a: l.a.map(t => apply(t, s)) });

const ts = t => isV(t) ? t.v : t.f + (t.a.length ? '(' + t.a.map(ts).join(',') + ')' : '');
const ls = l => l.n === '=' ? ts(l.a[0]) + (l.s ? ' = ' : ' != ') + ts(l.a[1]) : (l.s ? '' : '~') + l.n + (l.a.length ? '(' + l.a.map(ts).join(',') + ')' : '');

function match(p, t, s) { // 單向匹配:只綁定 p 的變數
  if (isV(p)) { const b = s[p.v]; return b ? (ts(b) === ts(t) ? s : null) : { ...s, [p.v]: t }; }
  if (isV(t) || p.f !== t.f || p.a.length !== t.a.length) return null;
  for (let i = 0; i < p.a.length && s; i++) s = match(p.a[i], t.a[i], s);
  return s;
}
function subsumes(c, d, s = {}, i = 0) { // c 是否包含 d
  if (i === c.length) return true;
  for (const l of d) {
    if (l.s !== c[i].s || l.n !== c[i].n || l.a.length !== c[i].a.length) continue;
    let t = s; for (let j = 0; j < l.a.length && t; j++) t = match(c[i].a[j], l.a[j], t);
    if (t && subsumes(c, d, t, i + 1)) return true;
  }
  return false;
}
const ren = lits => { const m = {}; const r = t => isV(t) ? (m[t.v] ??= { v: fresh() }) : { f: t.f, a: t.a.map(r) }; return lits.map(l => ({ s: l.s, n: l.n, a: l.a.map(r) })); };
function norm(lits) { // 去重複文字、剔除恆真子句、變數改名
  const seen = new Set(), out = [];
  for (const l of lits) { const k = ls(l); if (!seen.has(k)) { seen.add(k); out.push(l); } }
  if (out.some(l => l.s && l.n === '=' && ts(l.a[0]) === ts(l.a[1]))) return null; // t = t 恆真
  for (const l of out) if (seen.has(ls({ ...l, s: !l.s }))) return null;
  return ren(out);
}

/* ── 4a. 等式替換(paramodulation):用 A 中的 l = r 改寫 B 的子項 ── */
function* pos(t) {
  if (isV(t)) return;
  yield [t, x => x];
  for (let i = 0; i < t.a.length; i++) for (const [u, k] of pos(t.a[i])) yield [u, x => ({ f: t.f, a: t.a.map((y, j) => j === i ? k(x) : y) })];
}
function para(A, B, ida, idb, out) {
  for (const e of A) {
    if (!e.s || e.n !== '=') continue;
    for (const [l, r] of [[e.a[0], e.a[1]], [e.a[1], e.a[0]]]) {
      if (isV(l)) continue;
      for (const L of B) for (let i = 0; i < L.a.length; i++) for (const [u, k] of pos(L.a[i])) {
        const s = unify(l, u, {}); if (!s) continue;
        const L2 = { s: L.s, n: L.n, a: L.a.map((y, j) => j === i ? k(r) : y) };
        out.push([[...A.filter(x => x !== e), ...B.map(x => x === L ? L2 : x)].map(x => applyL(x, s)), 'para', [ida, idb]]);
      }
    }
  }
}

/* ── 4b. 歸結引擎(given-clause 迴圈) ── */
function prove(premises, goal, opts = {}) {
  const maxMs = opts.maxMs || 10000, maxN = opts.maxClauses || 20000, t0 = Date.now();
  const all = [], active = [], passive = []; let nid = 0, gen = 0, empty = null;
  const prune = (arr, c) => { for (let i = arr.length; i--; ) if (arr[i].lits.length >= c.lits.length && subsumes(c.lits, arr[i].lits)) arr.splice(i, 1); };
  const accept = (lits, rule, from) => {
    const l = norm(lits); if (!l) return null;
    for (const c of active.concat(passive)) if (c.lits.length <= l.length && subsumes(c.lits, l)) return null;
    const c = { id: ++nid, lits: l, rule, from, w: l.map(ls).join('').length };
    all[c.id] = c; prune(active, c); prune(passive, c); passive.push(c); gen++;
    if (!l.length) empty = c;
    return c;
  };
  const load = (src, rule) => { let f; try { f = parse(src); } catch (e) { throw new Error(`「${src}」${e.message}`); } return { f, rule }; };
  const items = premises.map(s => load(s, 'premise'));
  if (goal) { const g = load(goal, 'negated goal'); items.push({ f: { t: 'not', f: g.f }, rule: g.rule }); }
  for (const { f, rule } of items) for (const c of clausify(f)) accept(c, rule, []);

  while (!empty) {
    if (!passive.length) return fin('saturated');
    if (Date.now() - t0 > maxMs || gen > maxN) return fin('timeout');
    let bi = 0; for (let i = 1; i < passive.length; i++) if (passive[i].w < passive[bi].w) bi = i;
    const g = passive.splice(bi, 1)[0]; active.push(g);
    const news = [];
    for (let i = 0; i < g.lits.length; i++) for (let j = i + 1; j < g.lits.length; j++) { // 因子化
      if (g.lits[i].s !== g.lits[j].s) continue;
      const s = unifyL(g.lits[i], g.lits[j], {});
      if (s) news.push([g.lits.filter((_, k) => k !== j).map(x => applyL(x, s)), 'factor', [g.id]]);
    }
    for (const l of g.lits) { // 等式歸結:消去 t != t'
      if (l.s || l.n !== '=') continue;
      const s = unify(l.a[0], l.a[1], {});
      if (s) news.push([g.lits.filter(x => x !== l).map(x => applyL(x, s)), 'eqres', [g.id]]);
    }
    for (const h of active) { // 二元歸結與等式替換
      const hl = h === g ? ren(g.lits) : h.lits;
      para(g.lits, hl, g.id, h.id, news); para(hl, g.lits, h.id, g.id, news);
      for (const a of g.lits) for (const b of hl) {
        if (a.s === b.s) continue;
        const s = unifyL(a, b, {}); if (!s) continue;
        news.push([[...g.lits.filter(x => x !== a), ...hl.filter(x => x !== b)].map(x => applyL(x, s)), 'resolve', [g.id, h.id]]);
      }
    }
    for (const [l, r, f] of news) { accept(l, r, f); if (empty) break; }
  }
  return fin('proved');

  function fin(status) {
    const steps = [];
    if (empty) {
      const seen = new Set(), st = [empty.id];
      while (st.length) { const id = st.pop(); if (!seen.has(id)) { seen.add(id); st.push(...all[id].from); } }
      [...seen].sort((a, b) => a - b).forEach(id => steps.push({ id, text: fmtClause(all[id]), rule: fmtRule(all[id]), from: all[id].from }));
    }
    return { status, steps, generated: gen, ms: Date.now() - t0, hasGoal: !!goal };
  }
}

/* ── 5. 輸出 ── */
const pv = s => s.replace(/\b_(\d+)/g, 'X$1');
const fmtClause = c => c.lits.length ? pv(c.lits.map(ls).join(' | ')) : '⊥';
const fmtRule = c => c.rule === 'premise' ? '前提' : c.rule === 'negated goal' ? '否定結論' : ({ resolve: '歸結 ', factor: '因子化 ', para: '等式替換 ', eqres: '等式歸結 ' }[c.rule]) + c.from.join(', ');
const statusText = r => r.status === 'proved'
  ? `✔ ${r.hasGoal ? '證明成功' : '前提互相矛盾'}(產生 ${r.generated} 個子句,${r.ms} ms)`
  : r.status === 'saturated' ? '✘ 無法證明:子句集已飽和,結論不是前提的邏輯後果'
  : '… 超過時間或子句數上限,結果未知';
const format = r => [statusText(r), ...r.steps.map(s => `${String(s.id).padStart(3)}. ${s.text}    [${s.rule}]`)].join('\n');

/* ── 6. 範例 ── */
const examples = [
  { name: '蘇格拉底三段論', premises: ['forall x. (Man(x) -> Mortal(x))', 'Man(socrates)'], goal: 'Mortal(socrates)' },
  { name: '理髮師悖論(前提矛盾)', premises: ['exists b. forall x. (Shaves(b,x) <-> ~Shaves(x,x))'], goal: '' },
  { name: 'Peirce’s law', premises: [], goal: '((P -> Q) -> P) -> P' },
  { name: '飲酒者悖論', premises: [], goal: 'exists x. (D(x) -> forall y. D(y))' },
  { name: '傳遞關係', premises: ['forall x y z. ((R(x,y) & R(y,z)) -> R(x,z))', 'R(a,b)', 'R(b,c)', 'R(c,d)'], goal: 'R(a,d)' },
  { name: '等式代入', premises: ['a = b', 'b = c', 'P(a)'], goal: 'P(c)' },
  { name: 'f(f(a)) = a 的推論', premises: ['f(f(a)) = a', 'f(f(f(a))) = a'], goal: 'f(a) = a' },
  { name: '群論:單位元的反元素', premises: ['forall x. mul(e,x) = x', 'forall x. mul(inv(x),x) = e', 'forall x y z. mul(mul(x,y),z) = mul(x,mul(y,z))'], goal: 'inv(e) = e' },
  { name: '非定理(應回報失敗)', premises: [], goal: 'P -> Q' },
];

const API = { parse, prove, format, statusText, examples };
if (typeof module !== 'undefined' && module.exports) module.exports = API; else globalThis.Prover = API;
})();
