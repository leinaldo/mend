// mend: one patch tool for every AI edit format (SPEC.md v1).
// Implements sections 1-10: CLI, output, safe paths, format detection,
// matching at three tiers, unified diffs, SEARCH/REPLACE, V4A, JSON edits,
// order and atomicity. Node 22+, standard library alone.
// Based on the kit starter (MIT) for sections 1-4, 9 and 10; the other
// formats and matching are implemented here.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) { this.line = line; }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) { this.code = code; this.path = path; }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

function leadingWS(s: string): string {
  const m = s.match(/^[ \t]*/);
  return m ? m[0] : '';
}
function trimEndWS(s: string): string { return s.replace(/[ \t]+$/, ''); }
function trimWS(s: string): string { return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, ''); }

interface FileParts { br: string; lines: string[]; finalBr: boolean; }
function fileSplit(text: string): FileParts {
  if (text === '') return { br: '\n', lines: [], finalBr: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBr = text.endsWith(br);
  if (finalBr) parts.pop();
  return { br, lines: parts, finalBr };
}
function fileJoin(lines: string[], br: string, finalBr: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (finalBr ? br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try { if (statSync(p).isFile()) v = readFileSync(p, 'utf8'); } catch { v = null; }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;
interface Item { text: string; ctx: boolean; noNL?: boolean; kind?: 'ctx' | 'old' | 'new'; }

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

function tierTransform(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return trimEndWS(s);
  return trimWS(s);
}
function findOccurrences(fileLines: string[], o: string[], tier: number): number[] {
  const ot = o.map((s) => tierTransform(s, tier));
  const pos: number[] = [];
  if (o.length === 0) return pos;
  for (let i = 0; i + o.length <= fileLines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (tierTransform(fileLines[i + j], tier) !== ot[j]) { ok = false; break; }
    }
    if (ok) pos.push(i);
  }
  return pos;
}
function matchTierFrom(fileLines: string[], o: string[], strict: boolean, from: number): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const positions = findOccurrences(fileLines, o, tier).filter((x) => x >= from);
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}
function matchTier(fileLines: string[], o: string[], strict: boolean): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const positions = findOccurrences(fileLines, o, tier);
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

/** Build the replacement lines for Oitems -> Nitems at pos, tier as in SPEC section 5. */
function buildReplacement(fileLines: string[], pos: number, oItems: Item[], nItems: Item[], tier: number): string[] {
  const oCtxIdx: number[] = [];
  oItems.forEach((it, idx) => { if (it.ctx) oCtxIdx.push(idx); });
  let ctxCount = 0;
  const f = tier === 2 && oItems.length > 0 ? leadingWS(fileLines[pos] ?? '') : '';
  const p = tier === 2 && oItems.length > 0 ? leadingWS(oItems[0].text) : '';
  const out: string[] = [];
  for (const n of nItems) {
    if (n.ctx) {
      const oIdx = oCtxIdx[ctxCount++];
      out.push(fileLines[pos + oIdx]);
    } else {
      let txt = n.text;
      if (tier === 2 && txt.trim() !== '' && txt.startsWith(p)) txt = f + txt.slice(p.length);
      out.push(txt);
    }
  }
  return out;
}
function applyItems(fileLines: string[], pos: number, oItems: Item[], nItems: Item[], tier: number): string[] {
  const rep = buildReplacement(fileLines, pos, oItems, nItems, tier);
  return [...fileLines.slice(0, pos), ...rep, ...fileLines.slice(pos + oItems.length)];
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const parts = fileSplit(before);
      if (line < 0 || line > parts.lines.length) throw new Fail('no-match', p);
      const lines = [...parts.lines];
      lines.splice(line, 0, ...add);
      tree.now.set(p, fileJoin(lines, parts.br, parts.finalBr));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- Unified diffs (section 6) ----

interface Hunk { a: number; o: Item[]; n: Item[]; items: Item[]; }
interface UniSection { oldPath: string | null; newPath: string | null; isCreate: boolean; isDelete: boolean; hunks: Hunk[]; }

function diffPath(raw: string): string | null {
  const t = raw.split('\t')[0].trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/')) return t.slice(2);
  if (t.startsWith('b/')) return t.slice(2);
  return t;
}
function parseHunkHeader(line: string, lineNo: number): number {
  const m = line.match(/^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@(?:.*)?$/);
  if (!m) throw new Exit2(`error: parse ${lineNo}`);
  return parseInt(m[1], 10);
}
function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let sec: UniSection | null = null;
  // mode: 'outside' | 'header' | 'section' (after at least one hunk)
  let mode = 'outside';
  let i = 0;
  const startSection = (oldP: string | null, newP: string | null): void => {
    sec = { oldPath: oldP, newPath: newP, isCreate: false, isDelete: false, hunks: [] };
    sections.push(sec);
    mode = 'header';
  };
  while (i < lines.length) {
    const line = lines[i];
    if (line.startsWith('diff --git ')) {
      const m = line.match(/^diff --git a\/(.+?) b\/(.+)$/);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      startSection(m[1], m[2]);
      i++;
      continue;
    }
    if (mode === 'outside') {
      if (line.startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) {
        startSection(diffPath(line.slice(4)), diffPath(lines[i + 1].slice(4)));
        i += 2;
        continue;
      }
      if (line.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
      i++;
      continue;
    }
    if (mode === 'header') {
      if (line.startsWith('@@')) {
        const a = parseHunkHeader(line, i + 1);
        i++;
        const body = readBody(lines, i);
        i = body.next;
        sec!.hunks.push({ a, o: body.o, n: body.n, items: body.items });
        mode = 'section';
        continue;
      }
      if (line.startsWith('--- ')) {
        if (i + 1 >= lines.length || !lines[i + 1].startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
        sec!.oldPath = diffPath(line.slice(4));
        sec!.newPath = diffPath(lines[i + 1].slice(4));
        i += 2;
        continue;
      }
      if (line.startsWith('rename from ')) { sec!.oldPath = line.slice(12).trim(); i++; continue; }
      if (line.startsWith('rename to ')) { sec!.newPath = line.slice(10).trim(); i++; continue; }
      if (line.startsWith('new file mode')) { sec!.isCreate = true; i++; continue; }
      if (line.startsWith('deleted file mode')) { sec!.isDelete = true; i++; continue; }
      i++;
      continue;
    }
    // mode === 'section'
    if (line.startsWith('@@')) {
      const a = parseHunkHeader(line, i + 1);
      i++;
      const body = readBody(lines, i);
      i = body.next;
      sec!.hunks.push({ a, o: body.o, n: body.n, items: body.items });
      continue;
    }
    if (line.startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) {
      startSection(diffPath(line.slice(4)), diffPath(lines[i + 1].slice(4)));
      i += 2;
      continue;
    }
    i++;
  }
  return sections.map((s) => unifiedEdit(s, strict));
}

function readBody(lines: string[], start: number): { o: Item[]; n: Item[]; items: Item[]; next: number } {
  const raw: string[] = [];
  let i = start;
  while (i < lines.length) {
    const l = lines[i];
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) break;
    if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) { raw.push(l); i++; continue; }
    break;
  }
  while (raw.length > 0 && raw[raw.length - 1] === '') raw.pop();
  const o: Item[] = [];
  const n: Item[] = [];
  const items: Item[] = [];
  for (const l of raw) {
    if (l.startsWith('\\')) {
      if (items.length > 0) items[items.length - 1].noNL = true;
      continue;
    }
    if (l === '') { const it: Item = { text: '', ctx: true, kind: 'ctx' }; o.push(it); n.push(it); items.push(it); }
    else if (l.startsWith(' ')) { const it: Item = { text: l.slice(1), ctx: true, kind: 'ctx' }; o.push(it); n.push(it); items.push(it); }
    else if (l.startsWith('-')) { const it: Item = { text: l.slice(1), ctx: false, kind: 'old' }; o.push(it); items.push(it); }
    else if (l.startsWith('+')) { const it: Item = { text: l.slice(1), ctx: false, kind: 'new' }; n.push(it); items.push(it); }
  }
  return { o, n, items, next: i };
}


function lastCtxNewNoNL(items: Item[]): boolean | null {
  for (let k = items.length - 1; k >= 0; k--) {
    const it = items[k];
    if (it.kind === 'ctx' || it.kind === 'new') return it.noNL === true;
  }
  return null;
}

function applyHunksToText(text: string, hunks: Hunk[], strict: boolean, path: string): string {
  let parts = fileSplit(text);
  let lines = parts.lines;
  let finalBr = parts.finalBr;
  const br = parts.br;
  let d = 0;
  for (const h of hunks) {
    const oTexts = h.o.map((x) => x.text);
    if (h.o.length > 0) {
      const m = matchTier(lines, oTexts, strict);
      if (m === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let pos = m.positions[0];
      let best = Math.abs(pos - target);
      for (const p of m.positions) {
        const dist = Math.abs(p - target);
        if (dist < best) { best = dist; pos = p; }
      }
      const matchedEnd = pos + h.o.length === lines.length;
      const lastNoNL = lastCtxNewNoNL(h.items);
      const newLines = applyItems(lines, pos, h.o, h.n, m.tier);
      if (matchedEnd) {
        if (lastNoNL === null) finalBr = newLines.length === 0 ? false : true;
        else finalBr = !lastNoNL;
      }
      lines = newLines;
      d += h.n.length - h.o.length;
    } else {
      const insertPos = Math.min(h.a + d, lines.length);
      const atEnd = insertPos === lines.length;
      const lastNoNL = lastCtxNewNoNL(h.items);
      const newLines = [...lines.slice(0, insertPos), ...h.n.map((x) => x.text), ...lines.slice(insertPos)];
      if (atEnd && h.n.length > 0) finalBr = lastNoNL === null ? true : !lastNoNL;
      lines = newLines;
      d += h.n.length;
    }
  }
  return fileJoin(lines, br, finalBr);
}

function unifiedEdit(sec: UniSection, strict: boolean): Edit {
  return (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    const isCreate = sec.isCreate || oldP === null;
    const isDelete = sec.isDelete || newP === null;
    if (isCreate) {
      if (newP === null) throw new Fail('unsafe', '');
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const plus: string[] = [];
      let lastNoNL: boolean | null = null;
      for (const h of sec.hunks) {
        for (const it of h.items) {
          if (it.kind === 'new') { plus.push(it.text); lastNoNL = it.noNL === true; }
        }
      }
      const finalBr = plus.length === 0 ? false : (lastNoNL === null ? true : !lastNoNL);
      tree.now.set(newP, fileJoin(plus, '\n', finalBr));
      return;
    }
    if (isDelete) {
      if (oldP === null) throw new Fail('missing', '');
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (oldP === null || newP === null) throw new Fail('missing', oldP ?? newP ?? '');
    if (oldP !== newP) {
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const before = tree.get(oldP)!;
      const after = applyHunksToText(before, sec.hunks, strict, oldP);
      tree.now.set(oldP, null);
      tree.now.set(newP, after);
      tree.moves.push([oldP, newP]);
      return;
    }
    if (tree.get(oldP) === null) throw new Fail('missing', oldP);
    const before = tree.get(oldP)!;
    const after = applyHunksToText(before, sec.hunks, strict, oldP);
    tree.now.set(oldP, after);
  };
}

// ---- SEARCH/REPLACE blocks (section 7) ----

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1; // index of previous block's >>>>>>> line
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i].trimEnd() !== '<<<<<<< SEARCH') { i++; continue; }
    const s = i;
    // Path: nearest line before s, after prevEnd, not blank, not starting with ```
    let path: string | null = null;
    for (let j = s - 1; j > prevEnd; j--) {
      const l = lines[j];
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = prevPath;
    }
    // Find ======= then >>>>>>> REPLACE after s
    let eq = -1;
    for (let j = s + 1; j < lines.length; j++) {
      if (lines[j].trimEnd() === '=======') { eq = j; break; }
      if (lines[j].trimEnd() === '<<<<<<< SEARCH') break;
    }
    if (eq < 0) throw new Exit2(`error: parse ${s + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j].trimEnd() === '>>>>>>> REPLACE') { rep = j; break; }
      if (lines[j].trimEnd() === '<<<<<<< SEARCH') break;
    }
    if (rep < 0) throw new Exit2(`error: parse ${s + 1}`);
    const oldLines = lines.slice(s + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    const p = path;
    edits.push((tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (oldLines.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, fileJoin(newLines, '\n', newLines.length > 0));
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const parts = fileSplit(before);
      const m = matchTier(parts.lines, oldLines, strict);
      if (m === null) throw new Fail('no-match', p);
      if (m.positions.length !== 1) throw new Fail('ambiguous', p);
      const oItems: Item[] = oldLines.map((t) => ({ text: t, ctx: false }));
      const nItems: Item[] = newLines.map((t) => ({ text: t, ctx: false }));
      const newFileLines = applyItems(parts.lines, m.positions[0], oItems, nItems, m.tier);
      tree.now.set(p, fileJoin(newFileLines, parts.br, parts.finalBr));
    });
    prevPath = p;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

// ---- V4A patches (section 8) ----

interface VChunk { anchor: string | null; o: Item[]; n: Item[]; eof: boolean; }
interface VSection { kind: 'add' | 'delete' | 'update'; path: string; moveTo: string | null; lines: string[]; chunks: VChunk[]; lineNo: number; }

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  const last = (() => { let k = lines.length - 1; while (k >= 0 && blank(lines[k])) k--; return k; })();
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    if (blank(lines[i])) { i++; continue; }
    const line = lines[i];
    let kind: 'add' | 'delete' | 'update' | null = null;
    let path = '';
    if (line.startsWith('*** Add File:')) { kind = 'add'; path = line.slice('*** Add File:'.length).trim(); }
    else if (line.startsWith('*** Delete File:')) { kind = 'delete'; path = line.slice('*** Delete File:'.length).trim(); }
    else if (line.startsWith('*** Update File:')) { kind = 'update'; path = line.slice('*** Update File:'.length).trim(); }
    else throw new Exit2(`error: parse ${i + 1}`);
    const sectionLineNo = i + 1;
    i++;
    // Collect section lines until next section header or End Patch.
    const start = i;
    while (i < last) {
      const l = lines[i];
      if (l.startsWith('*** Add File:') || l.startsWith('*** Delete File:') || l.startsWith('*** Update File:')) break;
      i++;
    }
    let secLines = lines.slice(start, i);
    const secLineNos = secLines.map((_, k) => start + k + 1);
    // Blank lines at the end of a section are not part of it.
    while (secLines.length > 0 && blank(secLines[secLines.length - 1])) { secLines.pop(); secLineNos.pop(); }
    if (kind === 'add') {
      const fileLines: string[] = [];
      for (let k = 0; k < secLines.length; k++) {
        const l = secLines[k];
        if (l.startsWith('+')) fileLines.push(l.slice(1));
        else if (l === '') fileLines.push('');
        else throw new Exit2(`error: parse ${secLineNos[k]}`);
      }
      const p = path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, fileJoin(fileLines, '\n', fileLines.length > 0));
      });
    } else if (kind === 'delete') {
      for (let k = 0; k < secLines.length; k++) {
        if (!blank(secLines[k])) throw new Exit2(`error: parse ${secLineNos[k]}`);
      }
      const p = path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else {
      // update
      let moveTo: string | null = null;
      let rest = secLines;
      let restNos = secLineNos;
      if (rest.length > 0 && rest[0].startsWith('*** Move to:')) {
        moveTo = rest[0].slice('*** Move to:'.length).trim();
        rest = rest.slice(1);
        restNos = restNos.slice(1);
      }
      const chunks = parseVChunks(rest, restNos, sectionLineNo, moveTo !== null);
      const p = path;
      const mt = moveTo;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (mt !== null && !safe(mt)) throw new Fail('unsafe', mt);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        if (mt !== null && tree.get(mt) !== null) throw new Fail('exists', mt);
        const parts = fileSplit(before);
        let fileLines = parts.lines;
        let cursor = 0;
        for (const ch of chunks) {
          if (ch.anchor !== null) {
            let found: number | null = null;
            const tiers = strict ? [0] : [0, 1, 2];
            for (const tier of tiers) {
              const poss = findOccurrences(fileLines, [ch.anchor], tier).filter((x) => x >= cursor);
              if (poss.length > 0) { found = poss[0]; break; }
            }
            if (found === null) throw new Fail('no-match', p);
            cursor = found + 1;
          }
          const oTexts = ch.o.map((x) => x.text);
          if (ch.o.length === 0) {
            const pos = ch.eof ? fileLines.length : cursor;
            const rep = buildReplacement(fileLines, pos, [], ch.n, 0);
            fileLines = [...fileLines.slice(0, pos), ...rep, ...fileLines.slice(pos)];
            cursor = pos + ch.n.length;
            continue;
          }
          const m = matchTierFrom(fileLines, oTexts, strict, cursor);
          if (m === null) throw new Fail('no-match', p);
          const candidates = m.positions;
          if (candidates.length === 0) throw new Fail('no-match', p);
          let pos: number | null = null;
          for (const cpos of candidates) {
            if (ch.eof) {
              if (cpos + ch.o.length === fileLines.length) { pos = cpos; break; }
            } else { pos = cpos; break; }
          }
          if (pos === null) throw new Fail('no-match', p);
          fileLines = applyItems(fileLines, pos, ch.o, ch.n, m.tier);
          cursor = pos + ch.n.length;
        }
        const out = fileJoin(fileLines, parts.br, parts.finalBr);
        if (mt !== null) {
          tree.now.set(p, null);
          tree.now.set(mt, out);
          tree.moves.push([p, mt]);
        } else {
          tree.now.set(p, out);
        }
      });
    }
  }
  return edits;
}

function parseVChunks(lines: string[], lineNos: number[], sectionLineNo: number, hasMove: boolean): VChunk[] {
  if (lines.length === 0) {
    if (!hasMove) throw new Exit2(`error: parse ${sectionLineNo}`);
    return [];
  }
  const chunks: VChunk[] = [];
  let cur: { anchor: string | null; o: Item[]; n: Item[]; eof: boolean } | null = null;
  let started = false;
  let afterEof = false;
  const finish = (): void => {
    if (cur !== null) { chunks.push(cur); cur = null; }
  };
  for (let k = 0; k < lines.length; k++) {
    const l = lines[k];
    const no = lineNos[k];
    if (l.startsWith('@@')) {
      finish();
      afterEof = false;
      const anchorText = l.slice(2).trim();
      cur = { anchor: anchorText === '' ? null : anchorText, o: [], n: [], eof: false };
      started = true;
      continue;
    }
    if (l === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${no}`);
      cur.eof = true;
      finish();
      afterEof = true;
      continue;
    }
    if (l.startsWith('*** Move to:')) throw new Exit2(`error: parse ${no}`);
    if (l.startsWith('***')) throw new Exit2(`error: parse ${no}`);
    if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
      if (cur === null) {
        if (!started && !afterEof) {
          cur = { anchor: null, o: [], n: [], eof: false };
          started = true;
        } else {
          throw new Exit2(`error: parse ${no}`);
        }
      }
      if (l === '') { const it: Item = { text: '', ctx: true, kind: 'ctx' }; cur.o.push(it); cur.n.push(it); }
      else if (l.startsWith(' ')) { const it: Item = { text: l.slice(1), ctx: true, kind: 'ctx' }; cur.o.push(it); cur.n.push(it); }
      else if (l.startsWith('-')) { const it: Item = { text: l.slice(1), ctx: false, kind: 'old' }; cur.o.push(it); }
      else if (l.startsWith('+')) { const it: Item = { text: l.slice(1), ctx: false, kind: 'new' }; cur.n.push(it); }
      continue;
    }
    throw new Exit2(`error: parse ${no}`);
  }
  finish();
  if (chunks.length === 0 && !hasMove) throw new Exit2(`error: parse ${sectionLineNo}`);
  return chunks;
}


// ---- Main (sections 1, 2, 10) ----

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else if (kind === 'v4a') edits = parseV4a(lines, strict);
    else edits = [];
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // Output rows, with moves collapsed to R lines sorted by <new>.
  const changed = new Set<string>();
  for (const p of tree.now.keys()) {
    if (tree.original(p) !== tree.now.get(p)) changed.add(p);
  }
  const rows: Array<{ key: string; line: string }> = [];
  const usedOld = new Set<string>();
  const usedNew = new Set<string>();
  for (const [oldP, newP] of tree.moves) {
    if (changed.has(oldP) && changed.has(newP) && tree.original(oldP) !== null && tree.now.get(oldP) === null && tree.original(newP) === null && tree.now.get(newP) !== null) {
      rows.push({ key: newP, line: `R ${oldP} -> ${newP}` });
      usedOld.add(oldP);
      usedNew.add(newP);
    }
  }
  for (const p of changed) {
    if (usedOld.has(p) || usedNew.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const outLines = rows.map((r) => r.line);
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
