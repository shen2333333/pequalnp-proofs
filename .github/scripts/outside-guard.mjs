#!/usr/bin/env node
// Guards for a pull request that adds one proof file. Used by both workflows, before anything
// is built. Plain node, no dependencies. Every value this script hands back to the shell has
// passed a strict pattern, so the shell never sees free text from a pull request.
//
//   node outside-guard.mjs pr <pr.json> <files.json> <tree.json> <repo> <default branch> <out dir>
//   node outside-guard.mjs gap <gaps.json> <gap id> <file path> <out dir>
//   node outside-guard.mjs gap-of-file <gaps.json> <file path> <out dir>
//   node outside-guard.mjs imports <lean file> <imports.json>
//
// Exit 0: the guard holds. Exit 1: REFUSED, with one line saying why. Exit 3: bad usage.
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

export const FILE_RE = /^lean\/PEqualNP\/Outside\/L_[a-z0-9_]+\.lean$/;
export const GAP_RE = /^L-[a-z0-9]+(-[a-z0-9]+)*$/;
export const MODULE_RE = /^PEqualNP(\.[A-Za-z][A-Za-z0-9_]*)+$/;
export const MAX_BYTES = 512 * 1024;
const SHA_RE = /^[0-9a-f]{40}$/;
const LOGIN_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(\[bot\])?$/;

class Refused extends Error {}
const refuse = (why) => { throw new Refused(why); };
const json = (path) => { try { return JSON.parse(readFileSync(path, 'utf8')); } catch { return refuse(`${path} is not JSON`); } };
const moduleOf = (file) => file.slice('lean/'.length, -'.lean'.length).split('/').join('.');

// The pull request must add exactly one file, the allowed kind, as a plain file, and nothing else.
// Read from the API's own answers: the pull request, its file list, the tree of its head commit.
export function checkPr(pr, files, tree, repo, defaultBranch) {
  if (pr?.state !== 'open') refuse('the pull request is not open');
  if (pr.base?.repo?.full_name !== repo) refuse('the pull request is not against this repository');
  if (pr.base?.ref !== defaultBranch) refuse(`the pull request is not against ${defaultBranch}`);
  const head = pr.head?.sha;
  if (!SHA_RE.test(head ?? '')) refuse('the pull request has no head commit');
  const author = pr.user?.login;
  if (!LOGIN_RE.test(author ?? '')) refuse('the pull request author is not a plain account name');
  // changed_files is the whole count, so a long file list cannot hide a second file on another page.
  if (pr.changed_files !== 1) refuse(`the pull request changes ${pr.changed_files} files; it must add exactly one`);
  if (!Array.isArray(files) || files.length !== 1) refuse('the pull request must add exactly one file');
  const f = files[0];
  if (typeof f.filename !== 'string' || !FILE_RE.test(f.filename)) refuse('the one file must be lean/PEqualNP/Outside/L_<gap>.lean');
  if (f.status !== 'added') refuse(`the file must be added, not ${f.status}`);
  if (!SHA_RE.test(f.sha ?? '')) refuse('the file list names no content hash');
  // The tree says what kind of entry it is. 100644 is a plain file: a symbolic link is 120000,
  // an executable 100755, a submodule 160000, and each is refused.
  if (tree?.truncated) refuse('the tree of the head commit is too large to read whole');
  const entries = (tree?.tree ?? []).filter((e) => e.path === f.filename);
  if (entries.length !== 1) refuse('the file is not in the tree of the head commit');
  const e = entries[0];
  if (e.type !== 'blob' || e.mode !== '100644') refuse('the file must be a plain file (not a link, not executable)');
  if (e.sha !== f.sha) refuse('the file list and the tree disagree about the content');
  if (!Number.isInteger(e.size) || e.size < 1 || e.size > MAX_BYTES) refuse(`the file must be between 1 and ${MAX_BYTES} bytes`);
  return { file: f.filename, module: moduleOf(f.filename), head, blob: f.sha, author, size: e.size };
}

// The gap as the desk posts it. Its file must be the file of the pull request.
export function checkGap(gaps, pick, file) {
  const all = Array.isArray(gaps?.gaps) ? gaps.gaps : refuse('the gap list has no gaps');
  const found = all.filter(pick);
  if (found.length !== 1) refuse('the gap is not posted (it may be checked already, or withdrawn)');
  const g = found[0];
  if (typeof g.id !== 'string' || !GAP_RE.test(g.id)) refuse('the posted gap has a malformed id');
  if (g.file !== file || !FILE_RE.test(file)) refuse(`the file of gap ${g.id} is not the file of this pull request`);
  if (g.module !== moduleOf(file)) refuse(`gap ${g.id} names a module that is not its file`);
  if (typeof g.statement !== 'string' || !g.statement.trim() || g.statement.includes('\0')) refuse(`gap ${g.id} has no statement`);
  const imports = g.imports ?? [];
  if (!Array.isArray(imports) || !imports.every((m) => typeof m === 'string' && MODULE_RE.test(m))) refuse(`gap ${g.id} lists a malformed import`);
  return { id: g.id, statement: g.statement, imports };
}

// The import rule. The file starts with its import lines, one module per line, and nothing else
// is among them. Each must be Mathlib, a module of Mathlib, or a module the gap lists. After the
// import lines the word `import` may not appear at all: Lean reads imports through comments, so
// `/- -/ import X` on a later line would still be an import. A plain rule, stricter than Lean.
export function checkImports(bytes, allowed) {
  if (bytes.length > MAX_BYTES) refuse(`the file is larger than ${MAX_BYTES} bytes`);
  let text;
  try { text = new TextDecoder('utf-8', { fatal: true }).decode(bytes); } catch { return refuse('the file is not UTF-8 text'); }
  if (text.includes('\0')) refuse('the file holds a NUL byte');
  const lines = text.split('\n').map((l) => l.replace(/\r$/, ''));
  const ok = new Set(allowed);
  const seen = [];
  let i = 0;
  for (; i < lines.length; i += 1) {
    const l = lines[i];
    if (l.trim() === '') continue;
    const m = /^import ([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)[ \t]*$/.exec(l);
    if (!m) break;
    const name = m[1];
    if (!(name === 'Mathlib' || name.startsWith('Mathlib.') || ok.has(name))) refuse(`line ${i + 1}: import ${name} is not allowed (only Mathlib and the modules the gap lists)`);
    seen.push(name);
  }
  for (; i < lines.length; i += 1) {
    if (/(^|[^A-Za-z0-9_])import([^A-Za-z0-9_]|$)/.test(lines[i])) refuse(`line ${i + 1}: the word "import" after the import lines (imports are plain lines at the top, one module each)`);
  }
  checkPlain(text);
  return seen;
}

// THE DANGEROUS-BY-NAME RULE: a first filter, NOT what makes an outside file safe to build. A
// Lean file runs code while it compiles; what contains that is the sandbox this job runs in (no
// secrets, no network, a time limit, a machine thrown away after) and the checker's own rules.
// This rule refuses, early and by name, what has no place in a proof file: code that runs at
// build time, new syntax, kernel bypasses, the meta-programming namespaces, string literals.
//   1. The RAW text is searched, comments included, and nothing is stripped: a stripper can be
//      led astray, so none is used. A refused word inside a comment is refused too: reword it.
//   2. It does NOT judge form. Comment prose at column 0, a `#` heading in a doc comment, a small
//      data type (`inductive ... deriving DecidableEq`) or an instance are built and judged by
//      the checker; whether such a file is merged is decided where it is read before any merge.
//      (Measured 2026-11-23: a rule that also refused form bounced nine honest proofs of
//      eighteen, each for a comment line or a small enumerated type.)
//   3. KNOWN LIMIT: the list cannot be complete. What it misses meets the sandbox.
// The only attributes are `@[simp]` and `@[local simp]`; the only options are four limits.
const B = String.raw`(?<![A-Za-z0-9_])`, A = String.raw`(?![A-Za-z0-9_])`;
const FORBIDDEN = new RegExp([
  String.raw`"|[«»]|simproc|builtin_|native|bv_decide|ofReduce|reduceNat|reduceBool`,
  '|' + B + String.raw`(Lean|System|IO|Elab|Meta|Lake|FS|Process|EIO)` + A,
  String.raw`|_root_|RealWorld|BaseIO|include_str|notation|[A-Za-z0-9_]%|polyrith|initialize|run_cmd|run_tac|run_elab|run_meta|by_elab`,
  '|' + B + String.raw`elab|` + B + String.raw`macro|` + B + 'syntax' + A + '|' + B + 'attribute' + A,
  '|' + B + 'axiom' + A + '|' + B + 'opaque' + A + String.raw`|unsafe|` + B + 'partial' + A + String.raw`|sorry|` + B + 'admit' + A,
  String.raw`|#[a-z_][a-z_]{2,}|implemented_by|extern`,
  String.raw`|` + '`' + String.raw`\([a-z]+\||\$\(|%\[|@\[|register_|declare_|lcProof|lcUnreachable|` + B + 'infix|' + B + 'prefix' + A + '|' + B + 'postfix' + A,
  String.raw`|set_option|binder_predicate|unif_hint|^\s*add_\w+|unseal|compile_inductive|irreducible_def`,
].join(''), 'u');
// The four limit options, wherever they stand, are taken out before the list is asked; every
// other set_option, at column 0 or indented, is refused by it.
const LIMIT = /set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+ in(?![A-Za-z0-9_])/gu;
const INVISIBLE = /[​-‏‪-‮⁠-⁩﻿]/u;
const CONTROL = /[\u0000-\u0008\u000b-\u001f\u007f]/u;

export function checkPlain(text) {
  if (CONTROL.test(text.replace(/\r?\n/g, ''))) refuse('the file holds control characters');
  if (INVISIBLE.test(text)) refuse('the file holds invisible or direction-changing characters');
  let theorems = 0;
  text.split('\n').forEach((raw, k) => {
    const line = raw.replace(/\r$/, '');
    const m = FORBIDDEN.exec(line.replace(LIMIT, '').replace(/@\[(local )?simp\]/gu, ''));
    if (m) refuse(`line ${k + 1}: "${m[0].trim()}" is not allowed in a proof file, in code or in a comment (no code that runs at build time, no new syntax, no string literals, no attributes but simp, no options but the four limits)`);
    if (/^\s*(@\[(local )?simp\] )?((private|protected) )?theorem /u.test(line)) theorems += 1;
  });
  if (theorems === 0) refuse('the file holds no theorem');
}

const put = (dir, name, value) => writeFileSync(join(dir, name), value);
const main = () => {
  const [cmd, ...a] = process.argv.slice(2);
  if (cmd === 'pr' && a.length === 6) {
    const r = checkPr(json(a[0]), json(a[1]), json(a[2]), a[3], a[4]);
    for (const [k, v] of Object.entries(r)) put(a[5], `pr.${k}`, `${v}\n`);
  } else if ((cmd === 'gap' && a.length === 4) || (cmd === 'gap-of-file' && a.length === 3)) {
    const byId = cmd === 'gap';
    const [gapsPath, file, out] = byId ? [a[0], a[2], a[3]] : a;
    if (byId && !GAP_RE.test(a[1])) refuse('the gap id is malformed');
    const g = checkGap(json(gapsPath), byId ? (x) => x?.id === a[1] : (x) => x?.file === file, file);
    put(out, 'gap.id', `${g.id}\n`);
    put(out, 'statement.txt', g.statement);          // the posted text, byte for byte
    put(out, 'imports.json', JSON.stringify(g.imports));
    put(out, 'imports.txt', g.imports.map((m) => `${m}\n`).join(''));
  } else if (cmd === 'imports' && a.length === 2) {
    const seen = checkImports(readFileSync(a[0]), json(a[1]));
    process.stdout.write(`imports allowed: ${seen.join(' ') || '(none)'}\n`);
  } else {
    process.stderr.write('usage: outside-guard.mjs pr|gap|gap-of-file|imports ... (see the header)\n');
    process.exit(3);
  }
};

if (process.argv[1] && import.meta.url === new URL(`file://${process.argv[1]}`).href) {
  try { main(); } catch (e) {
    if (!(e instanceof Refused)) throw e;
    process.stdout.write(`REFUSED: ${e.message}\n`);
    process.exit(1);
  }
}
