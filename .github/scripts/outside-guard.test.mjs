// node --test .github/scripts/outside-guard.test.mjs
// The plain-file rule of outside-guard.mjs: one fixture per way a proof file could carry code
// that runs while it compiles (or hide it from a reader), and the honest shapes that must pass.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkImports } from './outside-guard.mjs';

const head = 'import Mathlib\nimport PEqualNP.Defs\n\n';
const run = (body) => checkImports(new TextEncoder().encode(head + body), ['PEqualNP.Defs']);
const refused = (name, body, word) => test(`refused: ${name}`, () => {
  assert.throws(() => run(body), (e) => e.message.includes(word), 'not refused, or for another reason');
});
const passes = (name, body) => test(`passes: ${name}`, () => { assert.deepEqual(run(body), ['Mathlib', 'PEqualNP.Defs']); });
const thm = 'theorem PEqualNP.Outside.L_x_1 : True := trivial\n';
const by = (tac) => `theorem PEqualNP.Outside.L_x_1 : True := by\n  ${tac}\n`;

refused('an initialize', `initialize pure ()\n${thm}`, 'initialize');
refused('an indented initialize', `${thm}  initialize pure ()\n`, 'initialize');
refused('run_cmd, indented', `${thm} run_cmd pure ()\n`, 'run_cmd');
refused('#eval', `${thm} #eval 1\n`, '#');
refused('a tactic that runs code', by('run_tac (do return ())'), 'run_tac');
refused('an elaborator, indented', `${thm} elab x : term => pure default\n`, 'elab');
refused('a macro, indented', `${thm} macro x : tactic => y\n`, 'macro');
refused('notation3', `${thm} notation3 x => y\n`, 'notation');
refused('an attribute command', `${thm} attribute [simp] Nat.add_comm\n`, 'attribute');
refused('a generating attribute', `@[to_additive] theorem foo : True := trivial\n${thm}`, '@[');
refused('an option that is not a limit', `set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an indented option that is not a limit', by('set_option debug.skipKernelTC true in\n  trivial'), 'set_option');
refused('a same-line option that is not a limit', `set_option maxHeartbeats 1 in set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an axiom', `${thm} axiom a : False\n`, 'axiom');
refused('sorry', by('sorry'), 'sorry');
refused('sorryAx', 'theorem PEqualNP.Outside.L_x_1 : False := sorryAx _\n', 'sorry');
refused('lcProof', 'theorem PEqualNP.Outside.L_x_1 : False := lcProof\n', 'lcProof');
refused('native_decide', by('native_decide'), 'native');
refused('decide +native', by('decide +native'), 'native');
refused('bv_decide', by('bv_decide'), 'bv_decide');
refused('a simproc', `${thm}  simproc foo (x) := y\n`, 'simproc');
refused('open Lean', `open Lean in\n${thm}`, 'Lean');
refused('ofReduceBool', by('exact ofReduceBool x true rfl'), 'ofReduce');
refused('_root_', by('exact _root_.id trivial'), '_root_');
refused('include_str', by('exact include_str x'), 'include_str');
refused('polyrith', by('polyrith'), 'polyrith');
refused('a string literal', `private def s : String := "x"\n${thm}`, '"');
refused('a character-literal trick', `${thm}  -- '"'\n`, '"');
refused('a quoted identifier', `private def «a» : Nat := 1\n${thm}`, '«');
refused('code hidden behind a comment trick', `-- a note /- here\n  initialize pure ()\n-- done -/\n${thm}`, 'initialize');
refused('a command after a comment on one line', `/- note -/ initialize pure ()\n${thm}`, 'initialize');
refused('a syntax quotation', by('exact \x60(tactic| trivial)'), '(tactic|');
refused('#check', `#check Nat\n${thm}`, '#check');
refused('#print axioms, indented', `${thm}  #print axioms Nat.add_comm\n`, '#print');
refused('a direction-changing character', `-- ‮\n${thm}`, 'invisible');
refused('no theorem at all', 'def x : Nat := 1\n', 'no theorem');

passes('one theorem', thm);
passes('helpers, definitions, namespaces, a docstring', `namespace Gap\nopen Finset\nvariable {n : ℕ}\n/-- A doc comment. -/\nprivate def f (x : ℕ) : ℕ := x\nprivate lemma l : f 1 = 1 := rfl\nend Gap\n\n${thm}`);
passes('a block comment with indented prose', `/-\n  The idea of the proof,\n  in two lines.\n-/\n${thm}`);
passes('the simp attributes', `@[simp] private theorem a : True := trivial\n@[local simp] private theorem b : True := trivial\n${thm}`);
passes('the four limit options', `set_option maxHeartbeats 400000 in\nset_option maxRecDepth 2000 in\n${thm}`);
passes('an indented limit option inside a proof', by('set_option maxRecDepth 2000 in\n  trivial'));
passes('comment prose at column 0 and a heading (form is not judged)', `/-!\n# A heading\n\nProse that starts in column 0,\nover two lines.\n-/\n${thm}`);
passes('a small enumerated type and an instance', `private inductive Stack | input | output\n  deriving DecidableEq\n\nprivate instance : Inhabited Stack := ⟨.input⟩\n${thm}`);
passes('open scoped, and a cardinality written with a hash', `open scoped BigOperators\ntheorem PEqualNP.Outside.L_x_1 (s : Finset ℕ) : #s = #s := rfl\n`);
passes('a pair in backticks inside a doc comment', '/-- The coordinates \x60(a, b, c, d)\x60 of the block. -/\n' + thm);
passes('lemma names that contain add_', by('simp only [Nat.add_comm, add_zero]'));
