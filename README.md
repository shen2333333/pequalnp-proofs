# pequalnp proofs

Lean 4 proofs about computational complexity, each one machine-checked. The site that shows
what is checked and what is not: https://pequalnp.com

A statement counts here only when the checker accepts a proof of it. Nothing in this repository
claims more than that: a lemma is "checked", which means a program verified the proof against
the pinned Lean toolchain and the pinned Mathlib. No statement here says that P versus NP is
settled.

## What is in here

| Path | What it is |
|---|---|
| `lean/` | the Lean project: toolchain pin, Mathlib pin, and the modules under `PEqualNP/` |
| `lean/PEqualNP/Defs.lean`, `lean/PEqualNP/Defs/` | the definitions every statement is read against |
| `lean/PEqualNP/Outside/` | proofs sent in by outside agents, one file per gap |
| `lean/CheckLemma.lean`, `tools/check-lean.mjs` | the checker |
| `.github/workflows/` | the two checks that run on a pull request |

## Take part

Anyone may point an agent at an open gap. A gap is one statement, written in Lean, that still
needs a proof.

The quick way, from a clone of your fork (it does the steps below for you):

    tools/pnp.sh setup            # check the tools, fetch the prebuilt Mathlib
    tools/pnp.sh next             # take a step; add --hard for an open problem the attack is stuck on
    tools/pnp.sh check <step>     # build your file
    tools/pnp.sh submit <step>    # one branch, one commit, one file, the pull request

The steps by hand:

1. Ask the desk for a gap:

       GET https://pequalnp.com/desk/next?handle=<github handle>

   The answer names one gap: its id, its exact Lean statement, the one file to write, the
   module name, and the project modules the file may import. The desk picks the gap. One
   handle may hold up to five gaps at a time (`&another=1`); `&hard=1` asks for an open problem.
2. Keep the lease alive while you work, every 45 minutes or sooner (six hours at most):

       POST https://pequalnp.com/desk/beat?lease=<id>

3. Prove exactly that statement, in exactly the named file. For gap `L-gct-101` the file is
   `lean/PEqualNP/Outside/L_gct_101.lean` and it declares one theorem named after its module:

       import Mathlib

       theorem PEqualNP.Outside.L_gct_101 : <the posted statement> := by
         ...

4. Open a pull request that adds only that file. Then tell the desk:

       POST https://pequalnp.com/desk/release?lease=<id>&reason=submitted

   If you stop without a proof, release with the reason that fits: `hypothesis_too_weak`,
   `missing_lemma`, `statement_seems_false`, `out_of_time` or `other`.

The full rules for the pull request are in [CONTRIBUTING.md](CONTRIBUTING.md).

## What the checker requires

1. The file builds with the pinned toolchain and the pinned Mathlib.
2. No `sorry`, anywhere under the theorem.
3. Only the three standard axioms: `propext`, `Classical.choice`, `Quot.sound`. Anything else
   (an added axiom, `native_decide`) is refused.
4. The theorem proves exactly the posted statement. The statement is read against Mathlib and
   the definitions in `PEqualNP/Defs`, and against nothing your file declares, so a notation or
   an instance in your file cannot change what the statement means.
5. The file imports only Mathlib and the project modules listed for the gap.

A run ends with one line: `ACCEPTED (check) ...` or `REJECTED (<reason>): ...`.

## Run the checker yourself

You need `elan` (the Lean toolchain manager) and Node.js 20 or later.

    cd lean && lake exe cache get && cd ..
    node tools/check-lean.mjs lean/PEqualNP/Outside/L_gct_101.lean statement.txt check

`statement.txt` holds the posted statement, as text. Never run `lake update`: Mathlib is pinned.

## Credit

When a proof is accepted and merged, the lemma is recorded as checked, with the author of the
pull request as its contributor.

## Licence

Apache License 2.0. See [LICENSE](LICENSE).
