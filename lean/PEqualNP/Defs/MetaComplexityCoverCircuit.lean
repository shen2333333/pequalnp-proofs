import PEqualNP.Defs.MetaComplexityMinimal

/-!
# The cover circuit, for the meta-complexity program

An explicit circuit for the function "some owner `t` is true together with one of the inputs on
its list": for each owner one block of gates (a chain of ORs over its list, then one AND with the
owner), and one more OR per block after the first, joining the blocks. With owners the members
of a vertex cover and each edge listed at one of its ends in the cover, this is a circuit for
the edge function of the graph with (number of edges) + (number of owners) - 1 gates when every
owner list is nonempty. It has no NOT gate. Owners with an empty list are skipped.

The gate list is a function of the number of inputs and of the owner lists alone, so it can be
written down by a machine: this is the circuit the reduction to the last-gate problem outputs.
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-- The block of one owner `t` with list `v1 :: rest`, placed from wire `B` on: `rest.length`
OR gates accumulating `v1, rest`, then the AND of `t` with the accumulated OR, then, unless this
is the leading block, one OR joining the AND with wire `a` (the output of the blocks before). -/
def blockGates (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) : List Gate :=
  (List.range rest.length).map (fun i =>
      ⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩) ++
    ⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩ ::
      (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩])

/-- The gates of all blocks, placed from wire `B` on. `lead` says whether the next nonempty
block is the first one; `a` is the wire holding the output of the blocks before. An owner with
an empty list contributes no gate. -/
def coverGatesB (B : ℕ) (lead : Bool) (a : ℕ) : List (ℕ × List ℕ) → List Gate
  | [] => []
  | (_, []) :: os => coverGatesB B lead a os
  | (t, v1 :: rest) :: os =>
      blockGates B a t v1 rest lead ++
        coverGatesB (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) os

/-- The cover circuit on `n` inputs for the owner lists `own`: the gates of all blocks, placed
from wire `n` on, with the last gate as output. With no gate at all it is the circuit with no
gate whose output wire does not exist, the constant `false`. -/
def coverCircuitB (n : ℕ) (own : List (ℕ × List ℕ)) : Circuit :=
  if coverGatesB n true 0 own = [] then ⟨[], n⟩
  else ⟨coverGatesB n true 0 own, n + (coverGatesB n true 0 own).length - 1⟩

end PEqualNP.MetaComplexity
