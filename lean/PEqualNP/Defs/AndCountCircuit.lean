import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic

/-!
# AND-count circuits on a vertex set

The monotone circuits of the AND-count family (cover-bound rows), with OR free. An AND-count
circuit on the vertex set `Fin n` is a list of `size` gates, each the AND of two SIDES. A side
is a pair `(B, F)`: a finite set `B` of vertices (its bare variables) and a finite set `F` of
gates (it reads gate `j` as an OR summand). The output is the OR of a set of vertices and a set
of gates. Value at a set `U` of true variables: a side is true iff `B` meets `U` or some gate
of `F` is true; a gate is true iff both its sides are; the circuit is true iff some output
vertex lies in `U` or some output gate is true. The size is the number of gates, i.e. the
number of AND gates (OR costs nothing).

The circuit COMPUTES the edge function of a graph `G` if its value at `U` is true exactly when
`U` contains both ends of an edge.

* `AndCountCircuit n`: the data (size, the two sides of each gate, the output).
* `AndCountCircuit.WellFormed`: every gate read by a side of gate `i` comes before `i`.
* `AndCountCircuit.sideTrue`, `AndCountCircuit.gateValFuel`, `AndCountCircuit.gateVal`: the
  value of a side, of a gate (by recursion on a fuel bounded by the size), at a set `U`.
* `AndCountCircuit.eval`: the value of the circuit at `U`.
* `AndCountCircuit.Computes`: the circuit computes the edge function of `G`.
* `AndCountCircuit.starCircuit`: the star circuit of a vertex set `T`, one gate per member
  `t` with sides `({t}, none)` and `(N(t), none)`, every gate an output.

Caveats for statements.
* Only `WellFormed` circuits are circuits. The evaluator reads gate `j` from gate `i` only
  when `j < i` (a later or equal index named by a side is ignored, not an error), so a
  statement about circuits must assume `WellFormed`: a gate naming a later gate is the
  thinker's non-circuit.
* The output may name vertices as well as gates (the normal form of the filer, rows L-meta-349
  ff., with `OV` and `OG`). A circuit computing the edge function of any graph has no output
  vertex (the singleton of that vertex contains no edge), so for computing circuits this is the
  thinker's "set of output gates". The output set is NOT required to be nonempty: the empty
  circuit (size 0, empty output) computes the edge function of an edgeless graph, and is the
  star circuit of the empty cover.
* Sides may be empty, may repeat a vertex, and the two sides of a gate may share vertices; no
  normal form (nonempty, disjoint, unit-free) is built in. State such hypotheses explicitly.
* Size is `size`, the AND count; it is not the gate count of `Defs/CircuitLowerBounds`.
* No 4-cycle condition is built in: on the 4-cycle one gate computes the edge function while
  the cover number is 2, so the family's statements assume girth at least 5 themselves.
-/

namespace PEqualNP.AndCount

/-- An AND-count circuit on the vertex set `Fin n`: `size` gates, gate `i` the AND of the
side `(leftVars i, leftGates i)` and the side `(rightVars i, rightGates i)`; the output is the
OR of the vertices `outVars` and the gates `outGates`. -/
structure AndCountCircuit (n : ℕ) where
  /-- The number of gates (AND gates). -/
  size : ℕ
  /-- The bare variables of the first side of each gate. -/
  leftVars : Fin size → Finset (Fin n)
  /-- The gates read by the first side of each gate. -/
  leftGates : Fin size → Finset (Fin size)
  /-- The bare variables of the second side of each gate. -/
  rightVars : Fin size → Finset (Fin n)
  /-- The gates read by the second side of each gate. -/
  rightGates : Fin size → Finset (Fin size)
  /-- The vertices read by the output OR. -/
  outVars : Finset (Fin n)
  /-- The gates read by the output OR. -/
  outGates : Finset (Fin size)

namespace AndCountCircuit

variable {n : ℕ}

/-- Well-formed: each side of gate `i` reads only gates `j < i`. -/
def WellFormed (C : AndCountCircuit n) : Prop :=
  ∀ i : Fin C.size, (∀ j ∈ C.leftGates i, j < i) ∧ (∀ j ∈ C.rightGates i, j < i)

/-- The value of the side `(B, F)` of gate `i` at `U`, given the values `val` of the gates:
`B` meets `U`, or some gate `j ∈ F` with `j < i` is true. -/
def sideTrue {k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val : Fin k → Bool) : Bool :=
  decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true)

/-- The gate values at `U` computed with fuel `d` (fuel `0` gives `false`). Fuel `C.size`
suffices, since only earlier gates are read. -/
def gateValFuel (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ℕ → Fin C.size → Bool
  | 0, _ => false
  | d + 1, i =>
      sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d)

/-- The value of gate `i` at the set `U` of true variables. -/
def gateVal (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  gateValFuel C U C.size i

/-- The value of the circuit at `U`: some output vertex is in `U` or some output gate is
true. -/
def eval (C : AndCountCircuit n) (U : Finset (Fin n)) : Bool :=
  decide ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true)

/-- `C` computes the edge function of `G`: its value at `U` is true exactly when `U`
contains both ends of an edge of `G`. -/
def Computes (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ U : Finset (Fin n), C.eval U = true ↔ ∃ a ∈ U, ∃ c ∈ U, G.Adj a c

/-- The star circuit of a vertex set `T`: gate `j` belongs to the `j`-th member `t` of `T` in
increasing order, with sides `({t}, none)` and `(N(t), none)`; every gate is an output. -/
def starCircuit (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) :
    AndCountCircuit n where
  size := T.card
  leftVars j := {T.orderEmbOfFin rfl j}
  leftGates _ := ∅
  rightVars j := Finset.univ.filter (fun w => G.Adj (T.orderEmbOfFin rfl j) w)
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

end AndCountCircuit

end PEqualNP.AndCount
