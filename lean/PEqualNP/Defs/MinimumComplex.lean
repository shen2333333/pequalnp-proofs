import Mathlib.Logic.Relation
import Mathlib.Order.Nat
import PEqualNP.Defs.MetaComplexityMinimal

/-!
# The minimum complex of a Boolean function

Circuits are the root circuits of `PEqualNP.Defs.CircuitLowerBounds` (straight-line programs,
wires `0` to `n - 1` are the inputs, gate number `j` produces wire `n + j`), restricted to the
STRICT model of this concept: every gate is an AND or an OR reading exactly two distinct earlier
wires, or a NOT reading exactly one earlier wire. Every gate counts, inputs are free. A circuit
computes `f` when it is strict, its output is one of its wires, and its value is `f`.

A minimum circuit of `f` determines the SET of functions its gates compute (its gate set). The
MINIMUM COMPLEX `M(f)` is the simplicial complex whose maximal faces (facets) are exactly the
gate sets of the minimum circuits of `f`. It is represented by PREDICATES on finite sets of
functions: `IsFacet n f S` (maximal faces) and `IsFace n f S` (all faces); vertices are the
useful functions. A vertex is FORCED when it lies in every facet; the REDUCED complex deletes the
forced vertices from every facet.

The ONE-ABOVE family `M_1(f)`: gate sets of strict circuits of `f` with `cc f + 1` gates whose
gate functions are pairwise distinct, none an input and none a constant. Such a set is PADDED if
it contains a facet of `M(f)`. Two one-above sets are joined at window `k` when they share at
least `cc f + 1 - k` functions (one step replaces at most `k` functions). The ESCAPE WINDOW is
the least `k` such that from every one-above set some padded one is reached by such steps.

* `BoolFun n`: Boolean functions of `n` inputs.
* `StrictGate w g`, `Strict n C`: the gate model (AND, OR on two distinct earlier wires, NOT on
  one), as a condition on root circuits.
* `Computes n f C`: `C` is strict, its output is a wire, and it computes `f`.
* `cc n f`: the least size of a circuit computing `f`.
* `IsMinCircuit n f C`: `C` computes `f` and no circuit computing `f` is smaller.
* `gateFun n C j`, `gateSet n C`: the function of gate `j`, the set of all gate functions.
* `IsFacet n f S`, `IsFace n f S`, `IsUseful n f g`: facets, faces and vertices of `M(f)`.
* `IsForced n f g`: a vertex lying in every facet.
* `IsReducedFacet n f R`: `R` is a facet with the forced vertices removed.
* `IsInputFun n g`, `IsConstFun g`: trivial functions.
* `IsOneAboveFacet n f S`, `IsPadded n f S`: the one-above family and its padded sets.
* `FlipAdj n f k S T`: one-above sets sharing at least `cc f + 1 - k` functions.
* `EscapesWithin n f k`, `escapeWindow n f`: every one-above set reaches a padded one at
  window `k`; the least such `k`.

Caveats a statement must respect.
* The intended hypothesis is that `f` is neither constant nor an input. For an input `f` the
  minimum circuit has no gate and the only facet is the empty set. For `n = 0` no circuit has a
  wire, nothing computes anything and `cc` is `sInf` of the empty set, that is `0`.
* A facet is a set of FUNCTIONS, not a circuit: circuits with different wiring may give the same
  facet, and duplicate gate functions collapse in `gateSet` (they do not occur in minimum
  circuits of non-constant non-input functions, a paper fact not stated here).
* `cc` and `escapeWindow` are `sInf` of sets of naturals: `0` when the set is empty (`escapeWindow`
  is also `0` when the one-above family is empty).
* `IsReducedFacet` of a rigid function (one facet) is the empty set, the empty face.
-/

namespace PEqualNP.MinimumComplex

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The Boolean functions of `n` inputs. -/
abbrev BoolFun (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- The gate `g`, placed where `w` wires exist (wires `0` to `w - 1`), is strict: an AND or an
OR reading exactly two distinct existing wires, or a NOT reading exactly one existing wire. -/
def StrictGate (w : ℕ) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
      ∀ i ∈ g.inputs, i < w) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1 ∧ ∀ i ∈ g.inputs, i < w)

/-- The circuit `C` on `n` inputs is strict: gate number `j` (wire `n + j`) is a strict gate
reading only the `n + j` wires before it. -/
def Strict (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (h : j < C.gates.length), StrictGate (n + j) C.gates[j]

/-- `C` computes `f` on `n` inputs in the strict model: `C` is strict, its output is one of its
wires (an input or a gate), and its value on every input is that of `f`. -/
def Computes (n : ℕ) (f : BoolFun n) (C : Circuit) : Prop :=
  Strict n C ∧ C.output < n + C.size ∧ circuitFun n C = f

/-- The circuit complexity of `f` in the strict model: the least size of a circuit computing
it (`0` if none does, which happens only for `n = 0`). -/
noncomputable def cc (n : ℕ) (f : BoolFun n) : ℕ :=
  sInf {s | ∃ C : Circuit, Computes n f C ∧ C.size = s}

/-- `C` is a minimum circuit of `f`: it computes `f` and every circuit computing `f` has at least
as many gates. -/
def IsMinCircuit (n : ℕ) (f : BoolFun n) (C : Circuit) : Prop :=
  Computes n f C ∧ ∀ D : Circuit, Computes n f D → C.size ≤ D.size

/-- The function computed by gate number `j` of `C` (wire `n + j`) on `n` inputs. -/
def gateFun (n : ℕ) (C : Circuit) (j : ℕ) : BoolFun n :=
  fun x => (C.wires (List.ofFn x)).getD (n + j) false

/-- The gate set of `C` on `n` inputs: the set of the functions its gates compute. -/
def gateSet (n : ℕ) (C : Circuit) : Finset (BoolFun n) :=
  (Finset.range C.size).image (gateFun n C)

/-- `S` is a facet (maximal face) of the minimum complex `M(f)`: the gate set of a minimum
circuit of `f`. -/
def IsFacet (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  ∃ C : Circuit, IsMinCircuit n f C ∧ gateSet n C = S

/-- `S` is a face of `M(f)`: a subset of a facet. -/
def IsFace (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  ∃ T, IsFacet n f T ∧ S ⊆ T

/-- `g` is a vertex of `M(f)` (a useful function of `f`): it lies in some facet. -/
def IsUseful (n : ℕ) (f : BoolFun n) (g : BoolFun n) : Prop :=
  ∃ S, IsFacet n f S ∧ g ∈ S

/-- `g` is a forced vertex of `M(f)`: a vertex lying in every facet. -/
def IsForced (n : ℕ) (f : BoolFun n) (g : BoolFun n) : Prop :=
  IsUseful n f g ∧ ∀ S, IsFacet n f S → g ∈ S

/-- `R` is a facet of the reduced complex: some facet of `M(f)` with its forced vertices
removed. -/
def IsReducedFacet (n : ℕ) (f : BoolFun n) (R : Finset (BoolFun n)) : Prop :=
  ∃ S, IsFacet n f S ∧ ∀ g, g ∈ R ↔ g ∈ S ∧ ¬ IsForced n f g

/-- `g` is an input: `g x = x i` for some `i`. -/
def IsInputFun (n : ℕ) (g : BoolFun n) : Prop :=
  ∃ i : Fin n, g = fun x => x i

/-- `g` is a constant function. -/
def IsConstFun {n : ℕ} (g : BoolFun n) : Prop :=
  ∃ b : Bool, g = fun _ => b

/-- `S` is a facet of the one-above family `M_1(f)`: the gate set of a strict circuit computing
`f` with `cc f + 1` gates whose gate functions are pairwise distinct (as many functions as
gates), none an input and none a constant. -/
def IsOneAboveFacet (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  ∃ C : Circuit, Computes n f C ∧ C.size = cc n f + 1 ∧ (gateSet n C).card = C.size ∧
    (∀ g ∈ gateSet n C, ¬ IsInputFun n g ∧ ¬ IsConstFun g) ∧ gateSet n C = S

/-- A one-above set is padded when it contains a facet of `M(f)`. -/
def IsPadded (n : ℕ) (f : BoolFun n) (S : Finset (BoolFun n)) : Prop :=
  IsOneAboveFacet n f S ∧ ∃ T, IsFacet n f T ∧ T ⊆ S

/-- The flip graph of `M_1(f)` at window `k`: two one-above sets sharing at least
`cc f + 1 - k` functions (one step replaces at most `k` functions). -/
def FlipAdj (n : ℕ) (f : BoolFun n) (k : ℕ) (S T : Finset (BoolFun n)) : Prop :=
  IsOneAboveFacet n f S ∧ IsOneAboveFacet n f T ∧ cc n f + 1 ≤ (S ∩ T).card + k

/-- At window `k` every one-above set reaches a padded one by flip steps. -/
def EscapesWithin (n : ℕ) (f : BoolFun n) (k : ℕ) : Prop :=
  ∀ S, IsOneAboveFacet n f S →
    ∃ T, Relation.ReflTransGen (FlipAdj n f k) S T ∧ IsPadded n f T

/-- The escape window of `f`: the least window at which every one-above set reaches a padded
one (`0` if there is none, by `sInf`). -/
noncomputable def escapeWindow (n : ℕ) (f : BoolFun n) : ℕ :=
  sInf {k | EscapesWithin n f k}

end PEqualNP.MinimumComplex
