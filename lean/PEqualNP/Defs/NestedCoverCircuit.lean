import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs.MetaComplexityMinimal

/-!
# Nested cover circuits of a graph function

The setting. The inputs are `Fin n`; wire `i < n` is the input `x_i`, and gate number `j` of a
circuit is wire `n + j` (the circuit model of `PEqualNP.Defs.CircuitLowerBounds`). A simple graph
`K` on `Fin n` and a set `A` of inputs give the graph function
`F_(K,A) = (OR of x_a, a in A) OR (OR over edges uv of K of (x_u AND x_v))`.

The object (definition 1.1 of the nested cover note of the last-gate route). DATA: a minimum
vertex cover `T`; for every edge an OWNER, one of its ends, in `T` (`N_t` = the other ends of the
edges owned by `t`); a partial map on `T`, the TIES `s -> t`, allowed only when `t` owns the edge
`st`; for every `t` in `T` a binary OR tree `Z_t` whose leaves are `x_t` and the terms `B_s` of the
`s` tied to `t`; for every `t` and every `r` in `N_t` a leaf `lam_t(r)`: the input `x_r` if `r` is
not in `T`, and if `r` is in `T` a node of `Z_r` with `x_r` below it or equal to it (a Z-node with
centre), which must be the root of `Z_r` when `r -> t`; for every `t` a binary OR tree `O_t` on the
leaves `lam_t(r)`, `r` in `N_t`; a binary OR tree TOP on the `x_a`, `a` in `A`, and the `B_t` of the
untied `t`. THE CIRCUIT: `B_t = AND(root of Z_t, root of O_t)`, output = root of TOP; a one-leaf
tree is its leaf. A Z-node with centre may be read by several `O_t`, so gates of fan-out above
one occur.

The formal reading. This module does not generate the circuit from the data: it says when a given
circuit of the existing model IS one, by labelling every gate with its ROLE (a gate of `Z_t`, of
`O_t`, the AND `B_t`, or a gate of TOP) and checking the trees through their reads. So every tree
shape, every gate order and both operand orders are covered, and a statement "the least circuits
are exactly the nested ones" can be made on the existing circuit type without an isomorphism.

* `Kind`: the four roles of a gate.
* `NCCData n`: the data: `cover`, `owns u v` (u owns the edge uv), `tie`, `role` of each gate
  (a kind and a vertex, as a number), and the wires `bw t` of `B_t`, `zroot t`, `oroot t`, and
  `lam t r`.
* `gateAt C j`: gate number `j` (an OR with no input past the end).
* `ReadsBack n C`: every gate reads only earlier wires (the circuit is laid out in order).
* `readsIn C G w`: how many operand positions of the gates with index in `G` read wire `w`.
* `IsOrTree n C G L ρ`: the gates with index in `G` form a binary OR tree with leaf set `L` and
  root wire `ρ` (with no gate: `L = {ρ}`).
* `IsMinCover K T`: `T` is a vertex cover of least size (Mathlib's `IsVertexCover`).
* `centreFlags`, `IsCentred`: the wires that are `x_t` for `t` in the cover, or a Z gate reading
  such a wire: on a valid labelling, exactly the Z-nodes with centre.
* `gatesOf`, `topGates`, `zLeaves`, `oLeaves`, `topLeaves`: the gate index sets and leaf sets.
* `OwnerOK`, `TieOK`, `RolesOK`, `TermOK`, `LamOK`: the conditions on the data.
* `Valid n K A C d`, `IsNestedCoverCircuit n K A C`: `C` is a nested cover circuit of `(K, A)`.
* `graphFun K A`: the graph function `F_(K,A)` on `n` inputs.

Caveats a statement must respect.
* `A` should be disjoint from the vertices of `K` that carry an edge (the concept says "further
  inputs"); nothing here enforces it, and the size `|A| + |E| + |T| - 1` and the theorems of the
  note assume it.
* With no edge and `A` empty, TOP has no leaf and NO circuit is nested (the function is `false`).
* The definition does not say that the circuit computes `F_(K,A)`: that is a theorem of the note
  (1.4), valid when no cycle of `K` lies in a minimum cover. Without that hypothesis the ties may
  be cyclic, which `ReadsBack` rules out, so nothing cyclic is ever nested.
* `role` of a TOP gate carries a vertex number that is ignored; `bw`, `zroot`, `oroot`, `lam` are
  determined by the rest on a valid labelling (they are data only to keep the conditions local).
* A vertex `t` is the wire `t.val`; vertex numbers in `role` are plain numbers compared with
  `t.val`.
-/

namespace PEqualNP.MetaComplexity.NestedCover

open PEqualNP.CircuitLowerBounds

/-- The role of a gate in a nested cover circuit. -/
inductive Kind where
  /-- An OR gate of the tree `Z_t`. -/
  | z
  /-- An OR gate of the tree `O_t`. -/
  | o
  /-- The AND gate `B_t`. -/
  | b
  /-- An OR gate of the tree TOP. -/
  | top
  deriving DecidableEq

/-- The data of a nested cover circuit on `n` inputs, read against a circuit. -/
structure NCCData (n : ℕ) where
  /-- The minimum vertex cover `T`. -/
  cover : Finset (Fin n)
  /-- `owns u v`: `u` is the owner of the edge `uv`. -/
  owns : Fin n → Fin n → Bool
  /-- The ties: `tie s = some t` is `s -> t`. -/
  tie : Fin n → Option (Fin n)
  /-- The role of gate number `j`: a kind and a vertex number (ignored for TOP). -/
  role : ℕ → Kind × ℕ
  /-- The wire of the term `B_t`. -/
  bw : Fin n → ℕ
  /-- The wire of the root of `Z_t`. -/
  zroot : Fin n → ℕ
  /-- The wire of the root of `O_t`. -/
  oroot : Fin n → ℕ
  /-- `lam t r`: the wire `O_t` reads for its owned neighbour `r`. -/
  lam : Fin n → Fin n → ℕ

/-- Gate number `j` of `C` (an OR gate with no input past the end of the list). -/
def gateAt (C : Circuit) (j : ℕ) : Gate :=
  C.gates.getD j ⟨GateOp.or, []⟩

/-- Every gate reads only earlier wires: gate `j` (wire `n + j`) reads wires below `n + j`. -/
def ReadsBack (n : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j

/-- The number of operand positions of the gates with index in `G` that read wire `w`. -/
def readsIn (C : Circuit) (G : Finset ℕ) (w : ℕ) : ℕ :=
  ∑ j ∈ G, (gateAt C j).inputs.count w

/-- The gates with index in `G` form a binary OR tree with leaf set `L` and root wire `ρ`: each is
an OR gate of two operands, each operand a leaf or a gate of `G`; no leaf is a gate of `G`; every
leaf and every gate of `G` is read exactly once inside `G`, except the root, read never; with no
gate, `L` is the single leaf `ρ`, otherwise `ρ` is a gate of `G`. Together with `ReadsBack` this
is exactly a binary tree in which each leaf occurs once. -/
def IsOrTree (n : ℕ) (C : Circuit) (G L : Finset ℕ) (ρ : ℕ) : Prop :=
  (∀ j ∈ G, (gateAt C j).op = GateOp.or ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ i ∈ (gateAt C j).inputs, i ∈ L ∨ (n ≤ i ∧ i - n ∈ G)) ∧
    (∀ w ∈ L, ¬ (n ≤ w ∧ w - n ∈ G) ∧ readsIn C G w = (if w = ρ then 0 else 1)) ∧
    (∀ j ∈ G, readsIn C G (n + j) = (if n + j = ρ then 0 else 1)) ∧
    (if G = ∅ then L = {ρ} else ∃ j ∈ G, ρ = n + j)

/-- `T` is a minimum vertex cover of `K`: a vertex cover (Mathlib's `IsVertexCover`) with no
vertex cover of smaller size. -/
def IsMinCover {n : ℕ} (K : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  K.IsVertexCover (T : Set (Fin n)) ∧
    ∀ T' : Finset (Fin n), K.IsVertexCover (T' : Set (Fin n)) → T.card ≤ T'.card

/-- The gate indices of role `(k, t)`. -/
def gatesOf {n : ℕ} (d : NCCData n) (C : Circuit) (k : Kind) (t : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => d.role j = (k, t))

/-- The gate indices of TOP. -/
def topGates {n : ℕ} (d : NCCData n) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => (d.role j).1 = Kind.top)

/-- The leaves of `Z_t`: `x_t` and the terms `B_s` of the `s` tied to `t`. -/
def zLeaves {n : ℕ} (d : NCCData n) (t : Fin n) : Finset ℕ :=
  insert t.val ((d.cover.filter (fun s => d.tie s = some t)).image d.bw)

/-- The leaves of `O_t`: the wires `lam t r`, `r` owned by `t`. -/
def oLeaves {n : ℕ} (d : NCCData n) (t : Fin n) : Finset ℕ :=
  (Finset.univ.filter (fun r => d.owns t r = true)).image (d.lam t)

/-- The leaves of TOP: the `x_a`, `a` in `A`, and the terms `B_t` of the untied `t`. -/
def topLeaves {n : ℕ} (d : NCCData n) (A : Finset (Fin n)) : Finset ℕ :=
  A.image Fin.val ∪ (d.cover.filter (fun t => d.tie t = none)).image d.bw

/-- One flag per wire: an input is flagged iff it is in the cover; a gate iff its role is a Z
role and it reads a flagged wire. On a valid labelling the flagged wires are the Z-nodes with
centre. Same fold as `Circuit.wires`. -/
def centreFlags (n : ℕ) (C : Circuit) (d : NCCData n) : List Bool :=
  C.gates.foldl
    (fun w g => w ++ [decide ((d.role (w.length - n)).1 = Kind.z) &&
      g.inputs.any (fun i => w.getD i false)])
    (List.ofFn fun i : Fin n => decide (i ∈ d.cover))

/-- Wire `w` is flagged by `centreFlags`. -/
def IsCentred (n : ℕ) (C : Circuit) (d : NCCData n) (w : ℕ) : Prop :=
  (centreFlags n C d).getD w false = true

/-- Owners: only an adjacent cover vertex owns an edge, and every edge has exactly one owner. -/
def OwnerOK {n : ℕ} (K : SimpleGraph (Fin n)) (d : NCCData n) : Prop :=
  (∀ u v, d.owns u v = true → K.Adj u v ∧ u ∈ d.cover) ∧
    ∀ u v, K.Adj u v → d.owns u v ≠ d.owns v u

/-- Ties: `s -> t` only for `s` in the cover and `t` the owner of the edge `ts`. -/
def TieOK {n : ℕ} (d : NCCData n) : Prop :=
  ∀ s t, d.tie s = some t → s ∈ d.cover ∧ d.owns t s = true

/-- Every gate has a role: TOP, or a role of a cover vertex `t`; a `B` role of `t` sits at the
wire `bw t` (so there is at most one per `t`). -/
def RolesOK (n : ℕ) (C : Circuit) (d : NCCData n) : Prop :=
  ∀ j < C.gates.length, (d.role j).1 = Kind.top ∨
    ∃ t ∈ d.cover, (d.role j).2 = t.val ∧ ((d.role j).1 = Kind.b → d.bw t = n + j)

/-- The term of `t`: the gate at wire `bw t` has role `B` of `t` and is the AND of the roots of
`Z_t` and `O_t`, in either order. -/
def TermOK (n : ℕ) (C : Circuit) (d : NCCData n) (t : Fin n) : Prop :=
  ∃ j < C.gates.length, d.bw t = n + j ∧ d.role j = (Kind.b, t.val) ∧
    (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [d.zroot t, d.oroot t] ∨ (gateAt C j).inputs = [d.oroot t, d.zroot t])

/-- The leaf `lam t r`: `x_r` for `r` outside the cover; for `r` in the cover a Z-node of `r`
with centre (`x_r` itself or a flagged gate of role `Z` of `r`), the root of `Z_r` if `r -> t`. -/
def LamOK (n : ℕ) (C : Circuit) (d : NCCData n) (t r : Fin n) : Prop :=
  if r ∈ d.cover then
    IsCentred n C d (d.lam t r) ∧
      (d.lam t r = r.val ∨ ∃ j < C.gates.length, d.lam t r = n + j ∧ d.role j = (Kind.z, r.val)) ∧
      (d.tie r = some t → d.lam t r = d.zroot r)
  else d.lam t r = r.val

/-- The data `d` labels `C` as a nested cover circuit of `(K, A)`. -/
def Valid (n : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit)
    (d : NCCData n) : Prop :=
  ReadsBack n C ∧ IsMinCover K d.cover ∧ OwnerOK K d ∧ TieOK d ∧ RolesOK n C d ∧
    (∀ t ∈ d.cover, TermOK n C d t ∧
      IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t) ∧
      IsOrTree n C (gatesOf d C Kind.o t.val) (oLeaves d t) (d.oroot t) ∧
      ∀ r, d.owns t r = true → LamOK n C d t r) ∧
    IsOrTree n C (topGates d C) (topLeaves d A) C.output

/-- `C` is a nested cover circuit of `(K, A)` on `n` inputs (definition 1.1 of the note). -/
def IsNestedCoverCircuit (n : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (C : Circuit) : Prop :=
  ∃ d : NCCData n, Valid n K A C d

/-! ## Decidability, so that small rows can be checked by `decide` -/

/-- Equality of gate operations is decidable. Not a global instance (the circuit module does not
declare one); it is made a local instance for the instances below. -/
@[instance_reducible]
def gateOpDecEq : DecidableEq GateOp := by
  intro a b
  cases a <;> cases b <;>
    first
    | exact isTrue rfl
    | (rename_i m m'
       exact if h : m = m' then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl)))
    | exact isFalse (by intro h; cases h)

attribute [local instance] gateOpDecEq

instance (n : ℕ) (C : Circuit) : Decidable (ReadsBack n C) := by
  unfold ReadsBack; infer_instance

instance (n : ℕ) (C : Circuit) (G L : Finset ℕ) (ρ : ℕ) : Decidable (IsOrTree n C G L ρ) := by
  unfold IsOrTree; infer_instance

instance {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (T : Finset (Fin n)) :
    Decidable (IsMinCover K T) :=
  inferInstanceAs (Decidable ((∀ v w : Fin n, K.Adj v w → v ∈ T ∨ w ∈ T) ∧
    ∀ T' : Finset (Fin n), (∀ v w : Fin n, K.Adj v w → v ∈ T' ∨ w ∈ T') → T.card ≤ T'.card))

instance (n : ℕ) (C : Circuit) (d : NCCData n) (w : ℕ) : Decidable (IsCentred n C d w) := by
  unfold IsCentred; infer_instance

instance {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (d : NCCData n) :
    Decidable (OwnerOK K d) := by
  unfold OwnerOK; infer_instance

instance {n : ℕ} (d : NCCData n) : Decidable (TieOK d) := by
  unfold TieOK; infer_instance

instance (n : ℕ) (C : Circuit) (d : NCCData n) : Decidable (RolesOK n C d) := by
  unfold RolesOK; infer_instance

instance (n : ℕ) (C : Circuit) (d : NCCData n) (t : Fin n) : Decidable (TermOK n C d t) := by
  unfold TermOK; infer_instance

instance (n : ℕ) (C : Circuit) (d : NCCData n) (t r : Fin n) : Decidable (LamOK n C d t r) := by
  unfold LamOK; infer_instance

instance (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
    (C : Circuit) (d : NCCData n) : Decidable (Valid n K A C d) := by
  unfold Valid; infer_instance

/-- The graph function `F_(K,A)`: some `x_a`, `a` in `A`, is true, or both ends of some edge. -/
def graphFun {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true) || decide (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)

end PEqualNP.MetaComplexity.NestedCover
