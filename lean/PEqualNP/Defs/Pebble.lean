import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.List.Chain
import Mathlib.Logic.Relation

/-!
# Pebble games on gate graphs

The black pebble game and the matching game (called the determination game in
`routes/evasion/OBJECTS.md`, sections 1 and 2) on gate graphs. This module records no result;
it holds only the definitions a statement needs.

* `GateGraph n`: a directed acyclic graph on the vertices `Fin n` in which every vertex is a
  source or has exactly two predecessors, both of smaller index and distinct from each other.
* `GateGraph.gate`, `GateGraph.Edge`, `GateGraph.Desc`: the gate of a vertex (the vertex and
  its two predecessors), the predecessor relation and its reflexive transitive closure.
* `GateGraph.BlackMove`, `GateGraph.MatchMoveWith`, `GateGraph.MatchMove`: the moves of the two
  games, from a kept set `R` placing a set `U`.
* `Step M P Q`: from the configuration `P`, keep a subset, then make one move of `M`.
* `PriceLe M x w`: some play of `M` from the empty configuration reaches `x` with every
  configuration of size at most `w`.
* `RunLink`, `GateGraph.Run`: a run of matching moves from a configuration, each move with its
  matching recorded.

A configuration is a `Finset (Fin n)`; its size is its number of elements, sources counted.
-/

namespace PEqualNP.Pebble

/-- A gate graph on the vertices `Fin n`. `src v` says whether `v` is a source. A vertex `v`
that is not a source has the two predecessors `p v` and `q v`, both of index smaller than `v`
and distinct from each other. At a source, `p v` and `q v` are arbitrary and are never read by
the definitions below except inside `gate`, whose value at a source is never used. -/
structure GateGraph (n : ℕ) where
  /-- `src v = true` iff `v` is a source. -/
  src : Fin n → Bool
  /-- The first predecessor of a non-source. -/
  p : Fin n → Fin n
  /-- The second predecessor of a non-source. -/
  q : Fin n → Fin n
  /-- The first predecessor of a non-source has smaller index. -/
  p_lt : ∀ v, src v = false → p v < v
  /-- The second predecessor of a non-source has smaller index. -/
  q_lt : ∀ v, src v = false → q v < v
  /-- The two predecessors of a non-source are distinct. -/
  p_ne : ∀ v, src v = false → p v ≠ q v

namespace GateGraph

variable {n : ℕ} (G : GateGraph n)

/-- The gate of `v`: the set `{v, p v, q v}`. At a non-source it has exactly three elements. At
a source it is a set of no meaning, and every use below reads it only at non-sources. -/
def gate (v : Fin n) : Finset (Fin n) := {v, G.p v, G.q v}

/-- `Edge u v`: `v` is not a source and `u` is one of its two predecessors (`u = p v` or
`u = q v`). The edge points from the predecessor `u` to `v`. -/
def Edge (u v : Fin n) : Prop := G.src v = false ∧ (u = G.p v ∨ u = G.q v)

/-- `Desc a d`: `d` is `a` itself or a descendant of `a`, that is, a path of zero or more edges
leads from `a` to `d`. -/
def Desc (a d : Fin n) : Prop := Relation.ReflTransGen G.Edge a d

/-- A black move from the kept set `R` placing the set `U`: `U` is a single vertex `v` that is
not in `R`, and either `v` is a source (placed freely) or both predecessors of `v` are in `R`. -/
def BlackMove (R U : Finset (Fin n)) : Prop :=
  ∃ v, U = {v} ∧ v ∉ R ∧ (G.src v = true ∨ (G.p v ∈ R ∧ G.q v ∈ R))

/-- A matching move from the kept set `R` placing the set `U`, with the matching `φ`:
* `U` is disjoint from `R`;
* every placed non-source `u` (in `U`, not a source) has as head `φ u` a non-source whose gate
  contains `u` and lies inside `R ∪ U`;
* the heads are distinct on the placed non-sources (`φ` is injective there).

Placed sources need nothing: they are free, and `φ` is not read at them. The empty placed set
is a legal move from every kept set, with every `φ` (a pure removal, once `Step` has dropped
vertices). -/
def MatchMoveWith (R U : Finset (Fin n)) (φ : Fin n → Fin n) : Prop :=
  Disjoint R U ∧
  (∀ u ∈ U, G.src u = false → G.src (φ u) = false ∧ u ∈ G.gate (φ u) ∧ G.gate (φ u) ⊆ R ∪ U) ∧
  Set.InjOn φ ↑(U.filter (fun u => G.src u = false))

/-- A matching move from the kept set `R` placing the set `U`: `MatchMoveWith R U φ` for some
matching `φ`. The empty placed set is a legal move (a pure removal). -/
def MatchMove (R U : Finset (Fin n)) : Prop := ∃ φ, G.MatchMoveWith R U φ

end GateGraph

variable {n : ℕ}

/-- One step of a play of the move relation `M` (one of `G.BlackMove`, `G.MatchMove`), from the
configuration `P` to the configuration `Q`: keep any subset `R` of `P` (the removed vertices are
those of `P` not in `R`), then make one move `M R U`; the new configuration is `Q = R ∪ U`. -/
def Step (M : Finset (Fin n) → Finset (Fin n) → Prop) (P Q : Finset (Fin n)) : Prop :=
  ∃ R U, R ⊆ P ∧ M R U ∧ Q = R ∪ U

/-- `PriceLe M x w`: some play of `M` from the empty configuration reaches `x` with at most `w`
pebbles. Precisely: there is a list `L` of configurations such that consecutive configurations
of `∅ :: L` are joined by `Step M`, some configuration of `L` contains `x`, and every
configuration of `L` has at most `w` elements. Since a step's new configuration is `R ∪ U`
with everything placed at once, the size during a move counts in full: placements cannot be
slid one by one to save a pebble. -/
def PriceLe (M : Finset (Fin n) → Finset (Fin n) → Prop) (x : Fin n) (w : ℕ) : Prop :=
  ∃ L : List (Finset (Fin n)), List.IsChain (Step M) (∅ :: L) ∧ (∃ K ∈ L, x ∈ K) ∧ ∀ K ∈ L, K.card ≤ w

/-- The link between consecutive entries `(R, U, φ)` of a run of matching moves: the kept set of
the later entry `b` lies inside the configuration `R ∪ U` left by the earlier entry `a`. -/
def RunLink (a b : Finset (Fin n) × Finset (Fin n) × (Fin n → Fin n)) : Prop := b.1 ⊆ a.1 ∪ a.2.1

namespace GateGraph

variable (G : GateGraph n)

/-- A run of matching moves from the configuration `P`: a list `l` of entries `(R, U, φ)`, each a
matching move `MatchMoveWith R U φ`, such that the first kept set lies inside `P` and each later
kept set lies inside the configuration `R ∪ U` left by the entry before it. Formally the list is
anchored at the entry `(P, ∅, id)`, which stands for the starting configuration. -/
def Run (P : Finset (Fin n)) (l : List (Finset (Fin n) × Finset (Fin n) × (Fin n → Fin n))) : Prop :=
  List.IsChain RunLink ((P, ∅, id) :: l) ∧ ∀ m ∈ l, G.MatchMoveWith m.1 m.2.1 m.2.2

end GateGraph

end PEqualNP.Pebble
