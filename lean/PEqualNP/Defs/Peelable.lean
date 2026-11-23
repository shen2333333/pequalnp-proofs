import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Peelable graphs

A finite simple graph on `Fin n` is PEELABLE if every induced subgraph with at least one edge has
a GOOD LEAF or a RUN of six. Both local shapes are the ones the last-gate line of the
meta-complexity work peels in its induction (a leaf step and a deep step), so a peelable graph is
one on which that induction never gets stuck.

* `delVerts G X`: the graph `G` with every edge that has an end in `X` deleted. The vertex type is
  kept (`Fin n`), so the vertices of `X` stay as isolated vertices. This is the induced subgraph on
  the complement of `X`, padded with isolated vertices.
* `GoodLeaf G`: a leaf `l` (its only neighbour is `p`) such that `p` has at most one neighbour
  besides `l`, or `p` has a second leaf `l' ≠ l`.
* `IsRun G a' a s t b b'`: six distinct vertices forming the path `a' - a - s - t - b - b'`, where
  `a, s, t, b` have exactly their two path neighbours as neighbours, and `a'` (resp. `b'`) has at
  most one neighbour besides `a` (resp. `b`). That one further neighbour may lie on the path (for
  example `a'` adjacent to `b'`, as in the 6-cycle).
* `HasPeel G`: if `G` has an edge, then `G` has a good leaf or a run.
* `Peelable G`: `HasPeel (delVerts G X)` for every vertex set `X`.

Caveats a statement must respect.

* The arity is fixed: an induced subgraph is `delVerts G X` on the same `Fin n`, never a graph on
  a smaller vertex type. Isolated vertices change neither `GoodLeaf` nor `IsRun`, so this is the
  same notion as quantifying over induced subgraphs `G.induce S`.
* In `IsRun`, the clause for an end counts EVERY neighbour other than its inner path neighbour,
  including a neighbour on the path. So "at most one neighbour off the path" is read as "at most
  one neighbour besides `a`" (resp. `b`): an end adjacent to the other end AND to a vertex off the
  path has two, and is not allowed.
* The good leaf and the run are the helper notions of the full-basis bound of the meta-complexity
  line, word for word (the run there is a structure with these six fields); they agree with these
  by a short proof, and that line's class hypotheses (closure under `delVerts`, and the dichotomy
  at every graph with an edge) hold for `Peelable`.
-/

namespace PEqualNP.Library.Peel

/-- The graph with every edge that has an end in `X` deleted, the vertex type kept. -/
def delVerts {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := G.Adj i j ∧ i ∉ X ∧ j ∉ X
  symm := ⟨fun _ _ h => ⟨G.adj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun i h => G.loopless.irrefl i h.1⟩

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Finset (Fin n)) :
    DecidableRel (delVerts G X).Adj :=
  fun i j => inferInstanceAs (Decidable (G.Adj i j ∧ i ∉ X ∧ j ∉ X))

/-- A good leaf: a leaf `l` at `p` where `p` has at most one further neighbour, or a second leaf
`l'` at `p`. -/
def GoodLeaf {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ l p : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
    ((∃ q, ∀ w, G.Adj p w → w = l ∨ w = q) ∨ (∃ l', l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Decidable (GoodLeaf G) :=
  inferInstanceAs (Decidable (∃ l p : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
    ((∃ q, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
      (∃ l', l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))))

/-- A run of six: distinct vertices `a' - a - s - t - b - b'` where `a, s, t, b` have exactly the
two neighbours on the run, and `a'`, `b'` have at most one neighbour besides `a`, `b`. -/
def IsRun {n : ℕ} (G : SimpleGraph (Fin n)) (a' a s t b b' : Fin n) : Prop :=
  [a', a, s, t, b, b'].Nodup ∧
    (∀ w, G.Adj a w ↔ w = a' ∨ w = s) ∧
    (∀ w, G.Adj s w ↔ w = a ∨ w = t) ∧
    (∀ w, G.Adj t w ↔ w = s ∨ w = b) ∧
    (∀ w, G.Adj b w ↔ w = t ∨ w = b') ∧
    (∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c) ∧
    (∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a' a s t b b' : Fin n) :
    Decidable (IsRun G a' a s t b b') :=
  inferInstanceAs (Decidable ([a', a, s, t, b, b'].Nodup ∧
    (∀ w, G.Adj a w ↔ w = a' ∨ w = s) ∧
    (∀ w, G.Adj s w ↔ w = a ∨ w = t) ∧
    (∀ w, G.Adj t w ↔ w = s ∨ w = b) ∧
    (∀ w, G.Adj b w ↔ w = t ∨ w = b') ∧
    (∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c) ∧
    (∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c)))

/-- The dichotomy at one graph: with an edge, a good leaf or a run. -/
def HasPeel {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∃ i j, G.Adj i j) → GoodLeaf G ∨ ∃ a' a s t b b' : Fin n, IsRun G a' a s t b b'

/-- A peelable graph: every induced subgraph (as `delVerts G X`) with an edge has a good leaf or a
run. -/
def Peelable {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ X : Finset (Fin n), HasPeel (delVerts G X)

end PEqualNP.Library.Peel
