import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The 2k-fold subdivision of a graph on `Fin m`

For a graph `H` on `Fin m` and a number `k`, the subdivision replaces every edge of `H` by a path
of `2k + 1` edges through `2k` new vertices. It lives on `Fin (nS m k)`, `nS m k = m + 2k m^2`,
numbered without enumerating edges:

* the HUBS are the indices `0, .., m - 1` (the vertices of `H`, same index);
* a SLOT is a pair `(u, v)` of vertices of `H`; it is LIVE iff `u < v` and `H.Adj u v`; the slot
  `(u, v)` owns the `2k` indices `m + 2k (u m + v) + i`, `i < 2k`;
* the THREAD of a live slot is `u, m + 2k (u m + v), .., m + 2k (u m + v) + 2k - 1, v`, a path
  of `2k + 1` steps. The indices of a slot that is not live are isolated vertices.

With `k = 0` there are no new vertices and the subdivision is `H` itself.

The adjacency is `SimpleGraph.fromRel` of an explicit relation (arithmetic and bounded
existentials), so it is symmetric and irreflexive by construction and decidable when `H.Adj` is.

* `nS m k`: the number of vertices.
* `SubRel k H x y`: `x` then `y` are consecutive on the thread of a live slot, read upward.
* `subdiv k H`: the subdivision.
* `OnThr k H j`: `j` is an inner vertex of the thread of a live slot.
* `pos k H j`: the position `1 .. 2k` of `j` on its thread, `0` on hubs and dead slots.

The same definitions, with their first lemmas, were built for the meta-complexity line in a
helper module; they agree with these by `rfl`. Nothing here imports beyond the pinned library.
-/

namespace PEqualNP.Library.Subdivision

/-- The number of vertices of the subdivision: `m` hubs and `2k` indices for each of the `m * m`
slots. -/
def nS (m k : ℕ) : ℕ := m + 2 * k * m * m

/-- One step of a thread, read from the lower end `u` toward the upper end `v` of a live slot:
`x` is the vertex at position `p` and `y` the vertex at position `p + 1`, where position `0` is
the hub `u`, position `2k + 1` is the hub `v`, and position `t` with `1 ≤ t ≤ 2k` is the index
`m + 2k (u m + v) + (t - 1)`. -/
def SubRel {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (nS m k)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : Fin (2 * k + 1),
    x.val = (if p.val = 0 then u.val else m + 2 * k * (u.val * m + v.val) + p.val - 1) ∧
    y.val = (if p.val = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + p.val)

/-- The 2k-fold subdivision of `H`: two indices are adjacent iff they are distinct and one thread
step joins them, in one of the two orders. -/
def subdiv {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) : SimpleGraph (Fin (nS m k)) :=
  SimpleGraph.fromRel (SubRel k H)

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidableRel (SubRel k H) :=
  fun x y => inferInstanceAs (Decidable (∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : Fin (2 * k + 1),
    x.val = (if p.val = 0 then u.val else m + 2 * k * (u.val * m + v.val) + p.val - 1) ∧
    y.val = (if p.val = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + p.val)))

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidableRel (subdiv k H).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (SubRel k H x y ∨ SubRel k H y x)))

/-- The index is an inner vertex of the thread of a live slot. -/
def OnThr {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (j : Fin (nS m k)) : Prop :=
  ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧
    j.val = m + 2 * k * (u.val * m + v.val) + i.val

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidablePred (OnThr k H) :=
  fun j => inferInstanceAs (Decidable (∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧
    j.val = m + 2 * k * (u.val * m + v.val) + i.val))

/-- The position of an index on its thread: `i + 1` on the inner vertex at offset `i` of a live
slot, `0` on hubs and on the indices of dead slots. -/
def pos {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (j : Fin (nS m k)) : ℕ :=
  if OnThr k H j then (j.val - m) % (2 * k) + 1 else 0

end PEqualNP.Library.Subdivision
