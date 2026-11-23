import PEqualNP.Defs.Pebble

/-!
# The three-way game on gate graphs

The three-way game (`routes/evasion/OBJECTS.md` DEF 3.1; `routes/evasion/DESK-GAPS.md` part 2,
block P2.0) on the gate graphs of `PEqualNP.Defs.Pebble`. This module records no result; it holds
only the definition a statement needs.

A gate is the three-element set `{v, p v, q v}` of a non-source `v` (`GateGraph.gate`). From a
kept set `R`, a three-way move places at most one vertex `u` not in `R`: `u` is a source (placed
freely), or some gate (of a non-source head) contains `u` and has its other two members in `R`.
So a value is recovered from a gate in any direction, as with a Latin-square operation: holding
`v` and `p v`, one may place `q v`, a backward move the black game forbids. One known member of a
gate is not enough.

* `GateGraph.ThreeWayMove R U`: a matching move (`GateGraph.MatchMove`) from the kept set `R`
  placing the set `U`, with at most one placed vertex. With one placed vertex `u` this says
  exactly: `u ∉ R`, and `u` is a source or lies in the gate of some non-source `h` with that
  gate inside `insert u R`. The empty placed set is a legal move (a pure removal, after `Step`
  has dropped vertices).

The three-way price is read through the generic play predicate of `PEqualNP.Defs.Pebble`:
`PriceLe G.ThreeWayMove x w` says some three-way play from the empty configuration reaches `x`
with every configuration of size at most `w`. No separate price function is defined.

Caveats a statement must respect:
* A configuration's size counts sources: a placed source costs a pebble like any other vertex.
* A step is "keep a subset, then place": `Step` keeps `R ⊆ P` and moves to `R ∪ U`. The
  thinker's "place, then drop any nodes" gives the same plays and the same peak sizes, since the
  configuration right after a placement is listed before the next step drops anything.
* The gate used to place `u` may be the gate of `u` itself (the forward, black direction) or the
  gate of a successor of `u` (the backward direction); its head must be a non-source.
* Because sources are placed freely, a backward move says something new only when the placed
  operand is itself a non-source.
-/

namespace PEqualNP.Pebble

namespace GateGraph

variable {n : ℕ} (G : GateGraph n)

/-- A three-way move from the kept set `R` placing the set `U`: a matching move
(`G.MatchMove R U`) that places at most one vertex. With `U = {u}` the matching sends `u` to the
head `h` of a gate that contains `u` and lies inside `R ∪ {u}`; when `u` is a source nothing is
required beyond `u ∉ R`. With `U = ∅` it is a pure removal. -/
def ThreeWayMove (R U : Finset (Fin n)) : Prop := G.MatchMove R U ∧ U.card ≤ 1

end GateGraph

end PEqualNP.Pebble
