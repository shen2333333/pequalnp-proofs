import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ENat.Lattice

/-!
# Co-level of a multiset of p-units

Fix a field `K`, a number `m` of variables `y_0, .., y_(m-1)` (the polynomial ring
`MvPolynomial (Fin m) K`) and a number `p` of rows.

A linear form is `l(y) = c_0 y_0 + .. + c_(m-1) y_(m-1)`, given by its coefficient vector
`c : Fin m → K`. Linear forms here are HOMOGENEOUS: no constant term. So every factor
`1 + l(y)` has constant term `1`, and every p-unit has constant term `1`.

A p-unit is `U = (1 + l_0(y)) * .. * (1 + l_(p-1)(y))`, given by its `p × m` coefficient
matrix `c : Fin p → Fin m → K` (row `r` is the form `l_r`). Two different matrices may give
the same polynomial (rows permuted); no notion below depends on which matrix is used.

The co-level of a finite multiset `A` of p-units is the least `N` such that there are p-units
`U_1, .., U_N` with `sum_(U in A) U + U_1 + .. + U_N = |A| + N` as polynomials (the constant
polynomial `|A| + N`), and `⊤` if no such `N` exists.

* `linForm c`: the linear form `sum_i c_i y_i`.
* `pUnit c`: the p-unit `prod_r (1 + linForm (c r))` of the coefficient matrix `c`.
* `CoLevelWitness A N`: there are `N` p-units completing the sum of `A` to the constant `|A| + N`.
* `coLevel A : ℕ∞`: the least `N` with `CoLevelWitness A N`, `⊤` if none.

Caveats a statement must respect.

* A multiset of p-units is a `Multiset (Fin p → Fin m → K)` of coefficient matrices; its
  polynomials are `A.map pUnit`. `|A|` is `Multiset.card A`, counted with multiplicity.
* The target constant is the literal `|A| + N`, cast into the polynomial ring (in
  characteristic `l` it is read mod `l`). Since every p-unit has constant term `1`, "the sum is
  a constant" and "the sum equals `|A| + N`" say the same thing.
* `coLevel` is an `ℕ∞` defined by `sInf` over the naturals that admit a witness; `sInf ∅ = ⊤`.
* `p = 0` makes every p-unit the polynomial `1`, so every multiset has co-level `0`.
-/

namespace PEqualNP.CoLevel

open MvPolynomial

variable {K : Type*} [Field K] {m p : ℕ}

/-- The homogeneous linear form `sum_i c_i y_i` with coefficient vector `c`. -/
noncomputable def linForm (c : Fin m → K) : MvPolynomial (Fin m) K :=
  ∑ i, C (c i) * X i

/-- The p-unit `prod_r (1 + l_r(y))` whose row `r` is the linear form with coefficients `c r`.
The number of rows `p` is the length of the product. -/
noncomputable def pUnit (c : Fin p → Fin m → K) : MvPolynomial (Fin m) K :=
  ∏ r, (1 + linForm (c r))

/-- `N` p-units `U_1, .., U_N` complete the multiset `A` of p-units: the sum of `A` plus
`U_1 + .. + U_N` is the constant polynomial `|A| + N`. -/
def CoLevelWitness (A : Multiset (Fin p → Fin m → K)) (N : ℕ) : Prop :=
  ∃ B : Fin N → Fin p → Fin m → K,
    (A.map pUnit).sum + ∑ j, pUnit (B j) = ((Multiset.card A + N : ℕ) : MvPolynomial (Fin m) K)

/-- The co-level of a multiset of p-units: the least `N` with `CoLevelWitness A N`, and `⊤`
if there is none. -/
noncomputable def coLevel (A : Multiset (Fin p → Fin m → K)) : ℕ∞ :=
  sInf ((fun N : ℕ => (N : ℕ∞)) '' {N | CoLevelWitness A N})

end PEqualNP.CoLevel
