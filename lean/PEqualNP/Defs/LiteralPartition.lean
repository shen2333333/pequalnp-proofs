import Mathlib.Data.Fintype.Basic

/-!
# Literal-rectangle partition number of a Boolean function

Let `f` be a Boolean function on `n` inputs. A pair is an input `x` with `f x = true` together
with an input `y` with `f y = false`. A literal rectangle is a set of pairs of the form `A × B`
(with `A` inside the inputs where `f` is true and `B` inside the inputs where `f` is false)
together with a literal: a position `i` and a bit `b` such that every `x` in `A` has `x i = b`
and every `y` in `B` has `y i` different from `b`. The literal-rectangle partition number of
`f` is the least `k` such that the set of all pairs is the disjoint union of `k` literal
rectangles. It sits between the typed rank of `Defs/MetaComplexityTypedRank.lean` and the de
Morgan leaf size of `Defs/DeMorganFormula.lean`.

* `IsLiteralPartition n f k A B pos bit`: the `k` rectangles `A j × B j`, each with the literal
  `(pos j, bit j)`, partition the pairs of `f`.
* `HasLiteralPartition n f k`: the pairs of `f` split into at most `k` literal rectangles.

Caveats a statement must respect.
* "At most `k`": empty rectangles are allowed, so `HasLiteralPartition n f k` is monotone in
  `k`, and the number itself is the least `k` for which it holds.
* The literal of a rectangle constrains only the pairs it contains: the condition is stated
  for each `x` in `A j` and `y` in `B j` together, so a rectangle with `A j` or `B j` empty
  places no condition on its literal. This is the reading of a rectangle as a set of pairs.
* Positions are natural numbers, not elements of `Fin n`, so that a partition into `k > 0`
  (empty) parts exists when `n = 0` (then `f` is constant and there is no pair). A rectangle
  holding a pair has its position below `n`.
* Partition means every pair lies in exactly one rectangle; a cover is not enough.

Nothing here speaks of formulas or ranks; the module imports only Mathlib.
-/

namespace PEqualNP.MetaComplexity

/-- The `k` rectangles `A j × B j` with literals `(pos j, bit j)` form a literal partition of the
pairs of `f`:
* every member of `A j` is an input where `f` is true, every member of `B j` an input where `f`
  is false;
* for `x` in `A j` and `y` in `B j`, the position `pos j` is some `i : Fin n` with
  `x i = bit j` and `y i ≠ bit j`;
* every pair `(x, y)` with `f x = true` and `f y = false` lies in exactly one rectangle. -/
def IsLiteralPartition (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ)
    (A B : Fin k → (Fin n → Bool) → Bool) (pos : Fin k → ℕ) (bit : Fin k → Bool) : Prop :=
  (∀ j : Fin k, ∀ x : Fin n → Bool, A j x = true → f x = true) ∧
  (∀ j : Fin k, ∀ y : Fin n → Bool, B j y = true → f y = false) ∧
  (∀ j : Fin k, ∀ x y : Fin n → Bool, A j x = true → B j y = true →
    ∃ i : Fin n, pos j = (i : ℕ) ∧ x i = bit j ∧ y i ≠ bit j) ∧
  (∀ x y : Fin n → Bool, f x = true → f y = false →
    ∃! j : Fin k, A j x = true ∧ B j y = true)

/-- The pairs of `f` split into at most `k` literal rectangles: the literal-rectangle partition
number of `f` is at most `k`. -/
def HasLiteralPartition (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ (A B : Fin k → (Fin n → Bool) → Bool) (pos : Fin k → ℕ) (bit : Fin k → Bool),
    IsLiteralPartition n f k A B pos bit

end PEqualNP.MetaComplexity
