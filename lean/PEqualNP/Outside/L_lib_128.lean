import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_128 :
    ∀ (f : ℕ → ℕ), f 0 = 1 →
      (∀ i : ℕ, f (i + 1) + 2 ^ i = 2 * f i + 2 ^ (i + 1) * (4 * i + 5)) →
      ∀ i : ℕ, 2 * f i = (4 * i ^ 2 + 5 * i + 2) * 2 ^ i := by
  intro f h0 hrec i
  induction i with
  | zero =>
    simp [h0]
  | succ i ih =>
    have h := hrec i
    have h2 : 2 * f (i + 1) + 2 * 2 ^ i =
        (4 * (i + 1) ^ 2 + 5 * (i + 1) + 2) * 2 ^ (i + 1) + 2 * 2 ^ i := by
      calc
        2 * f (i + 1) + 2 * 2 ^ i = 2 * (f (i + 1) + 2 ^ i) := by ring
        _ = 2 * (2 * f i + 2 ^ (i + 1) * (4 * i + 5)) := by rw [h]
        _ = 2 * ((4 * i ^ 2 + 5 * i + 2) * 2 ^ i) + 2 * (2 ^ (i + 1) * (4 * i + 5)) := by
          rw [ih]; ring
        _ = (4 * (i + 1) ^ 2 + 5 * (i + 1) + 2) * (2 * 2 ^ i) + 2 * 2 ^ i := by
          rw [pow_succ' 2 i]; ring
        _ = (4 * (i + 1) ^ 2 + 5 * (i + 1) + 2) * 2 ^ (i + 1) + 2 * 2 ^ i := by
          rw [pow_succ' 2 i]
    exact Nat.add_right_cancel h2
