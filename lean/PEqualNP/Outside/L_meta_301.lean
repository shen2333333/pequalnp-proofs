import Mathlib
import PEqualNP.Defs

private lemma path_count_step (m : ℕ) (c : ℕ → Bool) :
    ((Finset.Icc 1 (m + 1)).filter (fun j => c j = true)).card =
      ((Finset.Icc 1 m).filter (fun j => c j = true)).card +
        (if c (m + 1) = true then 1 else 0) := by
  have interval : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have fresh : m + 1 ∉ (Finset.Icc 1 m).filter (fun j => c j = true) := by
    simp [Finset.mem_filter, Finset.mem_Icc]
  rw [interval, Finset.filter_insert]
  by_cases h : c (m + 1) = true <;> simp [h, fresh]

theorem PEqualNP.Outside.L_meta_301 :
    ∀ (k : ℕ) (c : ℕ → Bool),
      (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) →
      k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤
        ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k
  induction k with
  | zero =>
      intro c cover
      rcases cover 0 (by omega) with h | h <;> simp_all
  | succ k ih =>
      intro c cover
      have previous := ih c (fun j hj => cover j (by omega))
      have edge₁ := cover (2 * k + 1) (by omega)
      have edge₂ := cover (2 * k + 2) (by omega)
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        path_count_step, path_count_step]
      cases h₀ : c 0 <;>
        cases h₁ : c (2 * k + 1) <;>
        cases h₂ : c (2 * k + 2) <;>
        cases h₃ : c (2 * k + 3) <;>
        simp_all [Nat.mul_succ, Nat.add_assoc] <;> omega
