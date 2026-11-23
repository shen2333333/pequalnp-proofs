import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_250 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧ ∀ v : Fin N, pos' v ≠ 0 → pos' v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk ⟨hsym, hz, hth⟩ hr
  have key : ∀ v, pos v ≤ 2 * k ∧ pos' v ≤ 2 * k ∧
      ((pos v = 0 ∧ pos' v = 0) ∨ pos v + pos' v = 2 * k + 1) := by
    intro v
    obtain ⟨h1, h2⟩ := hr v
    have h3 : pos v ≤ 2 * k := by
      by_cases h : pos v = 0
      · omega
      · exact (hth v h).1
    refine ⟨h3, h1, ?_⟩
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h2
    have hc2 : c < 2 := by
      by_contra hcon
      have : (2 * k + 1) * 2 ≤ (2 * k + 1) * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c
    · left; omega
    · right; omega
  have hmod : ∀ x, x ≤ 2 * k → (x + 1) % (2 * k + 1) = if x = 2 * k then 0 else x + 1 := by
    intro x hx
    split_ifs with h
    · subst h; exact Nat.mod_self _
    · exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    have := hz u v huv
    have := key u
    have := key v
    omega
  · intro v hv
    have kv := key v
    have hpv : pos v ≠ 0 := by omega
    obtain ⟨_, a, b, hE, ha, hb⟩ := hth v hpv
    refine ⟨kv.2.1, b, a, fun w => (hE w).trans or_comm, ?_, ?_⟩
    · rw [hmod _ kv.1] at hb
      have := key b
      split_ifs at hb <;> omega
    · rw [hmod _ kv.2.1]
      have := key a
      split_ifs <;> omega
