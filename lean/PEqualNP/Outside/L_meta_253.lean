import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_253 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
      (x : Fin n → Bool),
      decide (∃ u w : Fin n, G.Adj u w ∧
        Function.update x v false u = true ∧ Function.update x v false w = true) =
      decide (∃ u w : Fin n, u ≠ v ∧ w ≠ v ∧ G.Adj u w ∧
        x u = true ∧ x w = true) := by
  intro n G _ v x
  have updated (u : Fin n) :
      Function.update x v false u = true ↔ u ≠ v ∧ x u = true := by
    by_cases h : u = v
    · simp [h]
    · simp [h]
  rw [decide_eq_decide]
  simp_rw [updated]
  constructor
  · rintro ⟨u, w, hadj, ⟨huv, hu⟩, ⟨hwv, hw⟩⟩
    exact ⟨u, w, huv, hwv, hadj, hu, hw⟩
  · rintro ⟨u, w, huv, hwv, hadj, hu, hw⟩
    exact ⟨u, w, hadj, ⟨huv, hu⟩, ⟨hwv, hw⟩⟩
