import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_254 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (x : Fin n → Bool), decide (∃ u w : Fin n, G.Adj u w ∧ Function.update x v true u = true ∧ Function.update x v true w = true) = decide ((∃ u : Fin n, G.Adj v u ∧ x u = true) ∨ ∃ u w : Fin n, u ≠ v ∧ w ≠ v ∧ ¬ G.Adj v u ∧ ¬ G.Adj v w ∧ G.Adj u w ∧ x u = true ∧ x w = true) := by
  intro n G _ v x
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨u, w, huw, hu, hw⟩
    by_cases h1 : u = v
    · have hvw : G.Adj v w := by
        rw [h1] at huw
        exact huw
      have hwv : w ≠ v := (G.ne_of_adj hvw).symm
      rw [Function.update_of_ne hwv] at hw
      exact Or.inl ⟨w, hvw, hw⟩
    · rw [Function.update_of_ne h1] at hu
      by_cases h2 : w = v
      · have hvu : G.Adj v u := by
          rw [h2] at huw
          exact huw.symm
        exact Or.inl ⟨u, hvu, hu⟩
      · rw [Function.update_of_ne h2] at hw
        by_cases h3 : G.Adj v u
        · exact Or.inl ⟨u, h3, hu⟩
        · by_cases h4 : G.Adj v w
          · exact Or.inl ⟨w, h4, hw⟩
          · exact Or.inr ⟨u, w, h1, h2, h3, h4, huw, hu, hw⟩
  · rintro (⟨u, hvu, hu⟩ | ⟨u, w, h1, h2, -, -, huw, hu, hw⟩)
    · have huv : u ≠ v := (G.ne_of_adj hvu).symm
      refine ⟨v, u, hvu, ?_, ?_⟩
      · rw [Function.update_self]
      · rw [Function.update_of_ne huv]
        exact hu
    · refine ⟨u, w, huw, ?_, ?_⟩
      · rw [Function.update_of_ne h1]
        exact hu
      · rw [Function.update_of_ne h2]
        exact hw
