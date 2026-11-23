import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_207 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s t : ℕ), s ≤ t →
      PEqualNP.MetaComplexity.HasTypedRank n f s → PEqualNP.MetaComplexity.HasTypedRank n f t := by
  rintro n f s t hst ⟨τ, hτ, hr⟩
  exact ⟨τ, hτ, le_trans hr hst⟩
