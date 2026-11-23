import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_131 :
    ∀ (m s D Du Dd F E c c₁ c₂ E₀ Ew Ew' : ℕ), 16 ≤ m →
      (16 * s ≤ m → 15 * m ≤ 8 * (2 * m - 2 * s)) ∧
      (7 * m ≤ 8 * D → 8 * Du < m + 8 → D ≤ Dd + Du → m < 8 * Dd) ∧
      (m ≤ 2 * F → 16 * s ≤ m → F ≤ E + s → 7 * m ≤ 16 * E) ∧
      (m ≤ 2 * F → 8 * E < m → F ≤ E + c → m ≤ 32 * c) ∧
      (m ≤ 64 * c₁ → m ≤ 64 * c₂ → m ≤ 32 * (c₁ + c₂)) ∧
      (7 * m ≤ 16 * E₀ → 8 * Ew < m + 8 → E₀ ≤ Ew' + Ew → m < 8 * Ew') ∧
      (16 * s ≤ m → m ≤ 2 * (m - s)) := by
  intro m s D Du Dd F E c c₁ c₂ E₀ Ew Ew' hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
