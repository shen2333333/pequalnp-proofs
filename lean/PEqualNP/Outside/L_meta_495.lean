import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_495 :
    ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ), (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, (∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) ∧ ∀ g < e z, ∀ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[g]? = some (some l) → l.1 ≠ z := by
  intro φ e he z hz
  let L : List (Option PEqualNP.Search.Literal) := φ.flatMap (fun c => c.map some ++ [none])
  let p : Option PEqualNP.Search.Literal → Bool := fun o => o.any (fun l => l.1 == z)
  have hez : e z = L.findIdx p := he z
  have hex : ∃ o ∈ L, p o = true := by
    simp only [PEqualNP.MetaComplexity.CoverPromise.vars, List.mem_toFinset, List.mem_flatMap,
      List.mem_map] at hz
    rcases hz with ⟨c, hc, l, hl, rfl⟩
    refine ⟨some l, ?_, ?_⟩
    · simp only [L, List.mem_flatMap, List.mem_append, List.mem_map]
      exact ⟨c, hc, Or.inl ⟨l, hl, rfl⟩⟩
    · simp [p]
  have hlt : L.findIdx p < L.length := List.findIdx_lt_length.mpr hex
  constructor
  · have hp : p (L[L.findIdx p]'hlt) = true := List.findIdx_getElem (w := hlt)
    cases hget : L[L.findIdx p]'hlt with
    | none =>
      simp [p, hget] at hp
    | some l =>
      refine ⟨l, ?_, ?_⟩
      · rw [hez, List.getElem?_eq_getElem hlt, hget]
      · simp [p, hget] at hp
        exact hp
  · intro g hg l hlg
    rw [hez] at hg
    have hglt : g < L.length := lt_trans hg hlt
    have hnp : p (L[g]'hglt) = false := List.not_of_lt_findIdx hg
    rw [List.getElem?_eq_getElem hglt] at hlg
    injection hlg with hlg'
    rw [hlg'] at hnp
    simp [p] at hnp
    exact hnp
