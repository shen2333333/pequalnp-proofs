import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_165 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (t t1 t2 : ℕ),
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) ∧ S.card = t1) →
      (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) → t1 ≤ S.card) →
      (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) ∧ S.card = t2) →
      (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) → t2 ≤ S.card) →
      ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t ∧ v ∈ S) ↔
        t1 + 1 ≤ t2 + (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card) := by
  intro n G _ v t t1 t2 ⟨St, hSt_vc, hSt_card⟩ ht_min ⟨S1, hS1_cov, hS1_card⟩ ht1_min
    ⟨S2, hS2_cov, hS2_card⟩ ht2_min
  set N : Finset (Fin n) := Finset.univ.filter (fun u : Fin n => G.Adj v u)
  have hv_not_N : v ∉ N := by
    simp [N]
  have h_with_v_lb : ∀ S : Finset (Fin n),
      PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → v ∈ S → t1 + 1 ≤ S.card := by
    intro S hS hvS
    have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S.erase v ∨ b ∈ S.erase v := by
      intro a b hab hav hbv
      rcases hS a b hab with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hav, ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, hb⟩)
    have hle := ht1_min (S.erase v) hcov
    have hcard : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hvS
    omega
  have h_without_v_lb : ∀ S : Finset (Fin n),
      PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → v ∉ S → t2 + N.card ≤ S.card := by
    intro S hS hvS
    have hN_sub : N ⊆ S := by
      intro u hu
      have hvu : G.Adj v u := (Finset.mem_filter.mp hu).2
      rcases hS v u hvu with hv | hu'
      · exact absurd hv hvS
      · exact hu'
    have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b →
        a ∈ S \ N ∨ b ∈ S \ N := by
      intro a b hab _ _ hna hnb
      rcases hS a b hab with ha | hb
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha, by simp [N, hna]⟩)
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hb, by simp [N, hnb]⟩)
    have hle := ht2_min (S \ N) hcov
    have hcard : (S \ N).card + N.card = S.card := Finset.card_sdiff_add_card_eq_card hN_sub
    omega
  have hv_not_S1 : v ∉ S1 := by
    intro hvS1
    have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S1.erase v ∨ b ∈ S1.erase v := by
      intro a b hab hav hbv
      rcases hS1_cov a b hab hav hbv with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hav, ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, hb⟩)
    have hle := ht1_min (S1.erase v) hcov
    have hcard : (S1.erase v).card + 1 = S1.card := Finset.card_erase_add_one hvS1
    omega
  have hS1_ins_vc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (insert v S1) := by
    intro a b hab
    by_cases hav : a = v
    · subst hav; exact Or.inl (Finset.mem_insert_self _ _)
    · by_cases hbv : b = v
      · subst hbv; exact Or.inr (Finset.mem_insert_self _ _)
      · rcases hS1_cov a b hab hav hbv with ha | hb
        · exact Or.inl (Finset.mem_insert_of_mem ha)
        · exact Or.inr (Finset.mem_insert_of_mem hb)
  have hS1_ins_card : (insert v S1).card = t1 + 1 := by
    rw [Finset.card_insert_of_notMem hv_not_S1, hS1_card]
  have hS2_disj_N : Disjoint S2 N := by
    rw [Finset.disjoint_left]
    intro u hu2 huN
    have hvu : G.Adj v u := (Finset.mem_filter.mp huN).2
    have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b →
        a ∈ S2.erase u ∨ b ∈ S2.erase u := by
      intro a b hab hav hbv hna hnb
      have hau : a ≠ u := fun h => hna (h ▸ hvu)
      have hbu : b ≠ u := fun h => hnb (h ▸ hvu)
      rcases hS2_cov a b hab hav hbv hna hnb with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hau, ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbu, hb⟩)
    have hle := ht2_min (S2.erase u) hcov
    have hcard : (S2.erase u).card + 1 = S2.card := Finset.card_erase_add_one hu2
    omega
  have hS2_union_vc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (S2 ∪ N) := by
    intro a b hab
    by_cases hav : a = v
    · subst hav; exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩))
    · by_cases hbv : b = v
      · subst hbv; exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩))
      · by_cases hna : G.Adj v a
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hna⟩))
        · by_cases hnb : G.Adj v b
          · exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb⟩))
          · rcases hS2_cov a b hab hav hbv hna hnb with ha | hb
            · exact Or.inl (Finset.mem_union_left _ ha)
            · exact Or.inr (Finset.mem_union_left _ hb)
  have hS2_union_card : (S2 ∪ N).card = t2 + N.card := by
    rw [Finset.card_union_of_disjoint hS2_disj_N, hS2_card]
  have ht_le_1 : t ≤ t1 + 1 := hS1_ins_card ▸ ht_min (insert v S1) hS1_ins_vc
  have ht_le_2 : t ≤ t2 + N.card := hS2_union_card ▸ ht_min (S2 ∪ N) hS2_union_vc
  have ht_ge : t1 + 1 ≤ t ∨ t2 + N.card ≤ t := by
    by_cases hvSt : v ∈ St
    · exact Or.inl (hSt_card ▸ h_with_v_lb St hSt_vc hvSt)
    · exact Or.inr (hSt_card ▸ h_without_v_lb St hSt_vc hvSt)
  constructor
  · rintro ⟨S, hS_vc, hS_card, hvS⟩
    have h1 := h_with_v_lb S hS_vc hvS
    omega
  · intro hle
    refine ⟨insert v S1, hS1_ins_vc, ?_, Finset.mem_insert_self _ _⟩
    omega
