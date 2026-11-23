import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.L_meta_474 : ∀ φ : PEqualNP.Search.CNF, ∀ u ∈ PEqualNP.MetaComplexity.CoverPromise.cvcCover φ, ∃ v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ u hu
  rcases u with a | ij
  · simp only [cvcCover, coverOf, Finset.inl_mem_disjSum, Finset.mem_image] at hu
    obtain ⟨x,hx,rfl⟩ := hu
    exact ⟨Sum.inl (x,false), rfl, (by decide : true ≠ false), hx⟩
  · simp only [cvcCover, coverOf, Finset.inr_mem_disjSum, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨i,_,j,⟨hj,_⟩,rfl⟩ := hu
    refine ⟨Sum.inl ((clauseAt (cvcFormula φ) i)[j]), ?_⟩
    exact List.getElem?_eq_getElem hj
