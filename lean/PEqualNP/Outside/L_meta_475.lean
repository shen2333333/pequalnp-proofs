import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.MetaComplexity.CoverPromise

theorem L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inr (φ.length, 0), Sum.inl (fresh φ, false), ?_⟩
  show (clauseAt (cvcFormula φ) φ.length)[0]? = some (fresh φ, false)
  simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD, List.getElem?_append_right]

end PEqualNP.Outside
