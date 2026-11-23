import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta485

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem eval_true : Literal.eval (fun _ => true) = fun l : Literal => l.2 := by
  funext l
  simp [Literal.eval]

theorem mem_vars_cvc (φ : CNF) (x : ℕ) :
    x ∈ vars (cvcFormula φ) ↔ x ∈ vars φ ∨ x = fresh φ := by
  simp [vars, cvcFormula, List.mem_flatMap]
  aesop

theorem length_cvc (φ : CNF) : (cvcFormula φ).length = φ.length + 1 := by
  simp [cvcFormula]

theorem clauseAt_cvc_of_lt (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  unfold clauseAt cvcFormula
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem clauseAt_cvc_last (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  unfold clauseAt cvcFormula
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem mem_inl (φ : CNF) (x : ℕ) (b : Bool) :
    Sum.inl (x, b) ∈ cvcCover φ ↔ x ∈ vars (cvcFormula φ) ∧ b = true := by
  simp only [cvcCover, coverOf, Finset.inl_mem_disjSum, Finset.mem_image, Prod.mk.injEq]
  aesop

theorem mem_inr (φ : CNF) (i j : ℕ) :
    Sum.inr (i, j) ∈ cvcCover φ ↔ i < (cvcFormula φ).length ∧
      j < (clauseAt (cvcFormula φ) i).length ∧
      j ≠ (clauseAt (cvcFormula φ) i).findIdx (fun l => l.2) := by
  simp only [cvcCover, coverOf, Finset.inr_mem_disjSum, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, eval_true]
  aesop

end PEqualNP.Outside.LMeta485

open PEqualNP.Outside.LMeta485

theorem PEqualNP.Outside.L_meta_485 : ∀ (φ : PEqualNP.Search.CNF) (E : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ a : ℕ, (∃ u ∈ PEqualNP.MetaComplexity.CoverPromise.cvcCover φ, num u = a) ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2) ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2) := by
  intro φ E off e hE hoff he hinj num hnum1 hnum2 hnum3 hnum4 a
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases u with ⟨x, b⟩ | ⟨i, j⟩
    · obtain ⟨hx, rfl⟩ := (mem_inl φ x b).1 hu
      rcases (mem_vars_cvc φ x).1 hx with hx | rfl
      · exact Or.inl ⟨x, hx, by rw [hnum1 x hx true]; simp⟩
      · exact Or.inr (Or.inl (by rw [hnum2 true]; simp))
    · obtain ⟨hi, hj, hne⟩ := (mem_inr φ i j).1 hu
      rw [length_cvc] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [clauseAt_cvc_of_lt φ hi] at hj hne
        have hj' : j ≤ (φ.getD i []).length := by
          rw [List.length_append, List.length_singleton] at hj; omega
        exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj', hne, hnum3 i j hi hj'⟩))
      · rw [clauseAt_cvc_last φ] at hj
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0
        exact Or.inr (Or.inr (Or.inr hnum4))
  · rintro (⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl)
    · refine ⟨Sum.inl (z, true), (mem_inl φ z true).2 ⟨(mem_vars_cvc φ z).2 (Or.inl hz), rfl⟩, ?_⟩
      rw [hnum1 z hz true]
      simp
    · refine ⟨Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true),
        (mem_inl φ _ true).2 ⟨(mem_vars_cvc φ _).2 (Or.inr rfl), rfl⟩, ?_⟩
      rw [hnum2 true]
      simp
    · refine ⟨Sum.inr (i, j), (mem_inr φ i j).2 ⟨?_, ?_, ?_⟩, hnum3 i j hi hj⟩
      · rw [length_cvc]; omega
      · rw [clauseAt_cvc_of_lt φ hi, List.length_append, List.length_singleton]; omega
      · rw [clauseAt_cvc_of_lt φ hi]; exact hne
    · refine ⟨Sum.inr (φ.length, 0), (mem_inr φ φ.length 0).2 ⟨?_, ?_, ?_⟩, hnum4⟩
      · rw [length_cvc]; omega
      · rw [clauseAt_cvc_last φ]; simp
      · rw [clauseAt_cvc_last φ]; simp