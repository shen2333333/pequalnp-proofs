import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta478

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

private theorem clause_size (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  have lower : c.length ≤ (c.flatMap encodeLiteral).length := by
    induction c with
    | nil => simp
    | cons a c ih =>
      simp only [List.flatMap_cons, List.length_cons, List.length_append]
      have ha : 1 ≤ (encodeLiteral a).length := by simp [encodeLiteral]
      omega
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  omega

private theorem prefix_size (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    ((φ.take i).map (fun c => c.length + 1)).sum + (φ.getD i []).length <
      (encodeCNF φ).length := by
  induction φ generalizing i with
  | nil => simp at hi
  | cons c φ ih =>
    cases i with
    | zero =>
      have hc := clause_size c
      simp [encodeCNF] at *
      omega
    | succ i =>
      have hh := ih i (by simpa using hi)
      have hc := clause_size c
      simp [encodeCNF] at *
      omega

private theorem lit_mem {ψ : CNF} {i j : ℕ} {a : Literal}
    (h : (clauseAt ψ i)[j]? = some a) : a.1 ∈ vars ψ := by
  have hm := List.mem_of_getElem? h
  by_cases hi : i < ψ.length
  · rw [clauseAt, List.getD_eq_getElem _ _ hi] at hm
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
      ⟨ψ[i], List.getElem_mem hi, List.mem_map.mpr ⟨a, hm, rfl⟩⟩)
  · rw [clauseAt, List.getD_eq_default _ _ (Nat.le_of_not_gt hi)] at hm
    simp at hm

private theorem old_or_fresh {φ : CNF} {z : ℕ} (hz : z ∈ vars (cvcFormula φ)) :
    z ∈ vars φ ∨ z = fresh φ := by
  change z ∈ ((cvcFormula φ).flatMap (List.map Prod.fst)).toFinset at hz
  obtain ⟨d, hd, hmap⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hz)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmap
  simp only [cvcFormula, List.mem_append, List.mem_map, List.mem_singleton] at hd
  rcases hd with ⟨c, hc, rfl⟩ | rfl
  · rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl (List.mem_toFinset.mpr (List.mem_flatMap.mpr
        ⟨c, hc, List.mem_map.mpr ⟨a, ha, rfl⟩⟩))
    · simp only [List.mem_singleton] at ha
      simp [ha]
  · simp only [List.mem_singleton] at ha
    simp [ha]

private theorem position {φ : CNF} {i j : ℕ} (hj : j < (clauseAt (cvcFormula φ) i).length) :
    (i < φ.length ∧ j ≤ (φ.getD i []).length) ∨ (i = φ.length ∧ j = 0) := by
  by_cases hi : i < φ.length
  · left
    refine ⟨hi, ?_⟩
    rw [clauseAt, cvcFormula, List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)] at hj
    rw [List.getD_eq_getElem _ _ hi]
    simpa using hj
  · have hi' : φ.length ≤ i := by omega
    rw [clauseAt, cvcFormula, List.getD_append_right _ _ _ _ (by simpa using hi')] at hj
    simp only [List.length_map] at hj
    by_cases heq : i = φ.length
    · subst i
      simpa using hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      simp at hj

end PEqualNP.Outside.Meta478

open PEqualNP.Outside.Meta478 PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise in
theorem PEqualNP.Outside.L_meta_478 : ∀ (φ : PEqualNP.Search.CNF) (E : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v → num u < (3 * (E + 1)) := by
  intro φ E off e hE hoff he _ num hnum hfresh hpos hlast
  have literal (z : ℕ) (b : Bool) (hz : z ∈ vars (cvcFormula φ)) :
      num (.inl (z, b)) < 3 * (E + 1) := by
    rcases old_or_fresh hz with hz | rfl
    · rw [hnum z hz b]
      have := he z hz
      cases b <;> simp <;> omega
    · rw [hfresh b]
      cases b <;> simp <;> omega
  have occurrence (i j : ℕ) (hj : j < (clauseAt (cvcFormula φ) i).length) :
      num (.inr (i, j)) < 3 * (E + 1) := by
    rcases position hj with ⟨hi, hj'⟩ | ⟨rfl, rfl⟩
    · rw [hpos i j hi hj', hoff i]
      have := prefix_size φ i hi
      omega
    · rw [hlast]
      omega
  rintro (⟨z,b⟩ | ⟨i,j⟩) (⟨w,d⟩ | ⟨k,l⟩) h
  · exact literal z b h.2.2
  · exact literal z b (lit_mem h)
  · exact occurrence i j (List.getElem?_eq_some_iff.mp h).1
  · exact occurrence i j h.2.2.1
