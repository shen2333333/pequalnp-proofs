import Mathlib
import PEqualNP.Defs

open Finset

private theorem le_card_of_bins {α : Type*} (s : Finset α) (f : α → ℕ) (m : ℕ)
    (h : ∀ r < m, ∃ z ∈ s, f z = r) : m ≤ s.card := by
  have hsub : range m ⊆ s.image f := fun _ hr => mem_image.mpr (h _ (mem_range.mp hr))
  simpa using (card_le_card hsub).trans card_image_le


theorem PEqualNP.Outside.L_meta_279 : ∀ (n k t : ℕ) (E : List (Fin n × Fin n)), 0 < k → (∀ e ∈ E, e.1 ≠ e.2) → E.Nodup → (∀ e ∈ E, (e.2, e.1) ∉ E) → ((∃ S : Finset (Fin n), (∀ i : Fin E.length, (E.get i).1 ∈ S ∨ (E.get i).2 ∈ S) ∧ S.card = t) ∧ ∀ S : Finset (Fin n), (∀ i : Fin E.length, (E.get i).1 ∈ S ∨ (E.get i).2 ∈ S) → t ≤ S.card) → ((∃ S : Finset (Fin n ⊕ (Fin E.length × Fin (2 * k))), (∀ (i : Fin E.length) (j : Fin (2 * k)), (j.val = 0 → Sum.inl (E.get i).1 ∈ S ∨ Sum.inr (i, j) ∈ S) ∧ (j.val + 1 = 2 * k → Sum.inr (i, j) ∈ S ∨ Sum.inl (E.get i).2 ∈ S) ∧ (∀ j' : Fin (2 * k), j'.val = j.val + 1 → Sum.inr (i, j) ∈ S ∨ Sum.inr (i, j') ∈ S)) ∧ S.card = t + k * E.length) ∧ ∀ S : Finset (Fin n ⊕ (Fin E.length × Fin (2 * k))), (∀ (i : Fin E.length) (j : Fin (2 * k)), (j.val = 0 → Sum.inl (E.get i).1 ∈ S ∨ Sum.inr (i, j) ∈ S) ∧ (j.val + 1 = 2 * k → Sum.inr (i, j) ∈ S ∨ Sum.inl (E.get i).2 ∈ S) ∧ (∀ j' : Fin (2 * k), j'.val = j.val + 1 → Sum.inr (i, j) ∈ S ∨ Sum.inr (i, j') ∈ S)) → t + k * E.length ≤ S.card) := by
  intro n k t E hk _ _ _ hmin
  classical
  obtain ⟨⟨T, hT, hcard⟩, hleast⟩ := hmin
  constructor
  · let bit (i : Fin E.length) : ℕ := if (E.get i).1 ∈ T then 1 else 0
    have hbit (i : Fin E.length) : bit i ≤ 1 := by simp [bit]; split <;> omega
    let f (p : Fin E.length × Fin k) : Fin E.length × Fin (2 * k) :=
      (p.1, ⟨2 * p.2.val + bit p.1, by have := hbit p.1; have := p.2.isLt; omega⟩)
    have hf : Function.Injective f := by
      rintro ⟨i, a⟩ ⟨j, b⟩ h
      have hij : i = j := congrArg Prod.fst h
      subst j
      have hab : 2 * a.val + bit i = 2 * b.val + bit i := congrArg (fun p => p.2.val) h
      congr 1
      exact Fin.ext (by omega)
    let R := Finset.univ.image f
    have hin (i : Fin E.length) (j : Fin (2 * k)) (h : j.val % 2 = bit i) : (i, j) ∈ R := by
      refine mem_image.mpr ⟨(i, ⟨j.val / 2, by have := j.isLt; omega⟩), mem_univ _, ?_⟩
      refine Prod.ext ?_ ?_
      · rfl
      apply Fin.ext
      change 2 * (j.val / 2) + bit i = j.val
      omega
    refine ⟨T.disjSum R, ?_, ?_⟩
    · intro i j
      simp only [inl_mem_disjSum, inr_mem_disjSum]
      refine ⟨?_, ?_, ?_⟩
      · intro hj
        by_cases h : (E.get i).1 ∈ T
        · exact Or.inl h
        · exact Or.inr (hin i j (by rw [hj]; simp only [bit, ite_eq_right h]))
      · intro hj
        rcases hT i with h | h
        · apply Or.inl
          apply hin
          simp only [bit, ite_eq_left h]
          omega
        · exact Or.inr h
      · intro j' hj
        have := hbit i
        by_cases h : j.val % 2 = bit i
        · exact Or.inl (hin i j h)
        · exact Or.inr (hin i j' (by omega))
    · rw [card_disjSum, hcard, show R.card = E.length * k by
            simp [R, card_image_of_injective _ hf], Nat.mul_comm]
  · intro S hS
    let U := univ.filter (fun i : Fin E.length =>
      (E.get i).1 ∉ S.toLeft ∧ (E.get i).2 ∉ S.toLeft)
    let repair := fun i : Fin E.length => (E.get i).1
    have hrepair : t ≤ (S.toLeft ∪ U.image repair).card := by
      apply hleast
      intro i
      by_cases ha : (E.get i).1 ∈ S.toLeft
      · exact Or.inl (mem_union_left _ ha)
      by_cases hb : (E.get i).2 ∈ S.toLeft
      · exact Or.inr (mem_union_left _ hb)
      · exact Or.inl (mem_union_right _ (mem_image_of_mem repair (mem_filter.mpr
          ⟨mem_univ _, ha, hb⟩)))
    have hbase : t ≤ S.toLeft.card + U.card :=
      hrepair.trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))
    let fiber (i : Fin E.length) := S.toRight.filter (fun p => p.1 = i)
    have hmem (i : Fin E.length) (j : Fin (2 * k)) (h : Sum.inr (i, j) ∈ S) :
        (i, j) ∈ fiber i := mem_filter.mpr ⟨mem_toRight.mpr h, rfl⟩
    have hcount (i : Fin E.length) : k + (if i ∈ U then 1 else 0) ≤ (fiber i).card := by
      by_cases h : i ∈ U
      · rw [ite_eq_left h]
        obtain ⟨ha, hb⟩ := (mem_filter.mp h).2
        apply le_card_of_bins (fiber i) (fun p => (p.2.val + 1) / 2)
        intro r hr
        by_cases hzero : r = 0
        · subst r
          let j : Fin (2 * k) := ⟨0, by omega⟩
          exact ⟨(i, j), hmem i j (((hS i j).1 rfl).resolve_left (fun hx => ha (mem_toLeft.mpr hx))), by change (0 + 1) / 2 = 0; decide⟩
        by_cases hend : r = k
        · subst r
          let j : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
          have hj : j.val + 1 = 2 * k := by dsimp [j]; omega
          refine ⟨(i, j), hmem i j (((hS i j).2.1 hj).resolve_right (fun hx => hb (mem_toLeft.mpr hx))), ?_⟩
          change (2 * k - 1 + 1) / 2 = k
          omega
        · let a : Fin (2 * k) := ⟨2 * r - 1, by omega⟩
          let b : Fin (2 * k) := ⟨2 * r, by omega⟩
          rcases (hS i a).2.2 b (by dsimp [a, b]; omega) with ha' | hb'
          · exact ⟨(i, a), hmem i a ha', by dsimp [a]; omega⟩
          · exact ⟨(i, b), hmem i b hb', by dsimp [b]; omega⟩
      · rw [ite_eq_right h, Nat.add_zero]
        apply le_card_of_bins (fiber i) (fun p => p.2.val / 2)
        intro r hr
        let a : Fin (2 * k) := ⟨2 * r, by omega⟩
        let b : Fin (2 * k) := ⟨2 * r + 1, by omega⟩
        rcases (hS i a).2.2 b rfl with ha | hb
        · exact ⟨(i, a), hmem i a ha, by dsimp [a]; omega⟩
        · exact ⟨(i, b), hmem i b hb, by dsimp [b]; omega⟩
    have hfib : S.toRight.card = ∑ i, (fiber i).card :=
      card_eq_sum_card_fiberwise (f := Prod.fst) (fun _ _ => mem_univ _)
    have htotal := Finset.sum_le_sum (s := univ) (fun i _ => hcount i)
    rw [← hfib, Finset.sum_add_distrib] at htotal
    have hu : (∑ i : Fin E.length, if i ∈ U then 1 else 0) = U.card := by
      simp
    rw [hu] at htotal
    simp only [Finset.sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at htotal
    have hsplit : S.toLeft.card + S.toRight.card = S.card := card_toLeft_add_card_toRight
    rw [Nat.mul_comm k]
    omega
