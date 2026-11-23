import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

private theorem memVars {φ : CNF} {x : ℕ} :
    x ∈ vars φ ↔ ∃ c ∈ φ, ∃ l ∈ c, l.1 = x := by
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]

private theorem clauseAtIndex {φ : CNF} {i : ℕ} (h : 0 < (clauseAt φ i).length) :
    i < φ.length := by
  by_contra! hi
  rw [clauseAt, List.getD_eq_default _ _ hi] at h
  simp at h

private theorem adjacentEndpoint {φ : CNF} {u v : Vertex}
    (h : (satGraph φ).Adj u v) :
    match u with
    | .inl l => l.1 ∈ vars φ
    | .inr (i, j) => i < φ.length ∧ j < (clauseAt φ i).length := by
  change satAdj φ u v at h
  cases u with
  | inl l =>
      cases v with
      | inl l' => exact h.2.2
      | inr ij =>
          obtain ⟨i, j⟩ := ij
          change (clauseAt φ i)[j]? = some l at h
          obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp h
          have hi := clauseAtIndex (Nat.zero_lt_of_lt hj)
          have hc : clauseAt φ i ∈ φ := by
            rw [clauseAt, List.getD_eq_getElem _ _ hi]
            exact List.getElem_mem hi
          exact memVars.mpr ⟨_, hc, l, List.mem_of_getElem? h, rfl⟩
  | inr ij =>
      obtain ⟨i, j⟩ := ij
      cases v with
      | inl l =>
          change (clauseAt φ i)[j]? = some l at h
          obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp h
          exact ⟨clauseAtIndex (Nat.zero_lt_of_lt hj), hj⟩
      | inr kl =>
          obtain ⟨k, l⟩ := kl
          exact ⟨clauseAtIndex (Nat.zero_lt_of_lt h.2.2.1), h.2.2.1⟩

private theorem cvcVar {φ : CNF} {x : ℕ} (h : x ∈ vars (cvcFormula φ)) :
    x ∈ vars φ ∨ x = fresh φ := by
  obtain ⟨c, hc, l, hl, hxl⟩ := memVars.mp h
  simp only [cvcFormula, List.mem_append, List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨c', hc', rfl⟩ | rfl
  · simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact Or.inl (memVars.mpr ⟨c', hc', l, hl, hxl⟩)
    · exact Or.inr hxl.symm
  · simp only [List.mem_singleton] at hl
    subst l
    exact Or.inr hxl.symm

private theorem cvcPosition {φ : CNF} {i j : ℕ}
    (hi : i < (cvcFormula φ).length) (hj : j < (clauseAt (cvcFormula φ) i).length) :
    (i < φ.length ∧ j ≤ (φ.getD i []).length) ∨ (i = φ.length ∧ j = 0) := by
  by_cases h : i < φ.length
  · left
    refine ⟨h, ?_⟩
    have hm : i < (φ.map (fun c => c ++ [(fresh φ, true)])).length := by simpa using h
    rw [clauseAt, cvcFormula, List.getD_append _ _ _ _ hm,
      List.getD_eq_getElem _ _ hm, List.getElem_map] at hj
    rw [List.getD_eq_getElem _ _ h]
    simp at hj
    omega
  · have he : i = φ.length := by
      simp [cvcFormula] at hi
      omega
    subst i
    have ha : (φ.map (fun c => c ++ [(fresh φ, true)])).length ≤ φ.length := by simp
    rw [clauseAt, cvcFormula, List.getD_append_right _ _ _ _ ha] at hj
    simp at hj
    omega

private theorem encodeClauseLength (c : Clause) :
    c.length + 1 ≤ (encodeClause c).length := by
  have h : c.length ≤ (c.flatMap encodeLiteral).length := by
    induction c with
    | nil => simp
    | cons l ls ih =>
        have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        omega
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  omega

private theorem encodeCnfLength (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
      simpa only [encodeCNF, List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
        using Nat.add_le_add (encodeClauseLength c) ih

private theorem compareLiteralNumbers (x y : ℕ) (b b' : Bool)
    (h : 2 * x + (if b then 1 else 0) = 2 * y + (if b' then 1 else 0)) :
    x = y ∧ b = b' := by
  cases b <;> cases b' <;> simp at h ⊢ <;> omega

theorem PEqualNP.Outside.L_meta_479 : ∀ (φ : PEqualNP.Search.CNF) (E : ℕ)
    (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length →
    (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') →
    ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ,
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool,
      num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) →
    (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) =
      2 * E + (if b then 1 else 0)) →
    (∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) →
    num (Sum.inr (φ.length, 0)) = 3 * E + 2 →
    ∀ u v w z : PEqualNP.MetaComplexity.CoverPromise.Vertex,
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v →
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj w z →
      num u = num w → u = w := by
  intro φ E off e hE hoff he heinj num hOld hFresh hClause hLast
  have mono : Monotone off := by
    intro i k hik
    simpa only [hoff, List.map_take] using
      List.monotone_sum_take (φ.map (fun c => c.length + 1)) hik
  have next (i : ℕ) (hi : i < φ.length) :
      off (i + 1) = off i + ((φ.getD i []).length + 1) := by
    simp only [hoff, List.map_take]
    have hm : i < (φ.map (fun c => c.length + 1)).length := by simpa using hi
    rw [List.sum_take_succ _ _ hm, List.getElem_map, List.getD_eq_getElem _ _ hi]
  have finish : off φ.length ≤ E := by
    rw [hoff, List.take_length, hE]
    exact encodeCnfLength φ
  have ordinaryBeforeLast (i j : ℕ) (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inr (i, j)) < 3 * E + 2 := by
    rw [hClause i j hi hj]
    have hn := next i hi
    have hm : off (i + 1) ≤ off φ.length := mono (Nat.succ_le_of_lt hi)
    omega
  have literalBound (x : ℕ) (b : Bool) (hx : x ∈ vars φ ∨ x = fresh φ) :
      num (Sum.inl (x, b)) < 2 * (E + 1) := by
    rcases hx with h | rfl
    · have hb := he x h
      rw [hOld x h]
      cases b <;> simp <;> omega
    · rw [hFresh]
      cases b <;> simp <;> omega
  have occurrenceBound (i j : ℕ)
      (h : (i < φ.length ∧ j ≤ (φ.getD i []).length) ∨ (i = φ.length ∧ j = 0)) :
      2 * (E + 1) ≤ num (Sum.inr (i, j)) := by
    rcases h with ⟨hi, hj⟩ | ⟨rfl, rfl⟩
    · rw [hClause i j hi hj]
      omega
    · rw [hLast]
      omega
  intro u v w z huv hwz hn
  have hu := adjacentEndpoint (φ := cvcFormula φ) huv
  have hw := adjacentEndpoint (φ := cvcFormula φ) hwz
  rcases u with ⟨x, b⟩ | ⟨i, j⟩ <;> rcases w with ⟨y, b'⟩ | ⟨k, l⟩
  · rcases cvcVar hu with hx | rfl <;> rcases cvcVar hw with hy | rfl
    · rw [hOld x hx, hOld y hy] at hn
      obtain ⟨hxy, rfl⟩ := compareLiteralNumbers _ _ _ _ hn
      rw [heinj x hx y hy hxy]
    · rw [hOld x hx, hFresh] at hn
      exact (ne_of_lt (he x hx) (compareLiteralNumbers _ _ _ _ hn).1).elim
    · rw [hFresh, hOld y hy] at hn
      exact (ne_of_lt (he y hy) (compareLiteralNumbers _ _ _ _ hn).1.symm).elim
    · rw [hFresh, hFresh] at hn
      rw [(compareLiteralNumbers _ _ _ _ hn).2]
  · have h₁ := literalBound x b (cvcVar hu)
    have h₂ := occurrenceBound k l (cvcPosition hw.1 hw.2)
    omega
  · have h₁ := occurrenceBound i j (cvcPosition hu.1 hu.2)
    have h₂ := literalBound y b' (cvcVar hw)
    omega
  · rcases cvcPosition hu.1 hu.2 with ⟨hi, hj⟩ | ⟨rfl, rfl⟩ <;>
      rcases cvcPosition hw.1 hw.2 with ⟨hk, hl⟩ | ⟨rfl, rfl⟩
    · rw [hClause i j hi hj, hClause k l hk hl] at hn
      rcases lt_trichotomy i k with hik | rfl | hki
      · have h₁ := next i hi
        have h₂ : off (i + 1) ≤ off k := mono (Nat.succ_le_of_lt hik)
        omega
      · have h : j = l := by omega
        rw [h]
      · have h₁ := next k hk
        have h₂ : off (k + 1) ≤ off i := mono (Nat.succ_le_of_lt hki)
        omega
    · rw [hLast] at hn
      have h := ordinaryBeforeLast i j hi hj
      omega
    · rw [hLast] at hn
      have h := ordinaryBeforeLast k l hk hl
      omega
    · rfl
