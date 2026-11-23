import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

private lemma rowBefore (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using hi : i < (φ.map (fun C => C ++ [(fresh φ, true)])).length),
    List.getElem?_eq_getElem hi]

private lemma rowLast (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD]

private lemma rowAfter (φ : CNF) {i : ℕ} (hi : φ.length < i) :
    clauseAt (cvcFormula φ) i = [] := by
  have h : (cvcFormula φ).length ≤ i := by simp [cvcFormula]; omega
  simp [clauseAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private lemma varCases (φ : CNF) {z : ℕ} (h : z ∈ vars (cvcFormula φ)) :
    z ∈ vars φ ∨ z = fresh φ := by
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map] at h ⊢
  obtain ⟨c, hc, l, hl, rfl⟩ := h
  simp only [cvcFormula, List.mem_append, List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨c, hc, rfl⟩ | rfl
  · simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact Or.inl ⟨c, hc, l, hl, rfl⟩
    · exact Or.inr rfl
  · simp only [List.mem_singleton] at hl
    subst l
    exact Or.inr rfl

private lemma occVar (φ : CNF) {i j z : ℕ} {b : Bool}
    (h : (clauseAt (cvcFormula φ) i)[j]? = some (z,b)) :
    z ∈ vars (cvcFormula φ) := by
  have hl := List.mem_of_getElem? h
  have hi : i < (cvcFormula φ).length := by
    by_contra! hn
    simp [clauseAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hn] at h
  have hc : clauseAt (cvcFormula φ) i ∈ cvcFormula φ := by
    simp [clauseAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
  exact ⟨_, hc, _, hl, rfl⟩

private lemma encodingSpace (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  have hc (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
    have hh : c.length ≤ (c.flatMap encodeLiteral).length := by
      induction c with
      | nil => simp
      | cons l c ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        have hp : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
        omega
    simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]; omega
  induction φ with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
    simp only [encodeCNF, List.flatMap_cons, List.length_append] at *
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hc c) ih

private lemma offsetStep (φ : CNF) (off : ℕ → ℕ)
    (ho : ∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum)
    {i : ℕ} (hi : i < φ.length) :
    off (i+1) = off i + (φ.getD i []).length + 1 := by
  rw [ho (i+1), ho i, List.take_succ_eq_append_getElem hi]
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, Nat.add_assoc]

private lemma offsetMono (φ : CNF) (off : ℕ → ℕ)
    (ho : ∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) :
    Monotone off := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases h : i < φ.length
  · rw [offsetStep φ off ho h]; omega
  · rw [ho, ho, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_meta_496 : ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ u v : Fin N, u < v → H.Adj u v → (TH u.val ∨ TH v.val) ∧ ((u.val % 2 = 0 ∧ v.val = u.val + 1 ∧ v.val < 2 * (E + 1) ∧ ¬ TH u.val) ∨ (∃ i < φ.length, ∃ j l : ℕ, j < l ∧ l ≤ (φ.getD i []).length ∧ u.val = 2 * (E + 1) + off i + j ∧ v.val = 2 * (E + 1) + off i + l ∧ (TH u.val ↔ j ≠ f i)) ∨ (u.val < 2 * (E + 1) ∧ 2 * (E + 1) ≤ v.val ∧ (TH u.val ↔ u.val % 2 = 1))) := by
  classical
  intro φ E N off e hE _ hOff he _ num hnum hnew hrow hlast H hH f hf TH hTH u v huv hadj
  have ht (a : ℕ) (ha : a < 2 * (E+1)) (hz : ∃ w ∈ vars φ, a = 2 * e w + 1 ∨ a = 2 * e w) :
      TH a ↔ a % 2 = 1 := by
    rw [hTH]
    obtain ⟨w, hw, ha'⟩ := hz
    constructor
    · rintro (⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hn, rfl⟩ | rfl) <;> omega
    · intro hp
      exact Or.inl ⟨w, hw, by omega⟩
  have hvnum (z : ℕ) (b : Bool) (hz : z ∈ vars (cvcFormula φ)) :
      num (.inl (z,b)) < 2 * (E+1) ∧
      num (.inl (z,b)) % 2 = (if b then 1 else 0) ∧
      (TH (num (.inl (z,b))) ↔ b = true) := by
    rcases varCases φ hz with hz | rfl
    · have h := hnum z hz b
      have he' := he z hz
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at * <;>
        rw [h] <;> refine ⟨by omega, by omega, ?_⟩
      · rw [ht _ (by omega) ⟨z, hz, Or.inr rfl⟩]; simp
      · rw [ht _ (by omega) ⟨z, hz, Or.inl rfl⟩]; simp
    · rw [hnew b]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;>
        refine ⟨by omega, by omega, ?_⟩ <;> rw [hTH]
      · constructor
        · rintro (⟨w, hw, hh⟩ | hh | ⟨i, hi, j, hj, hn, hh⟩ | hh) <;> omega
        · intro hh; contradiction
      · exact iff_of_true (Or.inr (Or.inl rfl)) trivial
  have mono := offsetMono φ off hOff
  have hMax : off φ.length ≤ E := by
    rw [hOff, hE, List.take_length]
    exact encodingSpace φ
  have hend (i j : ℕ) (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      off i + j < off (i+1) := by rw [offsetStep φ off hOff hi]; omega
  have unique (i j k l : ℕ) (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length)
      (hk : k < φ.length) (hl : l ≤ (φ.getD k []).length)
      (hh : off i + j = off k + l) : i = k ∧ j = l := by
    have hh' : i = k := by
      by_contra! hn
      rcases lt_or_gt_of_ne hn with h | h
      · have := mono (show i+1 ≤ k by omega)
        have := hend i j hi hj
        omega
      · have := mono (show k+1 ≤ i by omega)
        have := hend k l hk hl
        omega
    subst k
    exact ⟨rfl, by omega⟩
  have hocc (i j : ℕ) (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      TH (num (.inr (i,j))) ↔ j ≠ f i := by
    rw [hrow i j hi hj, hTH]
    have hh := hend i j hi hj
    have hm := mono (show i+1 ≤ φ.length by omega)
    constructor
    · rintro (⟨z, hz, hh'⟩ | hh' | ⟨k, hk, l, hl, hn, hh'⟩ | hh')
      · have := he z hz
        omega
      · omega
      · obtain ⟨rfl, rfl⟩ := unique i j k l hi hj hk hl (by omega)
        exact hn
      · omega
    · exact fun hn => Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, hn, rfl⟩))
  have occInfo (i j z : ℕ) (b : Bool) (ha : (clauseAt (cvcFormula φ) i)[j]? = some (z,b)) :
      2*(E+1) ≤ num (.inr (i,j)) ∧ (b = true ∨ TH (num (.inr (i,j)))) := by
    by_cases hi : i < φ.length
    · rw [rowBefore φ hi] at ha
      have hj := (List.getElem?_eq_some_iff.mp ha).1
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      have hj' : j ≤ (φ.getD i []).length := by omega
      refine ⟨by rw [hrow i j hi hj']; omega, ?_⟩
      by_cases hn : j = f i
      · left
        rw [hn, hf] at ha
        exact List.findIdx_of_getElem?_eq_some ha
      · exact Or.inr ((hocc i j hi hj').2 hn)
    · by_cases heq : i = φ.length
      · subst i
        rw [rowLast] at ha
        have hj := (List.getElem?_eq_some_iff.mp ha).1
        simp only [List.length_cons, List.length_nil] at hj
        have hj0 : j = 0 := by omega
        subst j
        rw [hlast]
        exact ⟨by omega, Or.inr ((hTH _).2 (Or.inr (Or.inr (Or.inr rfl))))⟩
      · rw [rowAfter φ (by omega)] at ha
        simp at ha
  obtain ⟨a, b, ha, nau, nbv⟩ := (hH u v).1 hadj
  have hh : num a < num b := by simpa only [nau, nbv] using (show u.val < v.val from huv)
  rw [← nau, ← nbv]
  rcases a with ⟨z, p⟩ | ⟨i, j⟩ <;> rcases b with ⟨w, q⟩ | ⟨k, l⟩
  · change z = w ∧ p ≠ q ∧ z ∈ vars (cvcFormula φ) at ha
    obtain ⟨rfl, hne, hz⟩ := ha
    obtain ⟨hp1,hp2,hp3⟩ := hvnum z p hz
    obtain ⟨hq1,hq2,hq3⟩ := hvnum z q hz
    have near : num (.inl (z,true)) = num (.inl (z,false)) + 1 := by
      rcases varCases φ hz with hz | rfl
      · rw [hnum z hz true, hnum z hz false]; rfl
      · rw [hnew true, hnew false]; rfl
    cases p <;> cases q
    · exact False.elim (hne rfl)
    · exact ⟨Or.inr (hq3.2 rfl), Or.inl ⟨hp2, near, hq1, fun h => Bool.noConfusion (hp3.1 h)⟩⟩
    · omega
    · exact False.elim (hne rfl)
  · change (clauseAt (cvcFormula φ) k)[l]? = some (z,p) at ha
    obtain ⟨ha1,ha2,ha3⟩ := hvnum z p (occVar φ ha)
    obtain ⟨hb1,hb2⟩ := occInfo k l z p ha
    refine ⟨hb2.imp ha3.mpr id, Or.inr (Or.inr ⟨ha1, hb1, ?_⟩)⟩
    rw [ha3, ha2]
    cases p <;> simp
  · change (clauseAt (cvcFormula φ) i)[j]? = some (w,q) at ha
    have ha1 := (hvnum w q (occVar φ ha)).1
    have hb1 := (occInfo i j w q ha).1
    omega
  · change i = k ∧ j ≠ l ∧ j < (clauseAt (cvcFormula φ) i).length ∧ l < (clauseAt (cvcFormula φ) i).length at ha
    obtain ⟨rfl, hne, hj, hl⟩ := ha
    have hi : i < φ.length := by
      by_contra! hn
      rcases eq_or_lt_of_le hn with h | h
      · subst i
        rw [rowLast] at hj hl
        simp only [List.length_cons, List.length_nil] at hj hl
        omega
      · rw [rowAfter φ h] at hj
        simp at hj
    rw [rowBefore φ hi] at hj hl
    simp only [List.length_append, List.length_cons, List.length_nil] at hj hl
    have hj' : j ≤ (φ.getD i []).length := by omega
    have hl' : l ≤ (φ.getD i []).length := by omega
    have hjnum := hrow i j hi hj'
    have hlnum := hrow i l hi hl'
    have hthj := hocc i j hi hj'
    have hthl := hocc i l hi hl'
    refine ⟨?_, Or.inr (Or.inl ⟨i, hi, j, l, by omega, hl', hjnum, hlnum, hthj⟩)⟩
    by_cases h : j = f i
    · exact Or.inr (hthl.mpr (by omega))
    · exact Or.inl (hthj.mpr h)
