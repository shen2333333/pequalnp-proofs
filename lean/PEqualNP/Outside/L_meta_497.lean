import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta497

open PEqualNP.Search
open PEqualNP.MetaComplexity.CoverPromise

lemma encodeLiteral_length_ge (l : Literal) : 1 ≤ (encodeLiteral l).length := by
  simp only [encodeLiteral, List.length_append, List.length_cons, List.length_nil]
  omega

lemma encodeClause_length_ge (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  have h : c.length ≤ (c.flatMap encodeLiteral).length := by
    induction c with
    | nil => simp
    | cons l cs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hl := encodeLiteral_length_ge l
      omega
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  omega

lemma sum_len_le_encodeCNF (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
    simp only [encodeCNF, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    have hc := encodeClause_length_ge c
    omega

lemma take_sum_step (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    ((φ.take (i + 1)).map (fun c => c.length + 1)).sum =
      ((φ.take i).map (fun c => c.length + 1)).sum + ((φ.getD i []).length + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  have hget : φ.getD i [] = φ[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hget]

lemma take_sum_mono (φ : CNF) {i i' : ℕ} (h : i ≤ i') :
    ((φ.take i).map (fun c => c.length + 1)).sum ≤
      ((φ.take i').map (fun c => c.length + 1)).sum := by
  induction h with
  | refl => exact le_rfl
  | @step m hm ih =>
    by_cases hlt : m < φ.length
    · rw [take_sum_step φ hlt]
      omega
    · have hge : φ.length ≤ m := Nat.not_lt.mp hlt
      rw [List.take_of_length_le (Nat.le_trans hge (Nat.le_succ m))]
      rw [List.take_of_length_le hge] at ih
      exact ih

lemma take_sum_add_lt_take_sum (φ : CNF) {i i' j : ℕ}
    (hi : i < i') (hi' : i' ≤ φ.length) (hj : j ≤ (φ.getD i []).length) :
    ((φ.take i).map (fun c => c.length + 1)).sum + j <
      ((φ.take i').map (fun c => c.length + 1)).sum := by
  have h1 : i < φ.length := lt_of_lt_of_le hi hi'
  have hstep := take_sum_step φ h1
  have hmono := take_sum_mono φ (show i + 1 ≤ i' by omega)
  omega

lemma take_sum_add_lt_encodeCNF (φ : CNF) {i j : ℕ}
    (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
    ((φ.take i).map (fun c => c.length + 1)).sum + j < (encodeCNF φ).length := by
  have h1 := take_sum_add_lt_take_sum φ hi le_rfl hj
  rw [List.take_length] at h1
  have h2 := sum_len_le_encodeCNF φ
  omega

lemma take_sum_add_inj (φ : CNF) {i i' j j' : ℕ}
    (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length)
    (hi' : i' < φ.length) (hj' : j' ≤ (φ.getD i' []).length)
    (heq : ((φ.take i).map (fun c => c.length + 1)).sum + j =
      ((φ.take i').map (fun c => c.length + 1)).sum + j') :
    i = i' ∧ j = j' := by
  rcases lt_trichotomy i i' with hlt | rfl | hgt
  · exfalso
    have := take_sum_add_lt_take_sum φ hlt (le_of_lt hi') hj
    omega
  · exact ⟨rfl, by omega⟩
  · exfalso
    have := take_sum_add_lt_take_sum φ hgt (le_of_lt hi) hj'
    omega

lemma flatCNF_getElem?_eq (φ : CNF) :
    ∀ (m : ℕ) (l : Literal),
      (φ.flatMap (fun c => c.map some ++ [none]))[m]? = some (some l) →
      ∃ i < φ.length, ∃ j < (φ.getD i []).length,
        m = ((φ.take i).map (fun c => c.length + 1)).sum + j ∧
        (φ.getD i []).getD j (0, false) = l := by
  induction φ with
  | nil =>
    intro m l h
    simp at h
  | cons c cs ih =>
    intro m l h
    simp only [List.flatMap_cons] at h
    by_cases hm1 : m < c.length
    · have hm_lt : m < (c.map some ++ [none]).length := by simp; omega
      rw [List.getElem?_append_left hm_lt] at h
      have hm_lt' : m < (c.map some).length := by simp; omega
      rw [List.getElem?_append_left hm_lt'] at h
      rw [List.getElem?_map, List.getElem?_eq_getElem hm1] at h
      simp only [Option.map_some, Option.some.injEq] at h
      refine ⟨0, by simp, m, by simpa using hm1, by simp, ?_⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm1, h]
    · by_cases hm2 : m = c.length
      · subst hm2
        have hm_lt : c.length < (c.map some ++ [none]).length := by simp
        rw [List.getElem?_append_left hm_lt] at h
        have hge : (c.map some).length ≤ c.length := by simp
        rw [List.getElem?_append_right hge] at h
        simp at h
      · have hge : (c.map some ++ [none]).length ≤ m := by simp; omega
        rw [List.getElem?_append_right hge] at h
        simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at h
        obtain ⟨i, hi, j, hj, hm', hl⟩ := ih (m - (c.length + 1)) l h
        refine ⟨i + 1, by simp; omega, j, by simpa using hj, ?_, by simpa using hl⟩
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega

lemma fresh_not_mem_vars (φ : CNF) : fresh φ ∉ vars φ := by
  intro h
  have hle : fresh φ ≤ (vars φ).sup id := Finset.le_sup (f := id) h
  simp only [fresh] at hle
  omega

lemma mem_vars_of_clause_getD (φ : CNF) {i j : ℕ}
    (hi : i < φ.length) (hj : j < (φ.getD i []).length) :
    ((φ.getD i []).getD j (0, false)).1 ∈ vars φ := by
  have hci : φ.getD i [] = φ[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hmem_c : φ.getD i [] ∈ φ := by
    rw [hci]
    exact List.getElem_mem hi
  have hmem_l : (φ.getD i []).getD j (0, false) ∈ φ.getD i [] := by
    have hget : (φ.getD i []).getD j (0, false) = (φ.getD i [])[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hget]
    exact List.getElem_mem hj
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
  exact ⟨φ.getD i [], hmem_c, (φ.getD i []).getD j (0, false), hmem_l, rfl⟩

lemma vars_cvcFormula (φ : CNF) (z : ℕ) :
    z ∈ vars (cvcFormula φ) ↔ z ∈ vars φ ∨ z = fresh φ := by
  simp only [vars, cvcFormula, List.mem_toFinset, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨c, (⟨c', hc', rfl⟩ | rfl), l, hl, rfl⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with hl | rfl
      · left
        exact ⟨c', hc', l, hl, rfl⟩
      · right
        rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      right
      rfl
  · rintro (⟨c, hc, l, hl, rfl⟩ | rfl)
    · exact ⟨c ++ [(fresh φ, true)], Or.inl ⟨c, hc, rfl⟩, l, List.mem_append_left _ hl, rfl⟩
    · exact ⟨[(fresh φ, false)], Or.inr rfl, (fresh φ, false), by simp, rfl⟩

lemma clauseAt_cvcFormula_lt (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  have hi' : i < (φ.map (fun C => C ++ [(fresh φ, true)])).length := by simp [hi]
  simp only [clauseAt, cvcFormula, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi', List.getElem?_map, List.getElem?_eq_getElem hi]
  simp

lemma clauseAt_cvcFormula_eq (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  have hle : (φ.map (fun C => C ++ [(fresh φ, true)])).length ≤ φ.length := by simp
  simp only [clauseAt, cvcFormula, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right hle]
  simp

lemma clauseAt_cvcFormula_gt (φ : CNF) {i : ℕ} (hi : φ.length < i) :
    clauseAt (cvcFormula φ) i = [] := by
  have hle : (cvcFormula φ).length ≤ i := by
    simp only [cvcFormula, List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  simp only [clauseAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none]

lemma getD_append_fresh_lt (φ : CNF) {i j : ℕ} (hj : j < (φ.getD i []).length) :
    ((φ.getD i []) ++ [(fresh φ, true)]).getD j (0, false) = (φ.getD i []).getD j (0, false) := by
  generalize φ.getD i [] = c at hj ⊢
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma getD_append_fresh_eq (φ : CNF) (i : ℕ) :
    ((φ.getD i []) ++ [(fresh φ, true)]).getD (φ.getD i []).length (0, false) = (fresh φ, true) := by
  generalize φ.getD i [] = c
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

lemma getElem?_append_fresh (φ : CNF) {i j : ℕ} (hj : j ≤ (φ.getD i []).length) :
    ((φ.getD i []) ++ [(fresh φ, true)])[j]? =
      some (((φ.getD i []) ++ [(fresh φ, true)]).getD j (0, false)) := by
  generalize φ.getD i [] = c at hj ⊢
  have hlt : j < (c ++ [(fresh φ, true)]).length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]

lemma mem_inner_iff (k N u v : ℕ) (b : Bool) (x : ℕ) :
    x ∈ ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
        (fun t => N + 2 * k * (u * N + v) + t) ↔
      ∃ t < 2 * k, (t % 2 = 1 ↔ b = true) ∧ x = N + 2 * k * (u * N + v) + t := by
  simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨t, ⟨ht, hb⟩, rfl⟩
    refine ⟨t, ht, ?_, rfl⟩
    cases b <;> simp at hb ⊢ <;> omega
  · rintro ⟨t, ht, hb, rfl⟩
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    cases b <;> simp at hb ⊢ <;> omega

lemma nodup_inner (k N u v : ℕ) (b : Bool) :
    (((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
        (fun t => N + 2 * k * (u * N + v) + t)).Nodup := by
  exact (List.nodup_range.filter _).map (fun t1 t2 h => by omega)

lemma encode_inner_inj {k N u v t u' v' t' : ℕ}
    (_hu : u < N) (hv : v < N) (ht : t < 2 * k)
    (_hu' : u' < N) (hv' : v' < N) (ht' : t' < 2 * k)
    (heq : N + 2 * k * (u * N + v) + t = N + 2 * k * (u' * N + v') + t') :
    u = u' ∧ v = v' ∧ t = t' := by
  have huv : u * N + v = u' * N + v' := by
    rcases lt_trichotomy (u * N + v) (u' * N + v') with hlt | heq' | hgt
    · exfalso
      have h1 : 2 * k * (u * N + v + 1) ≤ 2 * k * (u' * N + v') :=
        Nat.mul_le_mul_left (2 * k) hlt
      have h2 : 2 * k * (u * N + v + 1) = 2 * k * (u * N + v) + 2 * k := by ring
      omega
    · exact heq'
    · exfalso
      have h1 : 2 * k * (u' * N + v' + 1) ≤ 2 * k * (u * N + v) :=
        Nat.mul_le_mul_left (2 * k) hgt
      have h2 : 2 * k * (u' * N + v' + 1) = 2 * k * (u' * N + v') + 2 * k := by ring
      omega
  have htt' : t = t' := by
    rw [huv] at heq
    omega
  have huu' : u = u' := by
    rcases lt_trichotomy u u' with hlt | heq' | hgt
    · exfalso
      have h1 : (u + 1) * N ≤ u' * N := Nat.mul_le_mul_right N hlt
      have h2 : (u + 1) * N = u * N + N := by ring
      omega
    · exact heq'
    · exfalso
      have h1 : (u' + 1) * N ≤ u * N := Nat.mul_le_mul_right N hgt
      have h2 : (u' + 1) * N = u' * N + N := by ring
      omega
  have hvv' : v = v' := by
    rw [huu'] at huv
    omega
  exact ⟨huu', hvv', htt'⟩

lemma nodup_flatMap_of_disjoint {α β : Type*} {L : List α} {f : α → List β}
    (hL : L.Nodup)
    (hnd : ∀ a ∈ L, (f a).Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x, x ∈ f a → x ∉ f b) :
    (L.flatMap f).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hnd, ?_⟩
  exact hL.imp_of_mem fun {a b} ha hb hab => List.disjoint_left.mpr (hdisj a ha b hb hab)

lemma nodup_append_iff_disj {α : Type*} {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hd : ∀ x, x ∈ l1 → x ∉ l2) :
    (l1 ++ l2).Nodup :=
  List.nodup_append.mpr ⟨h1, h2, fun x hx _y hy hxy => hd x hx (hxy ▸ hy)⟩

end PEqualNP.Outside.Meta497

theorem PEqualNP.Outside.L_meta_497 :
    ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal, (∀ i j, lit i j = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) → ∀ inner : ℕ → ℕ → Bool → List ℕ, (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map (fun t => N + 2 * k * (u * N + v) + t)) → ∀ TL : List ℕ, TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else []))) ++ (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) → TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  intro k φ E N off e hE hN hoff he_lt he_inj he_pos num hnum_var hnum_fresh hnum_occ hnum_last
    H hH f _hf TH hTH lit hlit inner hinner TL hTL
  open PEqualNP.Outside.Meta497 PEqualNP.MetaComplexity.CoverPromise in
  have hoff_lt : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → off i + j < E := by
    intro i j hi hj
    rw [hoff i, hE]
    exact take_sum_add_lt_encodeCNF φ hi hj
  have hoff_inj : ∀ i j i' j', i < φ.length → j ≤ (φ.getD i []).length →
      i' < φ.length → j' ≤ (φ.getD i' []).length →
      off i + j = off i' + j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' heq
    rw [hoff i, hoff i'] at heq
    exact take_sum_add_inj φ hi hj hi' hj' heq
  have hlit_var : ∀ i j, i < φ.length → j < (φ.getD i []).length → (lit i j).1 ∈ vars φ := by
    intro i j hi hj
    rw [hlit i j, getD_append_fresh_lt φ hj]
    exact mem_vars_of_clause_getD φ hi hj
  have hlit_fresh : ∀ i, lit i (φ.getD i []).length = (fresh φ, true) := by
    intro i
    rw [hlit i _, getD_append_fresh_eq φ i]
  have hnum_lit_lt : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inl (lit i j)) < 2 * E + 2 := by
    intro i j hi hj
    rcases lt_or_eq_of_le hj with hlt | rfl
    · have hz := hlit_var i j hi hlt
      have hez := he_lt _ hz
      have hnv := hnum_var (lit i j).1 hz (lit i j).2
      rcases hlit_pair : lit i j with ⟨z, b⟩
      rw [hlit_pair] at hnv hez
      dsimp at hnv hez
      rw [hnv]
      cases b <;> simp <;> omega
    · rw [hlit_fresh i, hnum_fresh true]
      simp
  have hnum_lit_TH : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (num (Sum.inl (lit i j))) ↔ (lit i j).2 = true) := by
    intro i j hi hj
    rcases lt_or_eq_of_le hj with hlt | rfl
    · have hz := hlit_var i j hi hlt
      have hez := he_lt _ hz
      rcases hlit_pair : lit i j with ⟨z, b⟩
      rw [hlit_pair] at hz hez
      dsimp at hz hez
      rw [hnum_var z hz b, hTH]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, iff_false, not_or, not_exists, not_and]
        refine ⟨?_, by omega, ?_, by omega⟩
        · intro z' _ h
          omega
        · intro i' _ j' _ _ h
          omega
      · simp only [↓reduceIte, iff_true]
        left
        exact ⟨z, hz, rfl⟩
    · rw [hlit_fresh i, hnum_fresh true, hTH]
      simp
  have hTH_even_var : ∀ z ∈ vars φ, ¬ TH (2 * e z) := by
    intro z hz h
    have hez := he_lt z hz
    rw [hTH] at h
    rcases h with ⟨z', _, h⟩ | h | ⟨i, _, j, _, _, h⟩ | h <;> omega
  have hTH_fresh_false : ¬ TH (2 * E) := by
    intro h
    rw [hTH] at h
    rcases h with ⟨z', _, h⟩ | h | ⟨i, _, j, _, _, h⟩ | h <;> omega
  have hTH_occ : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (num (Sum.inr (i, j))) ↔ j ≠ f i) := by
    intro i j hi hj
    rw [hnum_occ i j hi hj, hTH]
    have hlt := hoff_lt i j hi hj
    constructor
    · rintro (⟨z, hz, heq⟩ | heq | ⟨i', hi', j', hj', hne, heq⟩ | heq)
      · have := he_lt z hz
        omega
      · omega
      · have heq' : off i + j = off i' + j' := by omega
        obtain ⟨rfl, rfl⟩ := hoff_inj i j i' j' hi hj hi' hj' heq'
        exact hne
      · omega
    · intro hne
      right; right; left
      exact ⟨i, hi, j, hj, hne, rfl⟩
  have hvar_witness : ∀ z ∈ vars φ,
      ∃ i < φ.length, ∃ j < (φ.getD i []).length, off i + j = e z ∧ (lit i j).1 = z := by
    intro z hz
    obtain ⟨l, hget, hlz⟩ := he_pos z hz
    obtain ⟨i, hi, j, hj, heq, hgetD⟩ := flatCNF_getElem?_eq φ (e z) l hget
    refine ⟨i, hi, j, hj, ?_, ?_⟩
    · rw [hoff i]
      omega
    · rw [hlit i j, getD_append_fresh_lt φ hj, hgetD, hlz]
  have hinner_mem : ∀ u v b x, x ∈ inner u v b ↔
      ∃ t < 2 * k, (t % 2 = 1 ↔ b = true) ∧ x = N + 2 * k * (u * N + v) + t := by
    intro u v b x
    rw [hinner u v b]
    exact mem_inner_iff k N u v b x
  have hinner_nodup : ∀ u v b, (inner u v b).Nodup := by
    intro u v b
    rw [hinner u v b]
    exact nodup_inner k N u v b
  let pieceA (i j : ℕ) : List ℕ :=
    inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2
  let pieceB (i j : ℕ) : List ℕ :=
    ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
      (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))
  let pieceC (i j : ℕ) : List ℕ :=
    if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
      inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
    else []
  let pieceD (i j : ℕ) : List ℕ :=
    if j ≠ f i then [num (Sum.inr (i, j))] else []
  let pieceF (i j : ℕ) : List ℕ :=
    if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
      [num (Sum.inl ((lit i j).1, true))]
    else []
  let body (i j : ℕ) : List ℕ :=
    pieceA i j ++ pieceB i j ++ pieceC i j ++ pieceD i j ++ pieceF i j
  let tailG1 : List ℕ :=
    inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false
  let tailG2 : List ℕ :=
    inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false
  let tailPair : List ℕ :=
    [num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]
  let mainList : List ℕ :=
    (List.range φ.length).flatMap (fun i =>
      (List.range ((φ.getD i []).length + 1)).flatMap (fun j => body i j))
  let tailList : List ℕ := tailG1 ++ tailG2 ++ tailPair
  have hTL_eq : TL = mainList ++ tailList := hTL
  have hmemA : ∀ {i j x}, i < φ.length → j ≤ (φ.getD i []).length → x ∈ pieceA i j →
      ∃ u < 2 * E + 2, ∃ t < 2 * k,
        x = N + 2 * k * (u * N + (2 * (E + 1) + off i + j)) + t := by
    intro i j x hi hj hx
    rw [hinner_mem] at hx
    obtain ⟨t, ht, _, rfl⟩ := hx
    refine ⟨num (Sum.inl (lit i j)), hnum_lit_lt i j hi hj, t, ht, ?_⟩
    rw [hnum_occ i j hi hj]
  have hmemB : ∀ {i j x}, i < φ.length → j ≤ (φ.getD i []).length → x ∈ pieceB i j →
      ∃ l ≤ (φ.getD i []).length, j < l ∧ ∃ t < 2 * k,
        x = N + 2 * k * ((2 * (E + 1) + off i + j) * N + (2 * (E + 1) + off i + l)) + t := by
    intro i j x hi hj hx
    simp only [pieceB, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    obtain ⟨l, ⟨hl, hjl⟩, hx⟩ := hx
    have hl' : l ≤ (φ.getD i []).length := Nat.lt_succ_iff.mp hl
    rw [hinner_mem] at hx
    obtain ⟨t, ht, _, rfl⟩ := hx
    refine ⟨l, hl', hjl, t, ht, ?_⟩
    rw [hnum_occ i j hi hj, hnum_occ i l hi hl']
  have hmemC : ∀ {i j x}, i < φ.length → j ≤ (φ.getD i []).length → x ∈ pieceC i j →
      j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧
      ∃ t < 2 * k, x = N + 2 * k * ((2 * (off i + j)) * N + (2 * (off i + j) + 1)) + t := by
    intro i j x hi hj hx
    simp only [pieceC] at hx
    split_ifs at hx with hcond
    · rw [hinner_mem] at hx
      obtain ⟨t, ht, _, rfl⟩ := hx
      have hz := hlit_var i j hi hcond.1
      refine ⟨hcond.1, hcond.2, t, ht, ?_⟩
      rw [hnum_var _ hz false, hnum_var _ hz true, ← hcond.2]
      simp
    · simp at hx
  have hmemD : ∀ {i j x}, i < φ.length → j ≤ (φ.getD i []).length → x ∈ pieceD i j →
      j ≠ f i ∧ x = 2 * (E + 1) + off i + j := by
    intro i j x hi hj hx
    simp only [pieceD] at hx
    split_ifs at hx with hne
    · simp only [List.mem_singleton] at hx
      rw [hx, hnum_occ i j hi hj]
      exact ⟨hne, rfl⟩
    · simp at hx
  have hmemF : ∀ {i j x}, i < φ.length → j ≤ (φ.getD i []).length → x ∈ pieceF i j →
      j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧ x = 2 * (off i + j) + 1 := by
    intro i j x hi hj hx
    simp only [pieceF] at hx
    split_ifs at hx with hcond
    · simp only [List.mem_singleton] at hx
      have hz := hlit_var i j hi hcond.1
      refine ⟨hcond.1, hcond.2, ?_⟩
      rw [hx, hnum_var _ hz true, ← hcond.2]
      simp
    · simp at hx
  have hmemG1 : ∀ {x}, x ∈ tailG1 →
      ∃ t < 2 * k, x = N + 2 * k * ((2 * E) * N + (2 * E + 1)) + t := by
    intro x hx
    rw [hinner_mem] at hx
    obtain ⟨t, ht, _, rfl⟩ := hx
    refine ⟨t, ht, ?_⟩
    rw [hnum_fresh false, hnum_fresh true]
    simp
  have hmemG2 : ∀ {x}, x ∈ tailG2 →
      ∃ t < 2 * k, x = N + 2 * k * ((2 * E) * N + (3 * E + 2)) + t := by
    intro x hx
    rw [hinner_mem] at hx
    obtain ⟨t, ht, _, rfl⟩ := hx
    refine ⟨t, ht, ?_⟩
    rw [hnum_fresh false, hnum_last]
    simp
  have hmemPair : ∀ {x}, x ∈ tailPair → x = 2 * E + 1 ∨ x = 3 * E + 2 := by
    intro x hx
    simp only [tailPair, List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hnum_fresh true, hnum_last] at hx
    simpa using hx
  have hbody_nodup : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → (body i j).Nodup := by
    intro i j hi hj
    have hlt := hoff_lt i j hi hj
    have hndA : (pieceA i j).Nodup := hinner_nodup _ _ _
    have hndB : (pieceB i j).Nodup := by
      apply nodup_flatMap_of_disjoint (List.nodup_range.filter _)
      · intro l _
        exact hinner_nodup _ _ _
      · intro l1 hl1 l2 hl2 hne x hx1 hx2
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl1 hl2
        have hl1' : l1 ≤ (φ.getD i []).length := Nat.lt_succ_iff.mp hl1.1
        have hl2' : l2 ≤ (φ.getD i []).length := Nat.lt_succ_iff.mp hl2.1
        rw [hinner_mem] at hx1 hx2
        obtain ⟨t1, ht1, _, hx1⟩ := hx1
        obtain ⟨t2, ht2, _, hx2⟩ := hx2
        rw [hnum_occ i j hi hj, hnum_occ i l1 hi hl1'] at hx1
        rw [hnum_occ i j hi hj, hnum_occ i l2 hi hl2'] at hx2
        have hlt1 := hoff_lt i l1 hi hl1'
        have hlt2 := hoff_lt i l2 hi hl2'
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (hx1.symm.trans hx2)
        omega
    have hndC : (pieceC i j).Nodup := by
      simp only [pieceC]
      split_ifs
      · exact hinner_nodup _ _ _
      · exact List.nodup_nil
    have hndD : (pieceD i j).Nodup := by
      simp only [pieceD]
      split_ifs
      · exact List.nodup_singleton _
      · exact List.nodup_nil
    have hndF : (pieceF i j).Nodup := by
      simp only [pieceF]
      split_ifs
      · exact List.nodup_singleton _
      · exact List.nodup_nil
    have hAB : (pieceA i j ++ pieceB i j).Nodup := by
      apply nodup_append_iff_disj hndA hndB
      intro x hxA hxB
      obtain ⟨u, hu, t1, ht1, hx1⟩ := hmemA hi hj hxA
      obtain ⟨l, hl, _, t2, ht2, hx2⟩ := hmemB hi hj hxB
      have hltl := hoff_lt i l hi hl
      have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (hx1.symm.trans hx2)
      omega
    have hABC : (pieceA i j ++ pieceB i j ++ pieceC i j).Nodup := by
      apply nodup_append_iff_disj hAB hndC
      intro x hxAB hxC
      obtain ⟨_, _, t2, ht2, hx2⟩ := hmemC hi hj hxC
      rcases List.mem_append.mp hxAB with hxA | hxB
      · obtain ⟨u, hu, t1, ht1, hx1⟩ := hmemA hi hj hxA
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (hx1.symm.trans hx2)
        omega
      · obtain ⟨l, hl, _, t1, ht1, hx1⟩ := hmemB hi hj hxB
        have hltl := hoff_lt i l hi hl
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (hx1.symm.trans hx2)
        omega
    have hABCD : (pieceA i j ++ pieceB i j ++ pieceC i j ++ pieceD i j).Nodup := by
      apply nodup_append_iff_disj hABC hndD
      intro x hxABC hxD
      obtain ⟨_, hx2⟩ := hmemD hi hj hxD
      rcases List.mem_append.mp hxABC with hxAB | hxC
      · rcases List.mem_append.mp hxAB with hxA | hxB
        · obtain ⟨_, _, _, _, hx1⟩ := hmemA hi hj hxA
          omega
        · obtain ⟨_, _, _, _, _, hx1⟩ := hmemB hi hj hxB
          omega
      · obtain ⟨_, _, _, _, hx1⟩ := hmemC hi hj hxC
        omega
    apply nodup_append_iff_disj hABCD hndF
    intro x hxABCD hxF
    obtain ⟨_, _, hx2⟩ := hmemF hi hj hxF
    rcases List.mem_append.mp hxABCD with hxABC | hxD
    · rcases List.mem_append.mp hxABC with hxAB | hxC
      · rcases List.mem_append.mp hxAB with hxA | hxB
        · obtain ⟨_, _, _, _, hx1⟩ := hmemA hi hj hxA
          omega
        · obtain ⟨_, _, _, _, _, hx1⟩ := hmemB hi hj hxB
          omega
      · obtain ⟨_, _, _, _, hx1⟩ := hmemC hi hj hxC
        omega
    · obtain ⟨_, hx1⟩ := hmemD hi hj hxD
      omega
  have hbody_off_unique : ∀ {i j i' j' x},
      i < φ.length → j ≤ (φ.getD i []).length →
      i' < φ.length → j' ≤ (φ.getD i' []).length →
      x ∈ body i j → x ∈ body i' j' → off i + j = off i' + j' := by
    intro i j i' j' x hi hj hi' hj' hx1 hx2
    have hlt1 := hoff_lt i j hi hj
    have hlt2 := hoff_lt i' j' hi' hj'
    simp only [body, List.mem_append] at hx1 hx2
    rcases hx1 with (((hx1 | hx1) | hx1) | hx1) | hx1
    · obtain ⟨u1, hu1, t1, ht1, he1⟩ := hmemA hi hj hx1
      rcases hx2 with (((hx2 | hx2) | hx2) | hx2) | hx2
      · obtain ⟨u2, hu2, t2, ht2, he2⟩ := hmemA hi' hj' hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨l2, hl2, _, t2, ht2, he2⟩ := hmemB hi' hj' hx2
        have hltl2 := hoff_lt i' l2 hi' hl2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨_, _, t2, ht2, he2⟩ := hmemC hi' hj' hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨_, he2⟩ := hmemD hi' hj' hx2
        omega
      · obtain ⟨_, _, he2⟩ := hmemF hi' hj' hx2
        omega
    · obtain ⟨l1, hl1, _, t1, ht1, he1⟩ := hmemB hi hj hx1
      have hltl1 := hoff_lt i l1 hi hl1
      rcases hx2 with (((hx2 | hx2) | hx2) | hx2) | hx2
      · obtain ⟨u2, hu2, t2, ht2, he2⟩ := hmemA hi' hj' hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨l2, hl2, _, t2, ht2, he2⟩ := hmemB hi' hj' hx2
        have hltl2 := hoff_lt i' l2 hi' hl2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨_, _, t2, ht2, he2⟩ := hmemC hi' hj' hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨_, he2⟩ := hmemD hi' hj' hx2
        omega
      · obtain ⟨_, _, he2⟩ := hmemF hi' hj' hx2
        omega
    · obtain ⟨_, _, t1, ht1, he1⟩ := hmemC hi hj hx1
      rcases hx2 with (((hx2 | hx2) | hx2) | hx2) | hx2
      · obtain ⟨u2, hu2, t2, ht2, he2⟩ := hmemA hi' hj' hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨l2, hl2, _, t2, ht2, he2⟩ := hmemB hi' hj' hx2
        have hltl2 := hoff_lt i' l2 hi' hl2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨_, _, t2, ht2, he2⟩ := hmemC hi' hj' hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨_, he2⟩ := hmemD hi' hj' hx2
        omega
      · obtain ⟨_, _, he2⟩ := hmemF hi' hj' hx2
        omega
    · obtain ⟨_, he1⟩ := hmemD hi hj hx1
      rcases hx2 with (((hx2 | hx2) | hx2) | hx2) | hx2
      · obtain ⟨_, _, _, _, he2⟩ := hmemA hi' hj' hx2
        omega
      · obtain ⟨_, _, _, _, _, he2⟩ := hmemB hi' hj' hx2
        omega
      · obtain ⟨_, _, _, _, he2⟩ := hmemC hi' hj' hx2
        omega
      · obtain ⟨_, he2⟩ := hmemD hi' hj' hx2
        omega
      · obtain ⟨_, _, he2⟩ := hmemF hi' hj' hx2
        omega
    · obtain ⟨_, _, he1⟩ := hmemF hi hj hx1
      rcases hx2 with (((hx2 | hx2) | hx2) | hx2) | hx2
      · obtain ⟨_, _, _, _, he2⟩ := hmemA hi' hj' hx2
        omega
      · obtain ⟨_, _, _, _, _, he2⟩ := hmemB hi' hj' hx2
        omega
      · obtain ⟨_, _, _, _, he2⟩ := hmemC hi' hj' hx2
        omega
      · obtain ⟨_, he2⟩ := hmemD hi' hj' hx2
        omega
      · obtain ⟨_, _, he2⟩ := hmemF hi' hj' hx2
        omega
  have hmain_nodup : mainList.Nodup := by
    apply nodup_flatMap_of_disjoint List.nodup_range
    · intro i hi
      rw [List.mem_range] at hi
      apply nodup_flatMap_of_disjoint List.nodup_range
      · intro j hj
        rw [List.mem_range] at hj
        exact hbody_nodup i j hi (Nat.lt_succ_iff.mp hj)
      · intro j1 hj1 j2 hj2 hne x hx1 hx2
        rw [List.mem_range] at hj1 hj2
        have heq := hbody_off_unique hi (Nat.lt_succ_iff.mp hj1) hi (Nat.lt_succ_iff.mp hj2) hx1 hx2
        exact hne (hoff_inj i j1 i j2 hi (Nat.lt_succ_iff.mp hj1) hi (Nat.lt_succ_iff.mp hj2) heq).2
    · intro i1 hi1 i2 hi2 hne x hx1 hx2
      rw [List.mem_range] at hi1 hi2
      simp only [List.mem_flatMap, List.mem_range] at hx1 hx2
      obtain ⟨j1, hj1, hx1⟩ := hx1
      obtain ⟨j2, hj2, hx2⟩ := hx2
      have heq := hbody_off_unique hi1 (Nat.lt_succ_iff.mp hj1) hi2 (Nat.lt_succ_iff.mp hj2) hx1 hx2
      exact hne (hoff_inj i1 j1 i2 j2 hi1 (Nat.lt_succ_iff.mp hj1) hi2 (Nat.lt_succ_iff.mp hj2) heq).1
  have htail_nodup : tailList.Nodup := by
    have h12 : (tailG1 ++ tailG2).Nodup := by
      apply nodup_append_iff_disj (hinner_nodup _ _ _) (hinner_nodup _ _ _)
      intro x hx1 hx2
      obtain ⟨t1, ht1, he1⟩ := hmemG1 hx1
      obtain ⟨t2, ht2, he2⟩ := hmemG2 hx2
      have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
      omega
    have hpair : tailPair.Nodup := by
      simp only [tailPair, hnum_fresh true, hnum_last, List.nodup_cons, List.mem_singleton]
      simp
      omega
    apply nodup_append_iff_disj h12 hpair
    intro x hx12 hxP
    rcases hmemPair hxP with he2 | he2
    · rcases List.mem_append.mp hx12 with hx1 | hx2
      · obtain ⟨_, _, he1⟩ := hmemG1 hx1; omega
      · obtain ⟨_, _, he1⟩ := hmemG2 hx2; omega
    · rcases List.mem_append.mp hx12 with hx1 | hx2
      · obtain ⟨_, _, he1⟩ := hmemG1 hx1; omega
      · obtain ⟨_, _, he1⟩ := hmemG2 hx2; omega
  have hmain_tail_disj : ∀ x, x ∈ mainList → x ∉ tailList := by
    intro x hxM hxT
    simp only [mainList, List.mem_flatMap, List.mem_range] at hxM
    obtain ⟨i, hi, j, hj, hxB⟩ := hxM
    have hj' : j ≤ (φ.getD i []).length := Nat.lt_succ_iff.mp hj
    have hlt := hoff_lt i j hi hj'
    simp only [body, List.mem_append] at hxB
    simp only [tailList, List.mem_append] at hxT
    rcases hxB with (((hx1 | hx1) | hx1) | hx1) | hx1
    · obtain ⟨u1, hu1, t1, ht1, he1⟩ := hmemA hi hj' hx1
      rcases hxT with (hx2 | hx2) | hx2
      · obtain ⟨t2, ht2, he2⟩ := hmemG1 hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨t2, ht2, he2⟩ := hmemG2 hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · rcases hmemPair hx2 with he2 | he2 <;> omega
    · obtain ⟨l1, hl1, _, t1, ht1, he1⟩ := hmemB hi hj' hx1
      have hltl1 := hoff_lt i l1 hi hl1
      rcases hxT with (hx2 | hx2) | hx2
      · obtain ⟨t2, ht2, he2⟩ := hmemG1 hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨t2, ht2, he2⟩ := hmemG2 hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · rcases hmemPair hx2 with he2 | he2 <;> omega
    · obtain ⟨_, _, t1, ht1, he1⟩ := hmemC hi hj' hx1
      rcases hxT with (hx2 | hx2) | hx2
      · obtain ⟨t2, ht2, he2⟩ := hmemG1 hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · obtain ⟨t2, ht2, he2⟩ := hmemG2 hx2
        have hinj := encode_inner_inj (by omega) (by omega) ht1 (by omega) (by omega) ht2 (he1.symm.trans he2)
        omega
      · rcases hmemPair hx2 with he2 | he2 <;> omega
    · obtain ⟨_, he1⟩ := hmemD hi hj' hx1
      rcases hxT with (hx2 | hx2) | hx2
      · obtain ⟨_, _, he2⟩ := hmemG1 hx2; omega
      · obtain ⟨_, _, he2⟩ := hmemG2 hx2; omega
      · rcases hmemPair hx2 with he2 | he2 <;> omega
    · obtain ⟨_, _, he1⟩ := hmemF hi hj' hx1
      rcases hxT with (hx2 | hx2) | hx2
      · obtain ⟨_, _, he2⟩ := hmemG1 hx2; omega
      · obtain ⟨_, _, he2⟩ := hmemG2 hx2; omega
      · rcases hmemPair hx2 with he2 | he2 <;> omega
  refine ⟨?_, ?_⟩
  · rw [hTL_eq]
    exact nodup_append_iff_disj hmain_nodup htail_nodup hmain_tail_disj
  · intro x
    rw [hTL_eq]
    constructor
    · intro hx
      rw [List.mem_append] at hx
      rcases hx with hxM | hxT
      · simp only [mainList, List.mem_flatMap, List.mem_range] at hxM
        obtain ⟨i, hi, j, hj, hxB⟩ := hxM
        have hj' : j ≤ (φ.getD i []).length := Nat.lt_succ_iff.mp hj
        have hlt := hoff_lt i j hi hj'
        simp only [body, List.mem_append] at hxB
        rcases hxB with (((hx1 | hx1) | hx1) | hx1) | hx1
        · right
          rw [hinner_mem] at hx1
          obtain ⟨t, ht, hpar, rfl⟩ := hx1
          have hu_lt : num (Sum.inl (lit i j)) < 2 * E + 2 := hnum_lit_lt i j hi hj'
          have hv_eq : num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j := hnum_occ i j hi hj'
          refine ⟨⟨num (Sum.inl (lit i j)), by omega⟩, ⟨num (Sum.inr (i, j)), by omega⟩,
            by show num (Sum.inl (lit i j)) < num (Sum.inr (i, j)); omega, ?_,
            t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inl (lit i j), Sum.inr (i, j), ?_, rfl, rfl⟩
            change satAdj (cvcFormula φ) (Sum.inl (lit i j)) (Sum.inr (i, j))
            simp only [satAdj, clauseAt_cvcFormula_lt φ hi, hlit i j]
            exact getElem?_append_fresh φ hj'
          · exact hpar.trans (hnum_lit_TH i j hi hj').symm
        · right
          simp only [pieceB, List.mem_flatMap, List.mem_filter, List.mem_range,
            decide_eq_true_eq] at hx1
          obtain ⟨l, ⟨hl, hjl⟩, hx1⟩ := hx1
          have hl' : l ≤ (φ.getD i []).length := Nat.lt_succ_iff.mp hl
          have hltl := hoff_lt i l hi hl'
          rw [hinner_mem] at hx1
          obtain ⟨t, ht, hpar, rfl⟩ := hx1
          have hu_eq : num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j := hnum_occ i j hi hj'
          have hv_eq : num (Sum.inr (i, l)) = 2 * (E + 1) + off i + l := hnum_occ i l hi hl'
          refine ⟨⟨num (Sum.inr (i, j)), by omega⟩, ⟨num (Sum.inr (i, l)), by omega⟩,
            by show num (Sum.inr (i, j)) < num (Sum.inr (i, l)); omega, ?_,
            t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inr (i, j), Sum.inr (i, l), ?_, rfl, rfl⟩
            change satAdj (cvcFormula φ) (Sum.inr (i, j)) (Sum.inr (i, l))
            simp only [satAdj, clauseAt_cvcFormula_lt φ hi, List.length_append,
              List.length_cons, List.length_nil]
            exact ⟨trivial, Nat.ne_of_lt hjl, by omega, by omega⟩
          · rw [decide_eq_true_eq] at hpar
            exact hpar.trans (hTH_occ i j hi hj').symm
        · right
          simp only [pieceC] at hx1
          split_ifs at hx1 with hcond
          · rw [hinner_mem] at hx1
            obtain ⟨t, ht, hpar, rfl⟩ := hx1
            have hz := hlit_var i j hi hcond.1
            have hez := he_lt _ hz
            have hu_eq : num (Sum.inl ((lit i j).1, false)) = 2 * e (lit i j).1 := by
              rw [hnum_var _ hz false]; simp
            have hv_eq : num (Sum.inl ((lit i j).1, true)) = 2 * e (lit i j).1 + 1 := by
              rw [hnum_var _ hz true]; simp
            refine ⟨⟨num (Sum.inl ((lit i j).1, false)), by omega⟩,
              ⟨num (Sum.inl ((lit i j).1, true)), by omega⟩,
              by show num (Sum.inl ((lit i j).1, false)) < num (Sum.inl ((lit i j).1, true)); omega,
              ?_, t, ht, rfl, ?_⟩
            · rw [hH]
              refine ⟨Sum.inl ((lit i j).1, false), Sum.inl ((lit i j).1, true), ?_, rfl, rfl⟩
              change satAdj (cvcFormula φ) (Sum.inl ((lit i j).1, false)) (Sum.inl ((lit i j).1, true))
              simp only [satAdj, ne_eq, Bool.false_eq_true, not_false_eq_true, true_and]
              exact (vars_cvcFormula φ _).mpr (Or.inl hz)
            · simp only [Bool.false_eq_true, iff_false] at hpar
              have hnTH : ¬ TH (num (Sum.inl ((lit i j).1, false))) := by
                rw [hu_eq]
                exact hTH_even_var _ hz
              exact ⟨fun h => (hpar h).elim, fun h => (hnTH h).elim⟩
          · simp at hx1
        · left
          obtain ⟨hne, heq⟩ := hmemD hi hj' hx1
          rw [hTH]
          right; right; left
          exact ⟨i, hi, j, hj', hne, heq⟩
        · left
          obtain ⟨hjl, hoff_eq, heq⟩ := hmemF hi hj' hx1
          have hz := hlit_var i j hi hjl
          rw [hTH]
          left
          refine ⟨(lit i j).1, hz, ?_⟩
          rw [heq, hoff_eq]
      · simp only [tailList, List.mem_append] at hxT
        rcases hxT with (hx1 | hx1) | hx1
        · right
          rw [hinner_mem] at hx1
          obtain ⟨t, ht, hpar, rfl⟩ := hx1
          have hu_eq : num (Sum.inl (fresh φ, false)) = 2 * E := by rw [hnum_fresh false]; simp
          have hv_eq : num (Sum.inl (fresh φ, true)) = 2 * E + 1 := by rw [hnum_fresh true]; simp
          refine ⟨⟨num (Sum.inl (fresh φ, false)), by omega⟩,
            ⟨num (Sum.inl (fresh φ, true)), by omega⟩,
            by show num (Sum.inl (fresh φ, false)) < num (Sum.inl (fresh φ, true)); omega,
            ?_, t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inl (fresh φ, false), Sum.inl (fresh φ, true), ?_, rfl, rfl⟩
            change satAdj (cvcFormula φ) (Sum.inl (fresh φ, false)) (Sum.inl (fresh φ, true))
            simp only [satAdj, ne_eq, Bool.false_eq_true, not_false_eq_true, true_and]
            exact (vars_cvcFormula φ _).mpr (Or.inr rfl)
          · simp only [Bool.false_eq_true, iff_false] at hpar
            have hnTH : ¬ TH (num (Sum.inl (fresh φ, false))) := by
              rw [hu_eq]; exact hTH_fresh_false
            exact ⟨fun h => (hpar h).elim, fun h => (hnTH h).elim⟩
        · right
          rw [hinner_mem] at hx1
          obtain ⟨t, ht, hpar, rfl⟩ := hx1
          have hu_eq : num (Sum.inl (fresh φ, false)) = 2 * E := by rw [hnum_fresh false]; simp
          have hv_eq : num (Sum.inr (φ.length, 0)) = 3 * E + 2 := hnum_last
          refine ⟨⟨num (Sum.inl (fresh φ, false)), by omega⟩,
            ⟨num (Sum.inr (φ.length, 0)), by omega⟩,
            by show num (Sum.inl (fresh φ, false)) < num (Sum.inr (φ.length, 0)); omega,
            ?_, t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inl (fresh φ, false), Sum.inr (φ.length, 0), ?_, rfl, rfl⟩
            change satAdj (cvcFormula φ) (Sum.inl (fresh φ, false)) (Sum.inr (φ.length, 0))
            simp only [satAdj, clauseAt_cvcFormula_eq φ]
            rfl
          · simp only [Bool.false_eq_true, iff_false] at hpar
            have hnTH : ¬ TH (num (Sum.inl (fresh φ, false))) := by
              rw [hu_eq]; exact hTH_fresh_false
            exact ⟨fun h => (hpar h).elim, fun h => (hnTH h).elim⟩
        · left
          rcases hmemPair hx1 with rfl | rfl
          · rw [hTH]; right; left; rfl
          · rw [hTH]; right; right; right; rfl
    · intro hx
      rcases hx with hTHx | ⟨u, v, huv, hadj, t, ht, rfl, hpar⟩
      · rw [hTH] at hTHx
        rcases hTHx with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl
        · obtain ⟨i, hi, j, hj, hoff_eq, hlitz⟩ := hvar_witness z hz
          apply List.mem_append_left
          simp only [mainList, List.mem_flatMap, List.mem_range]
          refine ⟨i, hi, j, by omega, ?_⟩
          simp only [body, List.mem_append]
          right
          simp only [pieceF, hj, hlitz, hoff_eq, and_self, ↓reduceIte, List.mem_singleton]
          rw [hnum_var z hz true]
          simp
        · apply List.mem_append_right
          simp only [tailList, tailPair, List.mem_append, List.mem_cons]
          right; left
          rw [hnum_fresh true]
          simp
        · apply List.mem_append_left
          simp only [mainList, List.mem_flatMap, List.mem_range]
          refine ⟨i, hi, j, by omega, ?_⟩
          simp only [body, List.mem_append]
          left; right
          dsimp only [pieceD]
          split_ifs
          simp only [List.mem_singleton]
          exact (hnum_occ i j hi hj).symm
        · apply List.mem_append_right
          simp only [tailList, tailPair, List.mem_append, List.mem_cons]
          right; right; left
          exact hnum_last.symm
      · rw [hH] at hadj
        obtain ⟨p, q, hpq, hpu, hqv⟩ := hadj
        have huv' : num p < num q := by
          rw [hpu, hqv]
          exact huv
        rcases p with ⟨zp, bp⟩ | ⟨ip, jp⟩ <;> rcases q with ⟨zq, bq⟩ | ⟨iq, jq⟩
        · change satAdj (cvcFormula φ) (Sum.inl (zp, bp)) (Sum.inl (zq, bq)) at hpq
          simp only [satAdj] at hpq
          obtain ⟨hz_eq, hbne, hzp_mem⟩ := hpq
          subst hz_eq
          rw [vars_cvcFormula] at hzp_mem
          rcases hzp_mem with hzp | rfl
          · have hbp : bp = false ∧ bq = true := by
              rw [hnum_var zp hzp bp, hnum_var zp hzp bq] at huv'
              cases bp <;> cases bq <;> simp at hbne huv' ⊢
            obtain ⟨rfl, rfl⟩ := hbp
            obtain ⟨i, hi, j, hj, hoff_eq, hlitz⟩ := hvar_witness zp hzp
            apply List.mem_append_left
            simp only [mainList, List.mem_flatMap, List.mem_range]
            refine ⟨i, hi, j, by omega, ?_⟩
            simp only [body, List.mem_append]
            left; left; right
            simp only [pieceC, hj, hlitz, hoff_eq, and_self, ↓reduceIte]
            rw [hinner_mem]
            refine ⟨t, ht, ?_, ?_⟩
            · have hnTH : ¬ TH u.val := by
                rw [← hpu, hnum_var zp hzp false]
                simpa using hTH_even_var zp hzp
              simp only [Bool.false_eq_true, iff_false]
              intro h1
              exact hnTH (hpar.mp h1)
            · rw [← hpu, ← hqv]
          · have hbp : bp = false ∧ bq = true := by
              rw [hnum_fresh bp, hnum_fresh bq] at huv'
              cases bp <;> cases bq <;> simp at hbne huv' ⊢
            obtain ⟨rfl, rfl⟩ := hbp
            apply List.mem_append_right
            simp only [tailList, List.mem_append]
            left; left
            rw [hinner_mem]
            refine ⟨t, ht, ?_, ?_⟩
            · have hnTH : ¬ TH u.val := by
                rw [← hpu, hnum_fresh false]
                simpa using hTH_fresh_false
              simp only [Bool.false_eq_true, iff_false]
              intro h1
              exact hnTH (hpar.mp h1)
            · rw [← hpu, ← hqv]
        · change satAdj (cvcFormula φ) (Sum.inl (zp, bp)) (Sum.inr (iq, jq)) at hpq
          simp only [satAdj] at hpq
          rcases lt_trichotomy iq φ.length with hiq | rfl | hiq
          · rw [clauseAt_cvcFormula_lt φ hiq] at hpq
            have hjq : jq ≤ (φ.getD iq []).length := by
              have hlt_len : jq < (φ.getD iq [] ++ [(fresh φ, true)]).length := by
                by_contra h
                rw [List.getElem?_eq_none (Nat.not_lt.mp h)] at hpq
                simp at hpq
              simp only [List.length_append, List.length_cons, List.length_nil] at hlt_len
              omega
            have hlit_eq : (zp, bp) = lit iq jq := by
              rw [getElem?_append_fresh φ hjq, Option.some.injEq] at hpq
              rw [hlit iq jq, hpq]
            apply List.mem_append_left
            simp only [mainList, List.mem_flatMap, List.mem_range]
            refine ⟨iq, hiq, jq, by omega, ?_⟩
            simp only [body, List.mem_append]
            left; left; left; left
            rw [hinner_mem]
            refine ⟨t, ht, ?_, ?_⟩
            · rw [hpar, ← hpu, hlit_eq]
              exact hnum_lit_TH iq jq hiq hjq
            · rw [← hpu, ← hqv, hlit_eq]
          · rw [clauseAt_cvcFormula_eq φ] at hpq
            have hjq : jq = 0 := by
              cases jq with
              | zero => rfl
              | succ m => simp at hpq
            subst hjq
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hpq
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpq
            apply List.mem_append_right
            simp only [tailList, List.mem_append]
            left; right
            rw [hinner_mem]
            refine ⟨t, ht, ?_, ?_⟩
            · have hnTH : ¬ TH u.val := by
                rw [← hpu, hnum_fresh false]
                simpa using hTH_fresh_false
              simp only [Bool.false_eq_true, iff_false]
              intro h1
              exact hnTH (hpar.mp h1)
            · rw [← hpu, ← hqv]
          · rw [clauseAt_cvcFormula_gt φ hiq] at hpq
            simp at hpq
        · exfalso
          change satAdj (cvcFormula φ) (Sum.inr (ip, jp)) (Sum.inl (zq, bq)) at hpq
          simp only [satAdj] at hpq
          rcases lt_trichotomy ip φ.length with hip | rfl | hip
          · rw [clauseAt_cvcFormula_lt φ hip] at hpq
            have hjp : jp ≤ (φ.getD ip []).length := by
              have hlt_len : jp < (φ.getD ip [] ++ [(fresh φ, true)]).length := by
                by_contra h
                rw [List.getElem?_eq_none (Nat.not_lt.mp h)] at hpq
                simp at hpq
              simp only [List.length_append, List.length_cons, List.length_nil] at hlt_len
              omega
            have hlit_eq : (zq, bq) = lit ip jp := by
              rw [getElem?_append_fresh φ hjp, Option.some.injEq] at hpq
              rw [hlit ip jp, hpq]
            have hq_lt : num (Sum.inl (zq, bq)) < 2 * E + 2 := by
              rw [hlit_eq]
              exact hnum_lit_lt ip jp hip hjp
            have hp_eq : num (Sum.inr (ip, jp)) = 2 * (E + 1) + off ip + jp :=
              hnum_occ ip jp hip hjp
            omega
          · rw [clauseAt_cvcFormula_eq φ] at hpq
            have hjp : jp = 0 := by
              cases jp with
              | zero => rfl
              | succ m => simp at hpq
            subst hjp
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hpq
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpq
            rw [hnum_last, hnum_fresh false] at huv'
            simp at huv'
            omega
          · rw [clauseAt_cvcFormula_gt φ hip] at hpq
            simp at hpq
        · change satAdj (cvcFormula φ) (Sum.inr (ip, jp)) (Sum.inr (iq, jq)) at hpq
          simp only [satAdj] at hpq
          obtain ⟨hi_eq, hjne, hjp_len, hjq_len⟩ := hpq
          subst hi_eq
          rcases lt_trichotomy ip φ.length with hip | rfl | hip
          · rw [clauseAt_cvcFormula_lt φ hip, List.length_append, List.length_cons,
              List.length_nil] at hjp_len hjq_len
            have hjp' : jp ≤ (φ.getD ip []).length := by omega
            have hjq' : jq ≤ (φ.getD ip []).length := by omega
            have hlt_j : jp < jq := by
              rw [hnum_occ ip jp hip hjp', hnum_occ ip jq hip hjq'] at huv'
              omega
            apply List.mem_append_left
            simp only [mainList, List.mem_flatMap, List.mem_range]
            refine ⟨ip, hip, jp, by omega, ?_⟩
            simp only [body, List.mem_append]
            left; left; left; right
            simp only [pieceB, List.mem_flatMap, List.mem_filter, List.mem_range,
              decide_eq_true_eq]
            refine ⟨jq, ⟨by omega, hlt_j⟩, ?_⟩
            rw [hinner_mem]
            refine ⟨t, ht, ?_, ?_⟩
            · rw [hpar, ← hpu, decide_eq_true_eq]
              exact hTH_occ ip jp hip hjp'
            · rw [← hpu, ← hqv]
          · rw [clauseAt_cvcFormula_eq φ] at hjp_len hjq_len
            simp at hjp_len hjq_len
            omega
          · rw [clauseAt_cvcFormula_gt φ hip] at hjp_len
            simp at hjp_len
