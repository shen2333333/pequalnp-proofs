import Mathlib
import PEqualNP.Defs

private def rowColumnForm (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) (ij : Fin 4 × Fin 6) : ℂ :=
  Fin.cases
    (Fin.cases (-(∑ j, x.1 j)) x.1 ij.2)
    (fun i => if ij.2 = 0 then Fin.cases (-(∑ j, x.2 j)) x.2 i else 0)
    ij.1

private def rowColumnMap : ((Fin 5 → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := rowColumnForm
  map_add' x y := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;>
        simp [rowColumnForm, Finset.sum_add_distrib, add_comm]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (x + y).2 l) = -(∑ l, x.2 l) + -(∑ l, y.2 l)
          simp [Finset.sum_add_distrib, add_comm]
        · simp [rowColumnForm]
      · simp [rowColumnForm]
  map_smul' c x := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp [rowColumnForm, Finset.mul_sum]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (c • x).2 l) = c * -(∑ l, x.2 l)
          simp
          ring
        · simp [rowColumnForm]
      · simp [rowColumnForm]

private theorem rowColumnMap_injective : Function.Injective rowColumnMap := by
  intro x y h
  apply Prod.ext
  · funext j
    exact congrFun h ((0 : Fin 4), j.succ)
  · funext i
    have hh := congrFun h (i.succ.succ, (0 : Fin 6))
    exact hh

private def insertPick {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    Fin (n + 1) ↪ Fin (m + 1) :=
  Fin.Embedding.cons (f.trans (finSuccAboveEquiv p).asEmbedding) (a := p) (by
    rintro ⟨i, hi⟩
    exact ((finSuccAboveEquiv p) (f i)).property hi)

private theorem insertPick_zero {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    insertPick p f 0 = p := rfl

private theorem insertPick_succ {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m)
    (i : Fin n) : insertPick p f i.succ = p.succAbove (f i) := rfl

private noncomputable def pickEquiv (n m : ℕ) :
    Fin (m + 1) × (Fin n ↪ Fin m) ≃ (Fin (n + 1) ↪ Fin (m + 1)) :=
  Equiv.ofBijective (fun pf => insertPick pf.1 pf.2) (by
    constructor
    · rintro ⟨p, f⟩ ⟨q, g⟩ h
      have hpq : p = q := congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e 0) h
      subst q
      congr 1
      apply Function.Embedding.ext
      intro i
      apply Fin.succAbove_right_injective
      exact congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e i.succ) h
    · intro e
      let p := e 0
      let f : Fin n ↪ Fin m :=
        ((Fin.Embedding.tail e).codRestrict {j : Fin (m + 1) | j ≠ p} (fun i hi =>
          Fin.succ_ne_zero i (e.injective hi))).trans (finSuccAboveEquiv p).symm.toEmbedding
      refine ⟨(p, f), ?_⟩
      apply Function.Embedding.ext
      intro i
      change insertPick p f i = e i
      refine Fin.cases rfl (fun j => ?_) i
      rw [insertPick_succ]
      exact congrArg Subtype.val ((finSuccAboveEquiv p).apply_symm_apply
        ⟨e j.succ, fun h => Fin.succ_ne_zero j (e.injective h)⟩))

private theorem sumPick {n m : ℕ} (g : (Fin (n + 1) ↪ Fin (m + 1)) → ℂ) :
    (∑ f, g f) = ∑ j : Fin (m + 1), ∑ f : Fin n ↪ Fin m, g (insertPick j f) := by
  rw [← (pickEquiv n m).sum_comp g, Fintype.sum_prod_type]
  rfl

private theorem rowColumnEntry (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) (i : Fin 4) (j : Fin 6) :
    rowColumnForm x (i, j) =
      if i = 0 then
        if j = 0 then -(∑ k, x.1 k)
        else if j = 1 then x.1 0
        else if j = 2 then x.1 1
        else if j = 3 then x.1 2
        else if j = 4 then x.1 3
        else x.1 4
      else if j = 0 then
        if i = 1 then -(∑ k, x.2 k) else if i = 2 then x.2 0 else x.2 1
      else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem rowColumnFiber (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) (j : Fin 6) :
    (∑ f : Fin 3 ↪ Fin 5, ∏ i : Fin 4, (1 + rowColumnForm x (i, insertPick j f i))) =
      60 * (1 + rowColumnForm x (0, j)) := by
  simp only [sumPick (n := 2) (m := 4), sumPick (n := 1) (m := 3),
    sumPick (n := 0) (m := 2)]
  simp only [Fintype.sum_unique, Fin.sum_univ_succ,
    Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  fin_cases j <;>
    simp +decide [rowColumnEntry, Fin.succAbove, Fin.sum_univ_succ] <;> ring

private theorem rowColumnSum (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + rowColumnForm x (i, f i))) = 360 := by
  rw [sumPick]
  simp_rw [rowColumnFiber]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h : (∑ j : Fin 6, rowColumnForm x (0, j)) = 0 := by
    rw [Fin.sum_univ_succ]
    simp [rowColumnForm]
  rw [h]
  norm_num

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
    (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧
    Module.finrank ℂ L = 7 := by
  refine ⟨rowColumnMap.range, ?_, ?_⟩
  · rintro t ⟨x, rfl⟩
    exact rowColumnSum x
  · rw [LinearMap.finrank_range_of_inj rowColumnMap_injective, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    decide
