import Mathlib
import PEqualNP.Defs

-- Adapted from the repository's L_gct_180 construction: remove its zero fifth column
-- and impose that the last row sums to zero in the first four columns.
namespace PEqualNP.Outside.L_gct_197_aux

noncomputable def ω : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private lemma ω_sq_add : ω ^ 2 + ω + 1 = 0 := by
  apply Complex.ext
  · simp only [ω, sq, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    linarith
  · simp only [ω, sq, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im]
    ring

private lemma ω_sq : ω ^ 2 = -ω - 1 := by linear_combination ω_sq_add
private lemma ω_cube : ω ^ 3 = 1 := by linear_combination (ω - 1) * ω_sq_add

private lemma sum_ite_eq_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (a : ι) :
    (∑ x : ι, if a = x then f x else 0) = f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa.symm]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma sum_omit_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (a : ι) :
    (∑ x : ι, if a = x then (0 : ℂ) else f x) = (∑ x : ι, f x) - f a := by
  have h : (∑ x : ι, if a = x then (0 : ℂ) else f x) +
      (∑ x : ι, if a = x then f x else 0) = ∑ x : ι, f x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [sum_ite_eq_self] at h
  linear_combination h

private lemma sum_omit_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) {a b : ι} (hab : a ≠ b) :
    (∑ x : ι, if a = x ∨ b = x then (0 : ℂ) else f x) = (∑ x : ι, f x) - f a - f b := by
  have h : (∑ x : ι, if a = x ∨ b = x then (0 : ℂ) else f x) +
      (∑ x : ι, if a = x then f x else 0) +
      (∑ x : ι, if b = x then f x else 0) = ∑ x : ι, f x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : a = x <;> by_cases h2 : b = x
    · exact absurd (h1.trans h2.symm) hab
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  rw [sum_ite_eq_self, sum_ite_eq_self] at h
  linear_combination h

private lemma sum_omit_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ x : ι, if a = x ∨ b = x ∨ c = x then (0 : ℂ) else f x) =
      (∑ x : ι, f x) - f a - f b - f c := by
  have h : (∑ x : ι, if a = x ∨ b = x ∨ c = x then (0 : ℂ) else f x) +
      (∑ x : ι, if a = x then f x else 0) +
      (∑ x : ι, if b = x then f x else 0) +
      (∑ x : ι, if c = x then f x else 0) = ∑ x : ι, f x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : a = x <;> by_cases h2 : b = x <;> by_cases h3 : c = x
    · exact absurd (h1.trans h2.symm) hab
    · exact absurd (h1.trans h2.symm) hab
    · exact absurd (h1.trans h3.symm) hac
    · simp [h1, h2, h3]
    · exact absurd (h2.trans h3.symm) hbc
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
  rw [sum_ite_eq_self, sum_ite_eq_self, sum_ite_eq_self] at h
  linear_combination h

private lemma sum_distinct2_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℂ) :
    (∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else f j * g l) =
      (∑ j : ι, f j) * (∑ l : ι, g l) - ∑ j : ι, f j * g j := by
  have h : ∀ j : ι, (∑ l : ι, if j = l then (0 : ℂ) else f j * g l) =
      f j * (∑ l : ι, g l) - f j * g j := by
    intro j
    have h1 : (∑ l : ι, if j = l then (0 : ℂ) else f j * g l) =
        f j * (∑ l : ι, if j = l then (0 : ℂ) else g l) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> ring
    rw [h1, sum_omit_one g j]
    ring
  simp_rw [h, Finset.sum_sub_distrib, ← Finset.sum_mul]

private lemma sum_distinct3_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g h : ι → ℂ) (hg : ∑ l : ι, g l = 0) (hh : ∑ m : ι, h m = 0) :
    (∑ j : ι, ∑ l : ι, ∑ m : ι,
      if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f j * g l * h m) =
      2 * (∑ j : ι, f j * g j * h j) - (∑ j : ι, f j) * (∑ l : ι, g l * h l) := by
  have step1 : ∀ j l : ι,
      (∑ m : ι, if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f j * g l * h m) =
        if j = l then 0 else -(f j * h j * g l) - f j * (g l * h l) := by
    intro j l
    by_cases hjl : j = l
    · simp [hjl]
    · simp only [hjl, false_or, ite_false]
      have h1 : (∑ m : ι, if j = m ∨ l = m then (0 : ℂ) else f j * g l * h m) =
          f j * g l * (∑ m : ι, if j = m ∨ l = m then (0 : ℂ) else h m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> ring
      rw [h1, sum_omit_two h hjl, hh]
      ring
  simp_rw [step1]
  have split_sum :
      (∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else -(f j * h j * g l) - f j * (g l * h l)) =
        -(∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else (f j * h j) * g l) -
        (∑ j : ι, ∑ l : ι, if j = l then (0 : ℂ) else f j * (g l * h l)) := by
    simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  rw [split_sum, sum_distinct2_gen (fun j => f j * h j) g,
    sum_distinct2_gen f (fun l => g l * h l), hg]
  have hmul : (∑ j : ι, f j * h j * g j) = ∑ j : ι, f j * g j * h j :=
    Finset.sum_congr rfl fun j _ => by ring
  have hmul2 : (∑ j : ι, f j * (g j * h j)) = ∑ j : ι, f j * g j * h j :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hmul, hmul2]
  ring

private lemma sum_distinct4 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f0 f1 f2 f3 : ι → ℂ)
    (h0 : ∑ j : ι, f0 j = 0) (h1 : ∑ j : ι, f1 j = 0)
    (h2 : ∑ j : ι, f2 j = 0) (h3 : ∑ j : ι, f3 j = 0) :
    (∑ j : ι, ∑ l : ι, ∑ m : ι, ∑ n : ι,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
      else f0 j * f1 l * f2 m * f3 n) =
      (∑ j : ι, f0 j * f3 j) * (∑ l : ι, f1 l * f2 l) +
      (∑ j : ι, f1 j * f3 j) * (∑ l : ι, f0 l * f2 l) +
      (∑ j : ι, f2 j * f3 j) * (∑ l : ι, f0 l * f1 l) -
      6 * (∑ j : ι, f0 j * f1 j * f2 j * f3 j) := by
  have step1 : ∀ j l m : ι,
      (∑ n : ι, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
        else f0 j * f1 l * f2 m * f3 n) =
        if j = l ∨ j = m ∨ l = m then 0
        else -(f0 j * f3 j * f1 l * f2 m) - (f1 l * f3 l * f0 j * f2 m) -
          (f2 m * f3 m * f0 j * f1 l) := by
    intro j l m
    by_cases hcond : j = l ∨ j = m ∨ l = m
    · have hcond' : ∀ n : ι, j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n := by
        intro n
        rcases hcond with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      simp [hcond, hcond']
    · push Not at hcond
      rcases hcond with ⟨hjl, hjm, hlm⟩
      have hn : ∀ n : ι,
          (if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
            else f0 j * f1 l * f2 m * f3 n) =
          f0 j * f1 l * f2 m * (if j = n ∨ l = n ∨ m = n then (0 : ℂ) else f3 n) := by
        intro n
        by_cases hjn : j = n <;> by_cases hln : l = n <;> by_cases hmn : m = n <;>
          simp [hjl, hjm, hlm, hjn, hln, hmn]
      simp_rw [hn, ← Finset.mul_sum, sum_omit_three f3 hjl hjm hlm, h3]
      simp only [hjl, hjm, hlm, or_self, ite_false]
      ring
  simp_rw [step1]
  have split3 :
      (∑ j : ι, ∑ l : ι, ∑ m : ι,
        if j = l ∨ j = m ∨ l = m then (0 : ℂ)
        else -(f0 j * f3 j * f1 l * f2 m) - (f1 l * f3 l * f0 j * f2 m) -
          (f2 m * f3 m * f0 j * f1 l)) =
      -(∑ j : ι, ∑ l : ι, ∑ m : ι,
          if j = l ∨ j = m ∨ l = m then (0 : ℂ) else (f0 j * f3 j) * f1 l * f2 m) -
      (∑ l : ι, ∑ j : ι, ∑ m : ι,
          if l = j ∨ l = m ∨ j = m then (0 : ℂ) else (f1 l * f3 l) * f0 j * f2 m) -
      (∑ m : ι, ∑ j : ι, ∑ l : ι,
          if m = j ∨ m = l ∨ j = l then (0 : ℂ) else (f2 m * f3 m) * f0 j * f1 l) := by
    have t2 :
        (∑ l : ι, ∑ j : ι, ∑ m : ι,
          if l = j ∨ l = m ∨ j = m then (0 : ℂ) else (f1 l * f3 l) * f0 j * f2 m) =
        ∑ j : ι, ∑ l : ι, ∑ m : ι,
          if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f1 l * f3 l * f0 j * f2 m := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun m _ => ?_
      have heq : (l = j ∨ l = m ∨ j = m) ↔ (j = l ∨ j = m ∨ l = m) := by tauto
      simp only [heq]
    have t3 :
        (∑ m : ι, ∑ j : ι, ∑ l : ι,
          if m = j ∨ m = l ∨ j = l then (0 : ℂ) else (f2 m * f3 m) * f0 j * f1 l) =
        ∑ j : ι, ∑ l : ι, ∑ m : ι,
          if j = l ∨ j = m ∨ l = m then (0 : ℂ) else f2 m * f3 m * f0 j * f1 l := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun m l => if m = _ ∨ m = l ∨ _ = l then (0 : ℂ) else _)]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun m _ => ?_
      have heq : (m = j ∨ m = l ∨ j = l) ↔ (j = l ∨ j = m ∨ l = m) := by tauto
      simp only [heq]
    rw [t2, t3]
    simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  rw [split3,
    sum_distinct3_gen (fun j => f0 j * f3 j) f1 f2 h1 h2,
    sum_distinct3_gen (fun l => f1 l * f3 l) f0 f2 h0 h2,
    sum_distinct3_gen (fun m => f2 m * f3 m) f0 f1 h0 h1]
  have q1 : (∑ j : ι, f0 j * f3 j * f1 j * f2 j) = ∑ j : ι, f0 j * f1 j * f2 j * f3 j :=
    Finset.sum_congr rfl fun j _ => by ring
  have q2 : (∑ j : ι, f1 j * f3 j * f0 j * f2 j) = ∑ j : ι, f0 j * f1 j * f2 j * f3 j :=
    Finset.sum_congr rfl fun j _ => by ring
  have q3 : (∑ j : ι, f2 j * f3 j * f0 j * f1 j) = ∑ j : ι, f0 j * f1 j * f2 j * f3 j :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [q1, q2, q3]
  ring

noncomputable def witnessFun (p : Fin 5 → ℂ) (k : Fin 4 × Fin 4) : ℂ :=
  match k.1.val, k.2.val with
  | 0, 0 => p 0
  | 0, 1 => -p 0
  | 0, 2 => p 1
  | 0, 3 => -p 1
  | 1, 0 => ω * p 0
  | 1, 1 => -(ω * p 0)
  | 1, 2 => ω ^ 2 * p 1
  | 1, 3 => -(ω ^ 2 * p 1)
  | 2, 0 => ω ^ 2 * p 0
  | 2, 1 => -(ω ^ 2 * p 0)
  | 2, 2 => ω * p 1
  | 2, 3 => -(ω * p 1)
  | 3, 0 => p 2
  | 3, 1 => p 3
  | 3, 2 => p 4
  | 3, 3 => -(p 2 + p 3 + p 4)
  | _, _ => 0

noncomputable def witnessMap : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun := witnessFun
  map_add' p q := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [witnessFun] <;> ring
  map_smul' c p := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [witnessFun] <;> ring

private lemma witnessMap_injective : Function.Injective witnessMap := by
  intro p q h
  funext k
  fin_cases k
  · simpa [witnessMap, witnessFun] using congr_fun h (0, 0)
  · simpa [witnessMap, witnessFun] using congr_fun h (0, 2)
  · simpa [witnessMap, witnessFun] using congr_fun h (3, 0)
  · simpa [witnessMap, witnessFun] using congr_fun h (3, 1)
  · simpa [witnessMap, witnessFun] using congr_fun h (3, 2)

private lemma witness_row_sum (p : Fin 5 → ℂ) (i : Fin 4) :
    ∑ j : Fin 4, witnessFun p (i, j) = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_four, witnessFun]

private lemma witness_p2 (p : Fin 5 → ℂ) :
    (∑ j : Fin 4, ∑ l : Fin 4,
      if j = l then (0 : ℂ) else
        ∑ a : Fin 4, ∑ b : Fin 4, if a < b then witnessFun p (a, j) * witnessFun p (b, l) else 0) =
      0 := by
  have swap_ab :
      (∑ j : Fin 4, ∑ l : Fin 4,
        if j = l then (0 : ℂ) else
          ∑ a : Fin 4, ∑ b : Fin 4, if a < b then witnessFun p (a, j) * witnessFun p (b, l) else 0) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        if a < b then
          ∑ j : Fin 4, ∑ l : Fin 4, if j = l then (0 : ℂ) else witnessFun p (a, j) * witnessFun p (b, l)
        else 0 := by
    have h1 : ∀ j l : Fin 4,
        (if j = l then (0 : ℂ) else
          ∑ a : Fin 4, ∑ b : Fin 4, if a < b then witnessFun p (a, j) * witnessFun p (b, l) else 0) =
        ∑ a : Fin 4, ∑ b : Fin 4,
          if a < b then (if j = l then (0 : ℂ) else witnessFun p (a, j) * witnessFun p (b, l)) else 0 := by
      intro j l
      split_ifs with hjl
      · simp
      · rfl
    simp_rw [h1]
    have comm2 : ∀ (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ),
        (∑ j, ∑ l, ∑ a, ∑ b, F j l a b) = ∑ a, ∑ b, ∑ j, ∑ l, F j l a b := by
      intro F
      calc (∑ j, ∑ l, ∑ a, ∑ b, F j l a b)
          = ∑ j, ∑ a, ∑ l, ∑ b, F j l a b := by
              refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ a, ∑ j, ∑ l, ∑ b, F j l a b := Finset.sum_comm
        _ = ∑ a, ∑ j, ∑ b, ∑ l, F j l a b := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ j, ∑ l, F j l a b := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [comm2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a < b <;> simp [hab]
  rw [swap_ab]
  have hinner : ∀ a b : Fin 4,
      (∑ j : Fin 4, ∑ l : Fin 4, if j = l then (0 : ℂ) else witnessFun p (a, j) * witnessFun p (b, l)) =
        -(∑ j : Fin 4, witnessFun p (a, j) * witnessFun p (b, j)) := by
    intro a b
    rw [sum_distinct2_gen (fun j => witnessFun p (a, j)) (fun l => witnessFun p (b, l)),
      witness_row_sum p a, witness_row_sum p b]
    ring
  simp_rw [hinner]
  simp only [Fin.sum_univ_four, witnessFun]
  norm_num
  ring_nf
  simp only [ω_cube, ω_sq]
  ring

private lemma witness_p3 (p : Fin 5 → ℂ) :
    (∑ j : Fin 4, ∑ l : Fin 4, ∑ m : Fin 4,
      if j = l ∨ j = m ∨ l = m then (0 : ℂ) else
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          if a < b ∧ b < c then witnessFun p (a, j) * witnessFun p (b, l) * witnessFun p (c, m) else 0) =
      0 := by
  have swap_abc :
      (∑ j : Fin 4, ∑ l : Fin 4, ∑ m : Fin 4,
        if j = l ∨ j = m ∨ l = m then (0 : ℂ) else
          ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
            if a < b ∧ b < c then witnessFun p (a, j) * witnessFun p (b, l) * witnessFun p (c, m) else 0) =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        if a < b ∧ b < c then
          ∑ j : Fin 4, ∑ l : Fin 4, ∑ m : Fin 4,
            if j = l ∨ j = m ∨ l = m then (0 : ℂ)
            else witnessFun p (a, j) * witnessFun p (b, l) * witnessFun p (c, m)
        else 0 := by
    have h1 : ∀ j l m : Fin 4,
        (if j = l ∨ j = m ∨ l = m then (0 : ℂ) else
          ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
            if a < b ∧ b < c then witnessFun p (a, j) * witnessFun p (b, l) * witnessFun p (c, m) else 0) =
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          if a < b ∧ b < c then
            (if j = l ∨ j = m ∨ l = m then (0 : ℂ)
              else witnessFun p (a, j) * witnessFun p (b, l) * witnessFun p (c, m))
          else 0 := by
      intro j l m
      split_ifs with h
      · simp
      · rfl
    simp_rw [h1]
    have comm3 : ∀ (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ),
        (∑ j, ∑ l, ∑ m, ∑ a, ∑ b, ∑ c, F j l m a b c) =
        ∑ a, ∑ b, ∑ c, ∑ j, ∑ l, ∑ m, F j l m a b c := by
      intro F
      calc (∑ j, ∑ l, ∑ m, ∑ a, ∑ b, ∑ c, F j l m a b c)
          = ∑ j, ∑ l, ∑ a, ∑ m, ∑ b, ∑ c, F j l m a b c := by
              refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
        _ = ∑ j, ∑ a, ∑ l, ∑ m, ∑ b, ∑ c, F j l m a b c := by
              refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ a, ∑ j, ∑ l, ∑ m, ∑ b, ∑ c, F j l m a b c := Finset.sum_comm
        _ = ∑ a, ∑ j, ∑ l, ∑ b, ∑ m, ∑ c, F j l m a b c := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
                Finset.sum_congr rfl fun l _ => Finset.sum_comm
        _ = ∑ a, ∑ j, ∑ b, ∑ l, ∑ m, ∑ c, F j l m a b c := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ j, ∑ l, ∑ m, ∑ c, F j l m a b c := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ j, ∑ l, ∑ c, ∑ m, F j l m a b c := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
                Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ j, ∑ c, ∑ l, ∑ m, F j l m a b c := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
                Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ c, ∑ j, ∑ l, ∑ m, F j l m a b c := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    rw [comm3]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    by_cases habc : a < b ∧ b < c <;> simp [habc]
  rw [swap_abc]
  have hinner : ∀ a b c : Fin 4,
      (∑ j : Fin 4, ∑ l : Fin 4, ∑ m : Fin 4,
        if j = l ∨ j = m ∨ l = m then (0 : ℂ)
        else witnessFun p (a, j) * witnessFun p (b, l) * witnessFun p (c, m)) =
      2 * (∑ j : Fin 4, witnessFun p (a, j) * witnessFun p (b, j) * witnessFun p (c, j)) := by
    intro a b c
    rw [sum_distinct3_gen (fun j => witnessFun p (a, j)) (fun l => witnessFun p (b, l))
        (fun m => witnessFun p (c, m)) (witness_row_sum p b) (witness_row_sum p c),
      witness_row_sum p a]
    ring
  simp_rw [hinner]
  simp only [Fin.sum_univ_four, witnessFun]
  norm_num
  ring_nf
  simp only [ω_cube, ω_sq]
  ring

private lemma witness_p4 (p : Fin 5 → ℂ) :
    (∑ j : Fin 4, ∑ l : Fin 4, ∑ m : Fin 4, ∑ n : Fin 4,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℂ)
      else witnessFun p (0, j) * witnessFun p (1, l) * witnessFun p (2, m) * witnessFun p (3, n)) =
      0 := by
  rw [sum_distinct4
    (fun j => witnessFun p (0, j)) (fun l => witnessFun p (1, l))
    (fun m => witnessFun p (2, m)) (fun n => witnessFun p (3, n))
    (witness_row_sum p 0) (witness_row_sum p 1)
    (witness_row_sum p 2) (witness_row_sum p 3)]
  set x := p 0
  set y := p 1
  set dx := p 2 - p 3
  set dy := p 4 - (-(p 2 + p 3 + p 4))
  have h03 : (∑ j : Fin 4, witnessFun p (0, j) * witnessFun p (3, j)) = x * dx + y * dy := by
    rw [Fin.sum_univ_four]
    change p 0 * p 2 + -p 0 * p 3 + p 1 * p 4 + -p 1 * (-(p 2 + p 3 + p 4)) = x * dx + y * dy
    dsimp only [x, y, dx, dy]; ring
  have h13 : (∑ j : Fin 4, witnessFun p (1, j) * witnessFun p (3, j)) =
      ω * x * dx + ω ^ 2 * y * dy := by
    rw [Fin.sum_univ_four]
    change (ω * p 0) * p 2 + -(ω * p 0) * p 3 + (ω ^ 2 * p 1) * p 4 + -(ω ^ 2 * p 1) * (-(p 2 + p 3 + p 4)) = ω * x * dx + ω ^ 2 * y * dy
    dsimp only [x, y, dx, dy]; ring
  have h23 : (∑ j : Fin 4, witnessFun p (2, j) * witnessFun p (3, j)) =
      ω ^ 2 * x * dx + ω * y * dy := by
    rw [Fin.sum_univ_four]
    change (ω ^ 2 * p 0) * p 2 + -(ω ^ 2 * p 0) * p 3 + (ω * p 1) * p 4 + -(ω * p 1) * (-(p 2 + p 3 + p 4)) = ω ^ 2 * x * dx + ω * y * dy
    dsimp only [x, y, dx, dy]; ring
  have h01 : (∑ j : Fin 4, witnessFun p (0, j) * witnessFun p (1, j)) =
      2 * ω * x ^ 2 + 2 * ω ^ 2 * y ^ 2 := by
    rw [Fin.sum_univ_four]
    change p 0 * (ω * p 0) + -p 0 * -(ω * p 0) + p 1 * (ω ^ 2 * p 1) + -p 1 * -(ω ^ 2 * p 1) = 2 * ω * x ^ 2 + 2 * ω ^ 2 * y ^ 2
    dsimp only [x, y]; ring
  have h02 : (∑ j : Fin 4, witnessFun p (0, j) * witnessFun p (2, j)) =
      2 * ω ^ 2 * x ^ 2 + 2 * ω * y ^ 2 := by
    rw [Fin.sum_univ_four]
    change p 0 * (ω ^ 2 * p 0) + -p 0 * -(ω ^ 2 * p 0) + p 1 * (ω * p 1) + -p 1 * -(ω * p 1) = 2 * ω ^ 2 * x ^ 2 + 2 * ω * y ^ 2
    dsimp only [x, y]; ring
  have h12 : (∑ j : Fin 4, witnessFun p (1, j) * witnessFun p (2, j)) =
      2 * x ^ 2 + 2 * y ^ 2 := by
    rw [Fin.sum_univ_four]
    change (ω * p 0) * (ω ^ 2 * p 0) + -(ω * p 0) * -(ω ^ 2 * p 0) +
      (ω ^ 2 * p 1) * (ω * p 1) + -(ω ^ 2 * p 1) * -(ω * p 1) = 2 * x ^ 2 + 2 * y ^ 2
    dsimp only [x, y]
    linear_combination (2 * p 0 ^ 2 + 2 * p 1 ^ 2) * ω_cube
  have hQ : (∑ j : Fin 4, witnessFun p (0, j) * witnessFun p (1, j) *
      witnessFun p (2, j) * witnessFun p (3, j)) = x ^ 3 * dx + y ^ 3 * dy := by
    rw [Fin.sum_univ_four]
    change p 0 * (ω * p 0) * (ω ^ 2 * p 0) * p 2 +
      -p 0 * -(ω * p 0) * -(ω ^ 2 * p 0) * p 3 +
      p 1 * (ω ^ 2 * p 1) * (ω * p 1) * p 4 +
      -p 1 * -(ω ^ 2 * p 1) * -(ω * p 1) * (-(p 2 + p 3 + p 4)) = x ^ 3 * dx + y ^ 3 * dy
    dsimp only [x, y, dx, dy]
    linear_combination (p 0 ^ 3 * (p 2 - p 3) + p 1 ^ 3 * (p 4 - (-(p 2 + p 3 + p 4)))) * ω_cube
  rw [h03, h12, h13, h02, h23, h01, hQ]
  linear_combination
    (4 * x ^ 3 * dx + 4 * y ^ 3 * dy + 2 * ω * x ^ 2 * y * dy + 2 * ω * y ^ 2 * x * dx) * ω_cube +
    (2 * x ^ 2 * y * dy + 2 * y ^ 2 * x * dx) * ω_sq_add

end PEqualNP.Outside.L_gct_197_aux

open PEqualNP.Outside.L_gct_197_aux in
theorem PEqualNP.Outside.L_gct_197 : ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) ∧ Module.finrank ℂ L = 5 := by
  refine ⟨LinearMap.range witnessMap, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact ⟨witness_row_sum p, witness_p2 p, witness_p3 p, witness_p4 p⟩
  · rw [LinearMap.finrank_range_of_inj witnessMap_injective, Module.finrank_fin_fun]
