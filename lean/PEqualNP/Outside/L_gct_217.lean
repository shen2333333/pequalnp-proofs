import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct217

-- The alternating sum of matching coefficients is the permanent of 1 - t.
-- A column of ones makes this permanent zero, contradicting its constant value 24.
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 12000 in
private theorem no_one_column (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) :
    ∀ j : Fin 4, ¬ ∃ t ∈ L, ∀ i : Fin 4, t (i,j) = 1 := by
  rintro j ⟨t,ht,hj⟩
  obtain ⟨hr,h₂,h₃,h₄⟩ := hL t ht
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have r3 := hr 3
  have pair (l m : Fin 4) :
      (∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a,l) * t (b,m) else 0) =
        t (0,l) * t (1,m) + t (0,l) * t (2,m) + t (0,l) * t (3,m) + t (1,l) * t (2,m) + t (1,l) * t (3,m) + t (2,l) * t (3,m) := by
    norm_num [Fin.sum_univ_four]
    ring
  simp_rw [pair] at h₂
  have triple (l m n : Fin 4) :
      (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a,l) * t (b,m) * t (c,n) else 0) =
        t (0,l) * t (1,m) * t (2,n) + t (0,l) * t (1,m) * t (3,n) + t (0,l) * t (2,m) * t (3,n) + t (1,l) * t (2,m) * t (3,n) := by
    norm_num [Fin.sum_univ_four]
  simp_rw [triple] at h₃
  norm_num [Fin.sum_univ_four] at r0 r1 r2 r3 h₂ h₃ h₄
  have impossible : (24 : ℂ) = 0 := by
    fin_cases j
    all_goals first
      | change ∀ i : Fin 4, t (i,0) = 1 at hj
      | change ∀ i : Fin 4, t (i,1) = 1 at hj
      | change ∀ i : Fin 4, t (i,2) = 1 at hj
      | change ∀ i : Fin 4, t (i,3) = 1 at hj
    all_goals
      simp only [hj] at r0 r1 r2 r3 h₂ h₃ h₄
      linear_combination 6 * r0 + 6 * r1 + 6 * r2 + 6 * r3 - 2 * h₂ + h₃ - h₄
  norm_num at impossible

private def rowAtom (j : Fin 4) (z : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ :=
  z p.1 * (if p.2 = j then 3 else -1)

private theorem rowAtom_sparse (j : Fin 4) (z : Fin 4 → ℂ) (hz : z ≠ 0)
    (h₂ : (∑ j', ∑ l, if j' = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then rowAtom j z (a,j') * rowAtom j z (b,l) else 0) = 0)
    (h₃ : (∑ j', ∑ l, ∑ m, if j' = l ∨ j' = m ∨ l = m then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then
        rowAtom j z (a,j') * rowAtom j z (b,l) * rowAtom j z (c,m) else 0) = 0)
    (h₄ : (∑ j', ∑ l, ∑ m, ∑ n, if j' = l ∨ j' = m ∨ j' = n ∨ l = m ∨ l = n ∨ m = n
      then 0 else rowAtom j z (0,j') * rowAtom j z (1,l) *
        rowAtom j z (2,m) * rowAtom j z (3,n)) = 0) :
    ∃ i : Fin 4, z i ≠ 0 ∧ ∀ r : Fin 4, r ≠ i → z r = 0 := by
  have e₂ : z 0*z 1 + z 0*z 2 + z 0*z 3 + z 1*z 2 + z 1*z 3 + z 2*z 3 = 0 := by
    fin_cases j <;> norm_num [Fin.sum_univ_four, rowAtom] at h₂ <;>
      linear_combination -h₂ / 12
  have e₃ : z 0*z 1*z 2 + z 0*z 1*z 3 + z 0*z 2*z 3 + z 1*z 2*z 3 = 0 := by
    fin_cases j <;> norm_num [Fin.sum_univ_four, rowAtom] at h₃ <;>
      linear_combination h₃ / 48
  have e₄ : z 0*z 1*z 2*z 3 = 0 := by
    fin_cases j <;> norm_num [Fin.sum_univ_four, rowAtom] at h₄ <;>
      linear_combination -h₄ / 72
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! hall
    exact hz (funext hall)
  refine ⟨i,hi,?_⟩
  intro r hr
  by_contra hn
  clear h₂ h₃ h₄
  by_cases h0 : z 0 = 0 <;> by_cases h1 : z 1 = 0 <;>
    by_cases h2 : z 2 = 0 <;> by_cases h3 : z 3 = 0 <;>
    simp_all only [mul_zero, zero_mul, add_zero, zero_add, mul_eq_zero, or_false] <;>
    fin_cases i <;> fin_cases r <;> simp_all


private def contrast (j l : Fin 4) : ℂ := if l = j then 3 else -1

private def singleRow (r : Fin 4) (u : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ :=
  if p.1 = r then u p.2 else 0

private theorem dot_contrast (v : Fin 4 → ℂ) (j : Fin 4) :
    (∑ l, v l * contrast j l) = 4 * v j - ∑ l, v l := by
  have eqn (l : Fin 4) : v l * contrast j l = (if l = j then 4 * v l else 0) - v l := by
    unfold contrast
    split_ifs <;> ring
  simp_rw [eqn]
  rw [Finset.sum_sub_distrib]
  simp

private theorem bil_single (t : Fin 4 × Fin 4 → ℂ) (r : Fin 4) (u : Fin 4 → ℂ) :
    (∑ a : Fin 4, ∑ l : Fin 4, ((∑ b : Fin 4, t (b,l)) - t (a,l)) * singleRow r u (a,l)) =
    ∑ l : Fin 4, ((∑ b : Fin 4, t (b,l)) - t (r,l)) * u l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [singleRow, mul_ite]

private theorem align_rows (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hrow : ∀ t ∈ L, ∀ i : Fin 4, ∑ j, t (i,j) = 0)
    (hiso : ∀ t ∈ L, ∀ u ∈ L,
      (∑ a : Fin 4, ∑ l : Fin 4, ((∑ b : Fin 4, t (b,l)) - t (a,l)) * u (a,l)) = 0)
    (hat : ∀ j : Fin 4, ∃ z : Fin 4 → ℂ, rowAtom j z ∈ L ∧
      ∃ r : Fin 4, z r ≠ 0 ∧ ∀ i : Fin 4, i ≠ r → z i = 0) :
    ∃ r : Fin 4, (∀ u : Fin 4 → ℂ, (∑ j, u j) = 0 →
      (fun p : Fin 4 × Fin 4 => if p.1 = r then u p.2 else 0) ∈ L) ∧
      (∀ t ∈ L, ∀ j : Fin 4, (∑ i, t (i,j)) = t (r,j)) := by
  classical
  have normalized (j : Fin 4) : ∃ r, singleRow r (contrast j) ∈ L := by
    obtain ⟨z,hL,r,hr,hr'⟩ := hat j
    refine ⟨r, ?_⟩
    have he : (z r)⁻¹ • rowAtom j z = singleRow r (contrast j) := by
      funext ⟨i,l⟩
      by_cases hir : i = r
      · subst i
        simp [rowAtom, singleRow, contrast, hr]
      · simp [rowAtom, singleRow, hir, hr' i hir]
    exact he ▸ L.smul_mem _ hL
  choose roots hroots using normalized
  let r := roots 0
  have hall (j : Fin 4) : roots j = r := by
    by_contra hne
    have h := hiso _ (hroots j) _ (hroots 0)
    rw [bil_single] at h
    change (∑ l, ((∑ b, singleRow (roots j) (contrast j) (b,l)) -
      singleRow (roots j) (contrast j) (r,l)) * contrast 0 l) = 0 at h
    simp only [singleRow, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ite_eq_right (Ne.symm hne), sub_zero] at h
    have csum : (∑ l, contrast j l) = 0 := by
      fin_cases j <;> norm_num [contrast, Fin.sum_univ_four]
    rw [dot_contrast, csum, sub_zero] at h
    fin_cases j <;> norm_num [contrast] at h
  have hrall (j : Fin 4) : singleRow r (contrast j) ∈ L := hall j ▸ hroots j
  refine ⟨r, ?_, ?_⟩
  · intro u hu
    have hm : (∑ j : Fin 4, (u j / 4) • singleRow r (contrast j)) ∈ L :=
      L.sum_mem (fun j _ => L.smul_mem _ (hrall j))
    have he : (∑ j : Fin 4, (u j / 4) • singleRow r (contrast j)) = singleRow r u := by
      funext ⟨i,l⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, singleRow]
      by_cases hir : i = r
      · simp only [hir, ite_true]
        have symm' (j : Fin 4) : contrast j l = contrast l j := by
          simp only [contrast, eq_comm]
        calc
          _ = (∑ j : Fin 4, u j * contrast l j) / 4 := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [symm']
            ring
          _ = u l := by rw [dot_contrast, hu]; ring
      · simp [hir]
    change singleRow r u ∈ L
    rwa [← he]
  · intro t ht j
    have h := hiso t ht _ (hrall j)
    rw [bil_single, dot_contrast] at h
    have hs : (∑ l : Fin 4, ((∑ b : Fin 4, t (b,l)) - t (r,l))) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_comm, hrow _ ht r]
      simp [hrow _ ht]
    rw [hs, sub_zero] at h
    linear_combination h / 4

private abbrev Ambient217 := Fin 4 × Fin 4 → ℂ

private def b217 (t u : Ambient217) : ℂ :=
  ∑ i : Fin 4, ∑ l : Fin 4, ((∑ a : Fin 4, t (a,l)) - t (i,l)) * u (i,l)

private def q217 (t : Ambient217) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
    if a < b then t (a,j) * t (b,l) else 0

private theorem zero_b217 (t : Ambient217) (hc : ∀ i, ∑ j, t (i,j) = 0)
    (h : q217 t = 0) : b217 t t = 0 := by
  have lastcol (i : Fin 4) : t (i,3) = -(t (i,0)+t (i,1)+t (i,2)) := by
    have e := hc i
    rw [Fin.sum_univ_four] at e
    linear_combination e
  norm_num [q217, b217, Fin.sum_univ_four,lastcol] at h ⊢
  linear_combination -2*h

private theorem add_b217 (t u : Ambient217) :
    b217 (t+u) (t+u) = b217 t t + b217 u u + 2*b217 t u := by
  simp only [b217,Fin.sum_univ_four,Pi.add_apply]
  ring

private theorem isotropic217 (L : Submodule ℂ Ambient217)
    (hcent : ∀ t∈L, ∀ i, ∑ j, t (i,j) = 0) (hq : ∀ t∈L, q217 t=0) :
    ∀ t∈L, ∀ u∈L, (∑ i : Fin 4, ∑ l : Fin 4,
      ((∑ a : Fin 4, t (a,l)) - t (i,l)) * u (i,l)) = 0 := by
  intro t ht u hu
  have flat (x : Ambient217) (hx : x ∈ L) := zero_b217 x (hcent x hx) (hq x hx)
  have h := flat (t+u) (L.add_mem ht hu)
  rw [add_b217,flat t ht,flat u hu] at h
  change b217 t u = 0
  linear_combination h / 2

private def gram217 : Ambient217 →ₗ[ℂ] Ambient217 where
  toFun t := fun p => (∑ a : Fin 4, t (a,p.2)) - t p
  map_add' t u := by ext p; simp only [Pi.add_apply,Finset.sum_add_distrib]; ring
  map_smul' c t := by ext p; simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,RingHom.id_apply]; ring

private theorem gramInj217 : Function.Injective gram217 := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro t h
  have eqn (i j : Fin 4) : (∑ a : Fin 4, t (a,j)) - t (i,j) = 0 := congrFun h (i,j)
  funext ⟨i,j⟩
  change t (i,j) = 0
  have e0 := eqn 0 j
  have e1 := eqn 1 j
  have e2 := eqn 2 j
  have e3 := eqn 3 j
  have ei := eqn i j
  simp only [Fin.sum_univ_four] at e0 e1 e2 e3 ei
  linear_combination (e0+e1+e2+e3)/3-ei

private noncomputable def dual217 : Ambient217 →ₗ[ℂ] Module.Dual ℂ Ambient217 :=
  (dotProductEquiv ℂ (Fin 4 × Fin 4)).toLinearMap.comp gram217

private theorem dualApply217 (t u : Ambient217) : dual217 t u = b217 t u := by
  change (∑ p : Fin 4 × Fin 4, ((∑ a : Fin 4, t (a,p.2)) - t p) * u p) = _
  rw [Fintype.sum_prod_type]
  rfl

private theorem dualInj217 : Function.Injective dual217 :=
  (dotProductEquiv ℂ (Fin 4 × Fin 4)).injective.comp gramInj217

private def rows217 : (Fin 4 → ℂ) →ₗ[ℂ] Ambient217 where
  toFun w := fun p => w p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rowsDim217 : Module.finrank ℂ (LinearMap.range rows217) = 4 := by
  have hi : Function.Injective rows217 := fun u v h => funext fun i => congrFun h (i,0)
  rw [LinearMap.finrank_range_of_inj hi,Module.finrank_fin_fun]

private theorem rowsZero217 (r : Ambient217) (hr : r ∈ LinearMap.range rows217)
    (hc : ∀ i, ∑ j, r (i,j) = 0) : r=0 := by
  obtain ⟨w,rfl⟩ := hr
  funext ⟨i,j⟩
  have e := hc i
  change w i = 0
  change (∑ _ : Fin 4, w i) = 0 at e
  simp only [Fin.sum_univ_four] at e
  linear_combination e/4

private theorem maximal217 (L : Submodule ℂ Ambient217)
    (hcent : ∀ t∈L, ∀ i, ∑ j, t (i,j) = 0)
    (hi : ∀ t∈L, ∀ u∈L, b217 t u = 0) (hd : 6 ≤ Module.finrank ℂ L)
    (x : Ambient217) (hx : ∀ i, ∑ j, x (i,j)=0) (horth : ∀ t∈L, b217 x t=0) : x∈L := by
  let O := L.dualAnnihilator.comap dual217
  let R := LinearMap.range rows217
  have hLO : L ≤ O := fun t ht => (Submodule.mem_dualAnnihilator _).mpr fun u hu =>
    (dualApply217 t u).trans (hi t ht u hu)
  have hRO : R ≤ O := by
    rintro _ ⟨v,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro u hu
    rw [dualApply217]
    change (∑ i : Fin 4, ∑ l : Fin 4, ((∑ a : Fin 4, v a)-v i)*u (i,l))=0
    simp only [←Finset.mul_sum,hcent u hu,mul_zero,Finset.sum_const_zero]
  have hinf : L ⊓ R = ⊥ := by
    apply le_antisymm _ bot_le
    intro r hr
    change r = 0
    exact rowsZero217 r hr.2 (hcent r hr.1)
  have hr : ∀ t : O, (dual217.domRestrict O) t ∈ L.dualAnnihilator := fun t => t.property
  have ii : Function.Injective ((dual217.domRestrict O).codRestrict L.dualAnnihilator hr) :=
    fun a b hab => Subtype.ext (dualInj217 (congrArg Subtype.val hab))
  have hO := LinearMap.finrank_le_finrank_of_injective ii
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq L R
  have hR : Module.finrank ℂ R=4 := rowsDim217
  rw [hinf,finrank_bot,add_zero,hR] at hsup
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have h16 : Module.finrank ℂ Ambient217 = 16 := by
    rw [Module.finrank_fintype_fun_eq_card]; rfl
  rw [h16] at hann
  have heq : L ⊔ R = O := Submodule.eq_of_le_of_finrank_le (sup_le hLO hRO) (by omega)
  have xo : x ∈ O := (Submodule.mem_dualAnnihilator _).mpr fun t ht =>
    (dualApply217 x t).trans (horth t ht)
  rw [←heq] at xo
  obtain ⟨l,hl,r,hr',ex⟩ := Submodule.mem_sup.mp xo
  have rz : r=0 := rowsZero217 r hr' fun i => by
    have e := hx i
    rw [←ex] at e
    simpa only [Pi.add_apply, Finset.sum_add_distrib,hcent l hl i,zero_add] using e
  simpa [←ex,rz] using hl

private def col217 (j : Fin 4) : Ambient217 →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun t := fun i => t (i,j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem extract217 (L : Submodule ℂ Ambient217)
    (hcent : ∀ t∈L, ∀ i, ∑ j, t (i,j) = 0) (hq : ∀ t∈L, q217 t=0)
    (hd : 6 ≤ Module.finrank ℂ L) (hno : ∀ j : Fin 4, ¬∃ t∈L, ∀ i, t (i,j)=(1:ℂ)) :
    ∀ j, ∃ z : Fin 4 → ℂ, z ≠ 0 ∧ rowAtom j z ∈ L := by
  classical
  intro j
  let P := L.map (col217 j)
  have hnot : (1 : Fin 4 → ℂ) ∉ P := by
    rintro ⟨t,ht,e⟩
    exact hno j ⟨t,ht,fun i => congrFun e i⟩
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff P] at hnot
  push Not at hnot
  obtain ⟨φ,hφ,h1⟩ := hnot
  let w := (dotProductEquiv ℂ (Fin 4)).symm φ
  have repr (a : Fin 4 → ℂ) : φ a = ∑ i, w i*a i := by
    change φ a = (dotProductEquiv ℂ (Fin 4)) w a
    rw [show (dotProductEquiv ℂ (Fin 4)) w = φ from LinearEquiv.apply_symm_apply _ _]
  let z := fun i : Fin 4 => (∑ k, w k)/3-w i
  have inv (i : Fin 4) : (∑ a : Fin 4, z a) - z i = w i := by
    simp only [z,Fin.sum_univ_four]
    ring
  have zn : z ≠ 0 := by
    intro he
    have we (i : Fin 4) : w i = 0 := by rw [←inv i,he]; simp
    apply h1
    simp [repr,we]
  refine ⟨z,zn,maximal217 L hcent (isotropic217 L hcent hq) hd _ ?_ ?_⟩
  · intro i
    fin_cases j <;> norm_num [Fin.sum_univ_four,rowAtom] <;> ring
  · intro t ht
    have wp := (Submodule.mem_dualAnnihilator _).mp hφ (col217 j t) (Submodule.mem_map_of_mem ht)
    rw [repr] at wp
    have entry (a l : Fin 4) :
        (∑ b : Fin 4, rowAtom j z (b,l)) - rowAtom j z (a,l) =
          w a * (if l=j then 3 else -1) := by
      calc
        _ = ((∑ b : Fin 4, z b) - z a) * (if l=j then 3 else -1) := by
          simp only [rowAtom,Fin.sum_univ_four]
          ring
        _ = _ := by rw [inv]
    have inner (a : Fin 4) :
        (∑ l : Fin 4, w a * (if l=j then 3 else -1) * t (a,l)) = 4*(w a*t (a,j)) := by
      have ec := hcent t ht a
      rw [Fin.sum_univ_four] at ec
      fin_cases j <;> norm_num [Fin.sum_univ_four] <;> linear_combination -(w a)*ec
    change (∑ i : Fin 4, ∑ l : Fin 4, ((∑ a : Fin 4, rowAtom j z (a,l)) - rowAtom j z (i,l)) * t (i,l))=0
    simp only [entry,inner,← Finset.mul_sum]
    change (∑ i, w i*t (i,j))=0 at wp
    rw [wp, mul_zero]

-- At dimension six the quadratic form makes the space its own orthogonal complement.
-- A normal to each column projection therefore yields a matrix in the space. The
-- higher matching equations force these matrices to select the same single row.
private theorem structural217 (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0)
    (hd : 6 ≤ Module.finrank ℂ L) :
    ∃ r : Fin 4, (∀ u : Fin 4 → ℂ, (∑ j, u j) = 0 →
      (fun p : Fin 4 × Fin 4 => if p.1=r then u p.2 else 0) ∈ L) ∧
      (∀ t∈L, ∀ j : Fin 4, (∑ i, t (i,j)) = t (r,j)) := by
  have hc : ∀ t∈L, ∀ i : Fin 4, ∑ j, t (i,j)=0 := fun t ht => (hL t ht).1
  have hq : ∀ t∈L, q217 t=0 := fun t ht => (hL t ht).2.1
  refine align_rows L hc (isotropic217 L hc hq) ?_
  intro j
  obtain ⟨z,hz,ha⟩ := extract217 L hc hq hd (no_one_column L hL) j
  obtain ⟨_,h₂,h₃,h₄⟩ := hL _ ha
  exact ⟨z,ha,rowAtom_sparse j z hz h₂ h₃ h₄⟩

end PEqualNP.Outside.Gct217

namespace PEqualNP.Outside.Gct217Residual

private abbrev Mat := Fin 4 × Fin 4 → ℂ

private def quad (t : Mat) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a,j)*t (b,l) else 0

private def cube (t : Mat) : ℂ :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a,j)*t (b,l)*t (c,m) else 0

private def e2 (x y z w : ℂ) := x*y+x*z+x*w+y*z+y*w+z*w
private def e3 (x y z w : ℂ) := x*y*z+x*y*w+x*z*w+y*z*w
private def others (x y z : ℂ) := x*y+x*z+y*z

private theorem last_of_center (t : Mat) (ht : ∀ i : Fin 4, ∑ j, t (i,j) = 0) (i : Fin 4) :
    t (i,3) = -(t (i,0)+t (i,1)+t (i,2)) := by
  have h := ht i
  rw [Fin.sum_univ_four] at h
  linear_combination h

set_option maxHeartbeats 3000000 in
private theorem quad_center (t : Mat) (ht : ∀ i : Fin 4, ∑ j, t (i,j) = 0) :
    quad t = -(∑ j : Fin 4, e2 (t (0,j)) (t (1,j)) (t (2,j)) (t (3,j))) := by
  have rows (j l : Fin 4) : (∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a,j)*t (b,l) else 0) =
      t (0,j)*t (1,l)+t (0,j)*t (2,l)+t (0,j)*t (3,l)+t (1,j)*t (2,l)+t (1,j)*t (3,l)+t (2,j)*t (3,l) := by
    norm_num [Fin.sum_univ_four]
    ring
  unfold quad
  simp_rw [rows]
  norm_num [Fin.sum_univ_four,e2,last_of_center t ht]
  ring

set_option maxHeartbeats 4000000 in
private theorem cube_center (t : Mat) (ht : ∀ i : Fin 4, ∑ j, t (i,j) = 0) :
    cube t = 2 * ∑ j : Fin 4, e3 (t (0,j)) (t (1,j)) (t (2,j)) (t (3,j)) := by
  have rows (j l m : Fin 4) : (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      if a < b ∧ b < c then t (a,j)*t (b,l)*t (c,m) else 0) =
      t (0,j)*t (1,l)*t (2,m)+t (0,j)*t (1,l)*t (3,m)+
      t (0,j)*t (2,l)*t (3,m)+t (1,j)*t (2,l)*t (3,m) := by
    norm_num [Fin.sum_univ_four]
  unfold cube
  simp_rw [rows]
  norm_num [Fin.sum_univ_four,e3,last_of_center t ht]
  ring

private def entry (t : Mat) (r a j : Fin 4) := t (r+a,j)

private def star (r : Fin 4) (u : Fin 4 → ℂ) : Mat :=
  fun p => if p.1 = r then u p.2 else 0

private def rest2 (t : Mat) (r j : Fin 4) :=
  others (entry t r 1 j) (entry t r 2 j) (entry t r 3 j)

private def rest3 (t : Mat) (r j : Fin 4) :=
  entry t r 1 j * entry t r 2 j * entry t r 3 j

private theorem row_cases (r : Fin 4) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by
  fin_cases r <;> decide

private theorem split2 (t : Mat) (r j : Fin 4) (hz : t (r,j) = 0) :
    e2 (t (0,j)) (t (1,j)) (t (2,j)) (t (3,j)) = rest2 t r j := by
  rcases row_cases r with rfl | rfl | rfl | rfl <;>
    norm_num [entry,rest2,others,e2,hz] <;> ring

private theorem split3 (t : Mat) (r j : Fin 4) (hz : t (r,j) = 0) :
    e3 (t (0,j)) (t (1,j)) (t (2,j)) (t (3,j)) = rest3 t r j := by
  rcases row_cases r with rfl | rfl | rfl | rfl <;>
    norm_num [entry,rest3,e3,hz] <;> ring

private theorem add_star (t : Mat) (r j : Fin 4) (u : Fin 4 → ℂ) :
    e3 ((t+star r u) (0,j)) ((t+star r u) (1,j)) ((t+star r u) (2,j)) ((t+star r u) (3,j)) =
    e3 (t (0,j)) (t (1,j)) (t (2,j)) (t (3,j)) + u j * rest2 t r j := by
  fin_cases r <;> norm_num [rest2,others,entry,e3,star,Fin.reduceFinMk] <;> ring

private theorem residual_quadrics (L : Submodule ℂ Mat) (r : Fin 4)
    (hc : ∀ t ∈ L, ∀ i : Fin 4, ∑ j, t (i,j) = 0)
    (hq : ∀ t ∈ L, quad t = 0) (hb : ∀ t ∈ L, cube t = 0)
    (hrow : ∀ u : Fin 4 → ℂ, ∑ j, u j = 0 → star r u ∈ L)
    (t : Mat) (ht : t ∈ L) (hz : ∀ j, t (r,j) = 0) (k : Fin 4) :
    rest2 t r k = 0 := by
  have htotal : (∑ j, rest2 t r j) = 0 := by
    have h := hq t ht
    rw [quad_center t (hc t ht)] at h
    simpa only [fun j => split2 t r j (hz j), neg_eq_zero] using h
  let u (j : Fin 4) : ℂ := (if j = k then 4 else 0) - 1
  have hu : (∑ j, u j) = 0 := by simp [u,Finset.sum_sub_distrib]
  have htu := L.add_mem ht (hrow u hu)
  have h := hb (t+star r u) htu
  have h' := hb t ht
  rw [cube_center _ (hc _ htu)] at h
  rw [cube_center _ (hc _ ht)] at h'
  simp_rw [add_star] at h
  rw [Finset.sum_add_distrib] at h
  have dot : (∑ j, u j * rest2 t r j) = 0 := by linear_combination (h-h')/2
  simpa [u,sub_mul,ite_mul,Finset.sum_sub_distrib,htotal] using dot

private theorem others_sum (t : Mat) (r j : Fin 4)
    (hcol : (∑ i, t (i,j)) = t (r,j)) :
    entry t r 1 j + entry t r 2 j + entry t r 3 j = 0 := by
  fin_cases r <;> norm_num [Fin.sum_univ_four,entry,Fin.reduceFinMk] at * <;>
    linear_combination hcol

private theorem other_cubes (t : Mat) (r j : Fin 4)
    (hsum : entry t r 1 j + entry t r 2 j + entry t r 3 j = 0)
    (hq : rest2 t r j = 0) :
    (entry t r 1 j)^3 = rest3 t r j := by
  unfold rest2 others at hq
  unfold rest3
  linear_combination (entry t r 1 j)^2*hsum - (entry t r 1 j)*hq

private theorem zeros (x y z : ℂ) (hx : x = 0) (hsum : x+y+z = 0)
    (hq : others x y z = 0) : y = 0 ∧ z = 0 := by
  subst x
  simp only [others,zero_mul,zero_add] at hq
  rcases mul_eq_zero.mp hq with h | h
  · exact ⟨h, by simpa [h] using hsum⟩
  · exact ⟨by simpa [h] using hsum,h⟩

private theorem zero_row (t : Mat) (r : Fin 4) (ht : ∑ j, t (r,j) = 0)
    (h : ∀ j : Fin 3, t (r,j.castSucc) = 0) : ∀ j, t (r,j) = 0 := by
  have h0 : t (r,0) = 0 := h 0
  have h1 : t (r,1) = 0 := h 1
  have h2 : t (r,2) = 0 := h 2
  have h3 : t (r,3) = 0 := by simpa [Fin.sum_univ_four,h0,h1,h2] using ht
  intro j
  fin_cases j <;> assumption

-- Record the first three entries of the free row and of its successor. The centered
-- row condition supplies the last entry. Mixed cubic terms force the other two rows
-- to vanish in the kernel, while the cubic excludes the pair of rows used below.
private theorem residual_bound (L : Submodule ℂ Mat) (r : Fin 4)
    (hc : ∀ t ∈ L, ∀ i : Fin 4, ∑ j, t (i,j) = 0)
    (hq : ∀ t ∈ L, quad t = 0) (hb : ∀ t ∈ L, cube t = 0)
    (hrow : ∀ u : Fin 4 → ℂ, ∑ j, u j = 0 → star r u ∈ L)
    (hcol : ∀ t ∈ L, ∀ j : Fin 4, (∑ i, t (i,j)) = t (r,j)) :
    Module.finrank ℂ L ≤ 5 := by
  let f : L →ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 3 → ℂ)) :=
    { toFun := fun t => (fun j => t.val (r,j.castSucc), fun j => t.val (r+1,j.castSucc))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro t ht
    have h0 := zero_row t.val r (hc _ t.property r)
      (fun j => congrFun (congrArg Prod.fst ht) j)
    have h1 := zero_row t.val (r+1) (hc _ t.property (r+1))
      (fun j => congrFun (congrArg Prod.snd ht) j)
    have hrest j := zeros _ _ _ (h1 j) (others_sum _ r j (hcol _ t.property j))
      (residual_quadrics L r hc hq hb hrow _ t.property h0 j)
    apply Subtype.ext
    funext p
    rcases p with ⟨i,j⟩
    have h2 := (hrest j).1
    have h3 := (hrest j).2
    change t.val (i,j) = 0
    have hr := h0 j
    have hs := h1 j
    fin_cases r <;> fin_cases i <;> norm_num [entry,Fin.reduceFinMk] at * <;> assumption
  have hproper : LinearMap.range f ≠ ⊤ := by
    intro htop
    have hsur := LinearMap.range_eq_top.mp htop
    obtain ⟨t,ht⟩ := hsur (0, ![1,1,-2])
    have h0 := zero_row t.val r (hc _ t.property r)
      (fun j => congrFun (congrArg Prod.fst ht) j)
    have hval (j : Fin 3) : t.val (r+1,j.castSucc) = (![1,1,-2] : Fin 3 → ℂ) j :=
      congrFun (congrArg Prod.snd ht) j
    have ha : t.val (r+1,0) = 1 := hval 0
    have hb' : t.val (r+1,1) = 1 := hval 1
    have hd : t.val (r+1,2) = -2 := hval 2
    have he : t.val (r+1,3) = 0 := by
      have h := hc _ t.property (r+1)
      rw [Fin.sum_univ_four,ha,hb',hd] at h
      linear_combination h
    have hprod (j : Fin 4) := other_cubes t.val r j (others_sum _ r j (hcol _ t.property j))
      (residual_quadrics L r hc hq hb hrow _ t.property h0 j)
    have h := hb _ t.property
    rw [cube_center _ (hc _ t.property)] at h
    simp_rw [fun j => split3 _ r j (h0 j), ← hprod] at h
    norm_num [Fin.sum_univ_four,entry,ha,hb',hd,he] at h
  have hdim := Submodule.finrank_lt hproper
  rw [LinearMap.finrank_range_of_inj hinj] at hdim
  have hd : Module.finrank ℂ ((Fin 3 → ℂ) × (Fin 3 → ℂ)) = 6 := by
    simp [Module.finrank_prod]
  rw [hd] at hdim
  omega

end PEqualNP.Outside.Gct217Residual

theorem PEqualNP.Outside.L_gct_217 : ∀ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → Module.finrank ℂ L ≤ 5 := by
  intro L hL
  by_cases h : 6 ≤ Module.finrank ℂ L
  · obtain ⟨r,hr,hc⟩ := PEqualNP.Outside.Gct217.structural217 L hL h
    exact PEqualNP.Outside.Gct217Residual.residual_bound L r
      (fun t ht => (hL t ht).1) (fun t ht => (hL t ht).2.1)
      (fun t ht => (hL t ht).2.2.1) hr hc
  · omega
