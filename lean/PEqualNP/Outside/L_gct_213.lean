import Mathlib
import PEqualNP.Defs

private def L_gct_213_aux_sum : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := v 0 + v 1 + v 2
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp [Pi.smul_apply, smul_eq_mul, mul_add]

private def L_gct_213_aux_plane := LinearMap.ker L_gct_213_aux_sum

private lemma L_gct_213_aux_plane_dim :
    Module.finrank ℂ L_gct_213_aux_plane = 2 := by
  have hr : LinearMap.range L_gct_213_aux_sum = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro c
    exact ⟨![c, 0, 0], by simp [L_gct_213_aux_sum]⟩
  have h := LinearMap.finrank_range_add_finrank_ker L_gct_213_aux_sum
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_pi] at h
  change 1 + Module.finrank ℂ L_gct_213_aux_plane = 3 at h
  omega

private def L_gct_213_aux_dot : LinearMap.BilinForm ℂ (Fin 3 → ℂ) :=
  LinearMap.mk₂ ℂ (fun v w => v 0 * w 0 + v 1 * w 1 + v 2 * w 2)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

private def L_gct_213_aux_cross : LinearMap.BilinForm ℂ (Fin 3 → ℂ) :=
  LinearMap.mk₂ ℂ (fun v w =>
      v 0 * w 1 + v 0 * w 2 + v 1 * w 0 + v 1 * w 2 + v 2 * w 0 + v 2 * w 1)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

private lemma L_gct_213_aux_sum_apply (v : Fin 3 → ℂ) :
    L_gct_213_aux_sum v = v 0 + v 1 + v 2 := rfl

private lemma L_gct_213_aux_dot_apply (v w : Fin 3 → ℂ) :
    L_gct_213_aux_dot v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := rfl

private lemma L_gct_213_aux_cross_apply (v w : Fin 3 → ℂ) :
    L_gct_213_aux_cross v w =
      L_gct_213_aux_sum v * L_gct_213_aux_sum w - L_gct_213_aux_dot v w := by
  change v 0 * w 1 + v 0 * w 2 + v 1 * w 0 + v 1 * w 2 + v 2 * w 0 + v 2 * w 1 = _
  rw [L_gct_213_aux_sum_apply, L_gct_213_aux_sum_apply, L_gct_213_aux_dot_apply]
  ring

private lemma L_gct_213_aux_cross_symm (v w : Fin 3 → ℂ) :
    L_gct_213_aux_cross v w = L_gct_213_aux_cross w v := by
  simp only [L_gct_213_aux_cross_apply, L_gct_213_aux_dot_apply]
  ring

private lemma L_gct_213_aux_cross_nd : L_gct_213_aux_cross.Nondegenerate := by
  have hleft : ∀ v, (∀ w, L_gct_213_aux_cross v w = 0) → v = 0 := by
    intro v h
    have h0 := h ![1, 0, 0]
    have h1 := h ![0, 1, 0]
    have h2 := h ![0, 0, 1]
    simp [L_gct_213_aux_cross_apply, L_gct_213_aux_sum_apply, L_gct_213_aux_dot_apply] at h0 h1 h2
    funext i
    fin_cases i
    · change v 0 = 0
      linear_combination (h1 + h2 - h0) / 2
    · change v 1 = 0
      linear_combination (h0 + h2 - h1) / 2
    · change v 2 = 0
      linear_combination (h0 + h1 - h2) / 2
  exact ⟨hleft, fun v h => hleft v fun w => (L_gct_213_aux_cross_symm v w).trans (h w)⟩

private def L_gct_213_aux_plane_form := L_gct_213_aux_dot.restrict L_gct_213_aux_plane

private lemma L_gct_213_aux_plane_form_apply (v w : L_gct_213_aux_plane) :
    L_gct_213_aux_plane_form v w = L_gct_213_aux_dot v.val w.val := rfl

private lemma L_gct_213_aux_plane_form_nd : L_gct_213_aux_plane_form.Nondegenerate := by
  have hleft : ∀ v, (∀ w, L_gct_213_aux_plane_form v w = 0) → v = 0 := by
    intro v h
    have h0 := h ⟨![1, -1, 0], by
      change L_gct_213_aux_sum ![1, -1, 0] = 0
      norm_num [L_gct_213_aux_sum_apply]⟩
    have h1 := h ⟨![0, 1, -1], by
      change L_gct_213_aux_sum ![0, 1, -1] = 0
      norm_num [L_gct_213_aux_sum_apply]⟩
    have hs := v.property
    change L_gct_213_aux_sum v.val = 0 at hs
    simp [L_gct_213_aux_plane_form, L_gct_213_aux_dot_apply] at h0 h1
    rw [L_gct_213_aux_sum_apply] at hs
    apply Subtype.ext
    funext i
    fin_cases i
    · change v.val 0 = 0
      linear_combination (hs + 2 * h0 + h1) / 3
    · change v.val 1 = 0
      linear_combination (hs - h0 + h1) / 3
    · change v.val 2 = 0
      linear_combination (hs - h0 - 2 * h1) / 3
  refine ⟨hleft, fun v h => hleft v fun w => ?_⟩
  have hw := h w
  simp only [L_gct_213_aux_plane_form_apply, L_gct_213_aux_dot_apply] at hw ⊢
  linear_combination hw

private def L_gct_213_aux_form :
    LinearMap.BilinForm ℂ (L_gct_213_aux_plane × (Fin 3 → ℂ)) :=
  -L_gct_213_aux_plane_form.compl₁₂ (LinearMap.fst ℂ _ _) (LinearMap.fst ℂ _ _) -
    L_gct_213_aux_cross.compl₁₂ (LinearMap.snd ℂ _ _) (LinearMap.snd ℂ _ _)

private lemma L_gct_213_aux_form_apply
    (v w : L_gct_213_aux_plane × (Fin 3 → ℂ)) :
    L_gct_213_aux_form v w =
      -L_gct_213_aux_plane_form v.1 w.1 - L_gct_213_aux_cross v.2 w.2 := rfl

private lemma L_gct_213_aux_form_nd : L_gct_213_aux_form.Nondegenerate := by
  have hleft : ∀ v, (∀ w, L_gct_213_aux_form v w = 0) → v = 0 := by
    intro v h
    have h0 : v.1 = 0 := L_gct_213_aux_plane_form_nd.1 v.1 fun z => by
      have hz := h (z, 0)
      simp [L_gct_213_aux_form_apply] at hz
      exact hz
    have h1 : v.2 = 0 := L_gct_213_aux_cross_nd.1 v.2 fun z => by
      have hz := h (0, z)
      simpa [L_gct_213_aux_form_apply] using hz
    exact Prod.ext h0 h1
  refine ⟨hleft, fun v h => hleft v fun w => ?_⟩
  have hw := h w
  simp only [L_gct_213_aux_form_apply, L_gct_213_aux_plane_form_apply,
    L_gct_213_aux_dot_apply, L_gct_213_aux_cross_apply] at hw ⊢
  linear_combination hw

private lemma L_gct_213_aux_isotropic_dim
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {B : LinearMap.BilinForm ℂ V} (hB : B.Nondegenerate) (S : Submodule ℂ V)
    (hS : ∀ v ∈ S, ∀ w ∈ S, B v w = 0) :
    Module.finrank ℂ S + Module.finrank ℂ S ≤ Module.finrank ℂ V := by
  have hle : S ≤ B.orthogonal S := fun w hw v hv => hS v hv w hw
  have hd := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at hd
  have hv := Submodule.finrank_le S
  omega

private def L_gct_213_aux_u : (Fin 2 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun t j := t (0, j) + t (1, j)
  map_add' t s := by ext j; simp only [Pi.add_apply]; ring
  map_smul' c t := by ext j; simp [Pi.smul_apply, smul_eq_mul, mul_add]

private def L_gct_213_aux_v : (Fin 2 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun t j := t (0, j) - t (1, j)
  map_add' t s := by ext j; simp only [Pi.add_apply]; ring
  map_smul' c t := by ext j; simp [Pi.smul_apply, smul_eq_mul, mul_sub]

private lemma L_gct_213_aux_u_apply (t : Fin 2 × Fin 3 → ℂ) (j : Fin 3) :
    L_gct_213_aux_u t j = t (0, j) + t (1, j) := rfl

private lemma L_gct_213_aux_v_apply (t : Fin 2 × Fin 3 → ℂ) (j : Fin 3) :
    L_gct_213_aux_v t j = t (0, j) - t (1, j) := rfl

private lemma L_gct_213_aux_uv_injective
    {t s : Fin 2 × Fin 3 → ℂ}
    (hu : L_gct_213_aux_u t = L_gct_213_aux_u s)
    (hv : L_gct_213_aux_v t = L_gct_213_aux_v s) : t = s := by
  funext ij
  obtain ⟨i, j⟩ := ij
  have hj := congrFun hu j
  have hk := congrFun hv j
  rw [L_gct_213_aux_u_apply, L_gct_213_aux_u_apply] at hj
  rw [L_gct_213_aux_v_apply, L_gct_213_aux_v_apply] at hk
  fin_cases i
  · change t (0, j) = s (0, j)
    linear_combination (hj + hk) / 2
  · change t (1, j) = s (1, j)
    linear_combination (hj - hk) / 2

private lemma L_gct_213_aux_polarize
    {V E : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℂ E]
    (B : LinearMap.BilinForm ℂ E) (f : V →ₗ[ℂ] E)
    (hs : ∀ v w, B v w = B w v) (hq : ∀ v, B (f v) (f v) = 0) (v w : V) :
    B (f v) (f w) = 0 := by
  have h := hq (v + w)
  rw [map_add, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right, hq v, hq w, hs (f w) (f v)] at h
  linear_combination h / 2

private lemma L_gct_213_aux_form_symm (v w : L_gct_213_aux_plane × (Fin 3 → ℂ)) :
    L_gct_213_aux_form v w = L_gct_213_aux_form w v := by
  rw [L_gct_213_aux_form_apply, L_gct_213_aux_form_apply,
    L_gct_213_aux_plane_form_apply, L_gct_213_aux_plane_form_apply,
    L_gct_213_aux_dot_apply, L_gct_213_aux_dot_apply, L_gct_213_aux_cross_symm v.2 w.2]
  ring

private def L_gct_213_aux_cubic (v x : Fin 3 → ℂ) : ℂ :=
  v 1 * v 2 * x 0 + v 0 * v 2 * x 1 + v 0 * v 1 * x 2

private lemma L_gct_213_aux_q_identity (t : Fin 2 × Fin 3 → ℂ) :
    L_gct_213_aux_cross (L_gct_213_aux_u t) (L_gct_213_aux_u t) -
        L_gct_213_aux_cross (L_gct_213_aux_v t) (L_gct_213_aux_v t) =
      4 * (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) := by
  norm_num [Fin.sum_univ_three, L_gct_213_aux_cross_apply, L_gct_213_aux_sum_apply,
    L_gct_213_aux_dot_apply, L_gct_213_aux_u_apply, L_gct_213_aux_v_apply]
  ring

private lemma L_gct_213_aux_x_identity (t : Fin 2 × Fin 3 → ℂ) (x : Fin 3 → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l) + t (0, j) * x l + t (1, j) * x l) =
      (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) +
        L_gct_213_aux_cross (L_gct_213_aux_u t) x := by
  norm_num [Fin.sum_univ_three, L_gct_213_aux_cross_apply, L_gct_213_aux_sum_apply,
    L_gct_213_aux_dot_apply, L_gct_213_aux_u_apply]
  ring

private lemma L_gct_213_aux_cubic_identity (t : Fin 2 × Fin 3 → ℂ) (x : Fin 3 → ℂ) :
    L_gct_213_aux_cubic (L_gct_213_aux_u t) x - L_gct_213_aux_cubic (L_gct_213_aux_v t) x =
      2 * (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * x m) := by
  norm_num [Fin.sum_univ_three, L_gct_213_aux_cubic, L_gct_213_aux_u_apply, L_gct_213_aux_v_apply]
  ring

private lemma L_gct_213_aux_span_dim {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (z : V) (hz : z ≠ 0)
    (h : ∀ r ∈ S, ∃ c : ℂ, r = c • z) :
    Module.finrank ℂ S ≤ 1 := by
  have hle : S ≤ Submodule.span ℂ {z} := by
    intro r hr
    obtain ⟨c, rfl⟩ := h r hr
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z)
  simpa [finrank_span_singleton hz] using Submodule.finrank_mono hle

private lemma L_gct_213_aux_isotropic_line {z r : Fin 3 → ℂ}
    (hz0 : z 0 ≠ 0) (hsz : L_gct_213_aux_sum z = 0)
    (hdz : L_gct_213_aux_dot z z = 0)
    (hsr : L_gct_213_aux_sum r = 0) (hdr : L_gct_213_aux_dot r z = 0) :
    ∃ c : ℂ, r = c • z := by
  rw [L_gct_213_aux_sum_apply] at hsz hsr
  rw [L_gct_213_aux_dot_apply] at hdz hdr
  have hz12 : z 1 - z 2 ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    rw [← he'] at hsz hdz
    have hz1 : z 1 * z 1 = 0 := by
      linear_combination (hdz - (z 0 - 2 * z 1) * hsz) / 6
    have hz1' := (mul_eq_zero.mp hz1).elim id id
    exact hz0 (by linear_combination hsz - 2 * hz1')
  let c := r 0 / z 0
  use c
  have hr0 : r 0 - c * z 0 = 0 := by
    dsimp [c]
    rw [div_mul_cancel₀ _ hz0, sub_self]
  have hr1 : r 1 - c * z 1 = 0 := by
    apply (mul_eq_zero.mp (_ : (z 1 - z 2) * (r 1 - c * z 1) = 0)).resolve_left hz12
    linear_combination hdr - c * hdz - z 2 * (hsr - c * hsz) - (z 0 - z 2) * hr0
  have hr2 : r 2 - c * z 2 = 0 := by
    linear_combination hsr - c * hsz - hr0 - hr1
  funext i
  fin_cases i
  · exact sub_eq_zero.mp hr0
  · exact sub_eq_zero.mp hr1
  · exact sub_eq_zero.mp hr2

private lemma L_gct_213_aux_cubic_smul (c d : ℂ) (v x : Fin 3 → ℂ) :
    L_gct_213_aux_cubic (c • v) (d • x) = c ^ 2 * d * L_gct_213_aux_cubic v x := by
  simp only [L_gct_213_aux_cubic, Pi.smul_apply, smul_eq_mul]
  ring

private lemma L_gct_213_aux_products {w : Fin 3 → ℂ}
    (hs : L_gct_213_aux_sum w = 0) (hd : L_gct_213_aux_dot w w = 0) :
    w 1 * w 2 = w 0 ^ 2 ∧ w 0 * w 2 = w 1 ^ 2 ∧ w 0 * w 1 = w 2 ^ 2 := by
  rw [L_gct_213_aux_sum_apply] at hs
  rw [L_gct_213_aux_dot_apply] at hd
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -(hd + (w 0 - w 1 - w 2) * hs) / 2
  · linear_combination -(hd + (w 1 - w 0 - w 2) * hs) / 2
  · linear_combination -(hd + (w 2 - w 0 - w 1) * hs) / 2

private lemma L_gct_213_aux_ne_coords {w : Fin 3 → ℂ} (hw : w ≠ 0)
    (hs : L_gct_213_aux_sum w = 0) (hd : L_gct_213_aux_dot w w = 0) :
    w 0 ≠ 0 ∧ w 1 ≠ 0 ∧ w 2 ≠ 0 := by
  obtain ⟨h0, h1, h2⟩ := L_gct_213_aux_products hs hd
  rw [L_gct_213_aux_sum_apply] at hs
  have hz : w 0 = 0 → w 1 = 0 → w 2 = 0 → False := by
    intro e0 e1 e2
    apply hw
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
  refine ⟨?_, ?_, ?_⟩
  · intro e0
    rw [e0, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h0
    rcases mul_eq_zero.mp h0 with e1 | e2
    · exact hz e0 e1 (by linear_combination hs - e0 - e1)
    · exact hz e0 (by linear_combination hs - e0 - e2) e2
  · intro e1
    rw [e1, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h1
    rcases mul_eq_zero.mp h1 with e0 | e2
    · exact hz e0 e1 (by linear_combination hs - e0 - e1)
    · exact hz (by linear_combination hs - e1 - e2) e1 e2
  · intro e2
    rw [e2, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h2
    rcases mul_eq_zero.mp h2 with e0 | e1
    · exact hz e0 (by linear_combination hs - e0 - e2) e2
    · exact hz (by linear_combination hs - e1 - e2) e1 e2

private lemma L_gct_213_aux_exception
    (X : Submodule ℂ (Fin 3 → ℂ)) (w : Fin 3 → ℂ) (hw : w ≠ 0)
    (hsw : L_gct_213_aux_sum w = 0) (hdw : L_gct_213_aux_dot w w = 0)
    (hsX : ∀ x ∈ X, L_gct_213_aux_sum x = 0)
    (hcX : ∀ x ∈ X, L_gct_213_aux_cubic w x = 0) (hX : X ≠ ⊥) :
    Module.finrank ℂ X ≤ 1 ∧
      ∀ u v : Fin 3 → ℂ,
        L_gct_213_aux_sum u = 0 → L_gct_213_aux_sum v = 0 →
        L_gct_213_aux_dot v w = 0 →
        (∀ x ∈ X, L_gct_213_aux_dot u x = 0 ∧
          L_gct_213_aux_cubic u x = L_gct_213_aux_cubic v x) → u = 0 := by
  obtain ⟨hw0, hw1, hw2⟩ := L_gct_213_aux_ne_coords hw hsw hdw
  let p : Fin 3 → ℂ := fun j => w j ^ 2
  obtain ⟨hp0, hp1, hp2⟩ := L_gct_213_aux_products hsw hdw
  change w 1 * w 2 = p 0 at hp0
  change w 0 * w 2 = p 1 at hp1
  change w 0 * w 1 = p 2 at hp2
  have hp0ne : p 0 ≠ 0 := pow_ne_zero _ hw0
  have hp1ne : p 1 ≠ 0 := pow_ne_zero _ hw1
  have hp2ne : p 2 ≠ 0 := pow_ne_zero _ hw2
  have hp : p ≠ 0 := fun h => hp0ne (congrFun h 0)
  have hsp : L_gct_213_aux_sum p = 0 := by
    rw [L_gct_213_aux_sum_apply]
    rw [L_gct_213_aux_dot_apply] at hdw
    dsimp [p]
    linear_combination hdw
  have hpw (x : Fin 3 → ℂ) : L_gct_213_aux_dot x p = L_gct_213_aux_cubic w x := by
    rw [L_gct_213_aux_dot_apply, L_gct_213_aux_cubic, hp0, hp1, hp2]
    ring
  have hdp : L_gct_213_aux_dot p p = 0 := by
    calc
      L_gct_213_aux_dot p p = L_gct_213_aux_cubic w p := hpw p
      _ = (w 0 * w 1 * w 2) * L_gct_213_aux_sum w := by
        simp only [L_gct_213_aux_cubic, L_gct_213_aux_sum_apply, p]
        ring
      _ = 0 := by rw [hsw, mul_zero]
  have hpp : L_gct_213_aux_cubic p p ≠ 0 := by
    have he : L_gct_213_aux_cubic p p = 3 * p 0 * p 1 * p 2 := by
      unfold L_gct_213_aux_cubic
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp0ne) hp1ne) hp2ne
  have hXspan : ∀ x ∈ X, ∃ c : ℂ, x = c • p := by
    intro x hx
    exact L_gct_213_aux_isotropic_line hp0ne hsp hdp (hsX x hx) ((hpw x).trans (hcX x hx))
  refine ⟨L_gct_213_aux_span_dim X p hp hXspan, ?_⟩
  intro u v hsu hsv hvw huv
  obtain ⟨x, hx, hx0⟩ := X.ne_bot_iff.mp hX
  obtain ⟨c, hc⟩ := hXspan x hx
  have hc0 : c ≠ 0 := by
    intro h
    apply hx0
    rw [hc, h, zero_smul]
  have huX := (huv x hx).1
  rw [hc, LinearMap.BilinForm.smul_right] at huX
  have hup := (mul_eq_zero.mp huX).resolve_left hc0
  obtain ⟨a, ha⟩ := L_gct_213_aux_isotropic_line hp0ne hsp hdp hsu hup
  obtain ⟨b, hb⟩ := L_gct_213_aux_isotropic_line hw0 hsw hdw hsv hvw
  have hcube := (huv x hx).2
  have hwpp : L_gct_213_aux_cubic w p = 0 := (hpw p).symm.trans hdp
  rw [ha, hb, hc, L_gct_213_aux_cubic_smul, L_gct_213_aux_cubic_smul, hwpp, mul_zero] at hcube
  have ha0 : a = 0 := by
    by_contra h
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h) hc0) hpp hcube
  simpa [ha0] using ha

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_gct_213 :
    ∀ (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (X : Submodule ℂ (Fin 3 → ℂ)) (Y : Submodule ℂ (Fin 2 → ℂ)), (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) → (∀ t ∈ L, ∀ x ∈ X, (∑ j, (t (0, j) + t (1, j) + x j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l) + t (0, j) * x l + t (1, j) * x l) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * x m) = 0) → (∀ t ∈ L, ∀ y ∈ Y, (∑ j, (t (0, j) + t (1, j))) + y 0 + y 1 = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) + (∑ j, t (0, j)) * y 1 + y 0 * (∑ j, t (1, j)) = 0) → Module.finrank ℂ L + Module.finrank ℂ X + Module.finrank ℂ Y ≤ 3 := by
  intro L X Y hL hX hY
  have hsumU (t) (ht : t ∈ L) : L_gct_213_aux_sum (L_gct_213_aux_u t) = 0 := by
    simpa only [Fin.sum_univ_three, L_gct_213_aux_sum_apply, L_gct_213_aux_u_apply]
      using (hL t ht).1
  have hsumX (x) (hx : x ∈ X) : L_gct_213_aux_sum x = 0 := by
    simpa [Fin.sum_univ_three, L_gct_213_aux_sum_apply] using (hX 0 L.zero_mem x hx).1
  have hsumY (y) (hy : y ∈ Y) : y 0 + y 1 = 0 := by
    simpa using (hY 0 L.zero_mem y hy).1
  have hdotX (t) (ht : t ∈ L) (x) (hx : x ∈ X) :
      L_gct_213_aux_dot (L_gct_213_aux_u t) x = 0 := by
    have he := (hX t ht x hx).2.1
    rw [L_gct_213_aux_x_identity, (hL t ht).2, zero_add, L_gct_213_aux_cross_apply,
      hsumU t ht, zero_mul, zero_sub, neg_eq_zero] at he
    exact he
  have hcubic (t) (ht : t ∈ L) (x) (hx : x ∈ X) :
      L_gct_213_aux_cubic (L_gct_213_aux_u t) x =
        L_gct_213_aux_cubic (L_gct_213_aux_v t) x := by
    apply sub_eq_zero.mp
    rw [L_gct_213_aux_cubic_identity, (hX t ht x hx).2.2, mul_zero]
  have hYdim : Module.finrank ℂ Y ≤ 1 := by
    apply L_gct_213_aux_span_dim Y ![1, -1]
    · intro h
      have he := congrFun h (0 : Fin 2)
      norm_num at he
    · intro y hy
      refine ⟨y 0, ?_⟩
      funext i
      fin_cases i
      · change y 0 = y 0 * 1
        rw [mul_one]
      · change y 1 = y 0 * -1
        linear_combination hsumY y hy
  let U : L →ₗ[ℂ] L_gct_213_aux_plane :=
    (L_gct_213_aux_u.comp L.subtype).codRestrict _ fun t => hsumU t.val t.property
  let V : L →ₗ[ℂ] (Fin 3 → ℂ) := L_gct_213_aux_v.comp L.subtype
  let F := U.prod V
  have hF_inj : Function.Injective F := by
    intro t s h
    apply Subtype.ext
    exact L_gct_213_aux_uv_injective
      (congrArg (fun z => z.1.val) h) (congrArg Prod.snd h)
  have hdiag (t : L) : L_gct_213_aux_form (F t) (F t) = 0 := by
    have h := L_gct_213_aux_q_identity t.val
    rw [(hL t.val t.property).2, mul_zero,
      L_gct_213_aux_cross_apply (L_gct_213_aux_u t.val),
      hsumU t.val t.property, zero_mul, zero_sub] at h
    exact h
  have hbil := L_gct_213_aux_polarize L_gct_213_aux_form F L_gct_213_aux_form_symm hdiag
  have hLdim : Module.finrank ℂ L ≤ 2 := by
    have h := L_gct_213_aux_isotropic_dim L_gct_213_aux_form_nd (LinearMap.range F) (by
      rintro _ ⟨t, rfl⟩ _ ⟨s, rfl⟩
      exact hbil t s)
    rw [← (LinearEquiv.ofInjective F hF_inj).finrank_eq, Module.finrank_prod,
      L_gct_213_aux_plane_dim, Module.finrank_pi] at h
    change Module.finrank ℂ L + Module.finrank ℂ L ≤ 2 + 3 at h
    omega
  let XP : X →ₗ[ℂ] L_gct_213_aux_plane :=
    X.subtype.codRestrict _ fun x => hsumX x.val x.property
  have hXP_inj : Function.Injective XP := by
    intro x z h
    apply Subtype.ext
    exact congrArg (fun z : L_gct_213_aux_plane => z.val) h
  have hUXdim : Module.finrank ℂ (LinearMap.range U) + Module.finrank ℂ X ≤ 2 := by
    have hle : LinearMap.range U ≤ L_gct_213_aux_plane_form.orthogonal (LinearMap.range XP) := by
      rintro _ ⟨t, rfl⟩ _ ⟨x, rfl⟩
      change L_gct_213_aux_dot x.val (L_gct_213_aux_u t.val) = 0
      have h := hdotX t.val t.property x.val x.property
      rw [L_gct_213_aux_dot_apply] at h ⊢
      linear_combination h
    have h := Submodule.finrank_mono hle
    rw [LinearMap.BilinForm.finrank_orthogonal L_gct_213_aux_plane_form_nd,
      L_gct_213_aux_plane_dim, ← (LinearEquiv.ofInjective XP hXP_inj).finrank_eq] at h
    have hx := Submodule.finrank_le (LinearMap.range XP)
    rw [L_gct_213_aux_plane_dim, ← (LinearEquiv.ofInjective XP hXP_inj).finrank_eq] at hx
    omega
  let K := LinearMap.ker U
  let VK := V.comp K.subtype
  have hVK_inj : Function.Injective VK := by
    intro t s h
    apply Subtype.ext
    apply hF_inj
    apply Prod.ext
    · change U t.val = U s.val
      exact t.property.trans s.property.symm
    · exact h
  have hKdim : Module.finrank ℂ K ≤ 1 := by
    have h := L_gct_213_aux_isotropic_dim L_gct_213_aux_cross_nd (LinearMap.range VK) (by
      rintro _ ⟨t, rfl⟩ _ ⟨s, rfl⟩
      have he := hbil t.val s.val
      change -L_gct_213_aux_plane_form (U t.val) (U s.val) -
        L_gct_213_aux_cross (VK t) (VK s) = 0 at he
      have ht : U t.val = 0 := t.property
      simp [ht] at he
      exact he)
    rw [← (LinearEquiv.ofInjective VK hVK_inj).finrank_eq, Module.finrank_pi] at h
    change Module.finrank ℂ K + Module.finrank ℂ K ≤ 3 at h
    omega
  have hdim := LinearMap.finrank_range_add_finrank_ker U
  change Module.finrank ℂ (LinearMap.range U) + Module.finrank ℂ K = Module.finrank ℂ L at hdim
  by_cases hY0 : Y = ⊥
  · rw [hY0, finrank_bot]
    omega
  by_cases hX0 : X = ⊥
  · rw [hX0, finrank_bot]
    omega
  by_cases hK0 : K = ⊥
  · rw [hK0, finrank_bot] at hdim
    omega
  obtain ⟨y, hy, hy0⟩ := Y.ne_bot_iff.mp hY0
  have hy0' : y 0 ≠ 0 := by
    intro he
    apply hy0
    funext i
    fin_cases i
    · exact he
    · change y 1 = 0
      linear_combination hsumY y hy - he
  have hsumV (t : L) : L_gct_213_aux_sum (V t) = 0 := by
    have h := (hY t.val t.property y hy).2
    rw [(hL t.val t.property).2, zero_add] at h
    have hy1 : y 1 = -y 0 := by linear_combination hsumY y hy
    rw [hy1, Fin.sum_univ_three, Fin.sum_univ_three] at h
    have hv : y 0 * L_gct_213_aux_sum (V t) = 0 := by
      change y 0 * L_gct_213_aux_sum (L_gct_213_aux_v t.val) = 0
      simp only [L_gct_213_aux_sum_apply, L_gct_213_aux_v_apply]
      linear_combination -h
    exact (mul_eq_zero.mp hv).resolve_left hy0'
  obtain ⟨k, hk, hk0⟩ := K.ne_bot_iff.mp hK0
  have hkU : U k = 0 := hk
  have hku : L_gct_213_aux_u k.val = 0 := congrArg Subtype.val hkU
  let w := V k
  have hw : w ≠ 0 := by
    intro hw0
    apply hk0
    apply hF_inj
    rw [map_zero]
    exact Prod.ext hkU hw0
  have hvw (t : L) : L_gct_213_aux_dot (V t) w = 0 := by
    have he := hbil t k
    change -L_gct_213_aux_plane_form (U t) (U k) - L_gct_213_aux_cross (V t) w = 0 at he
    rw [hkU, LinearMap.BilinForm.zero_right, neg_zero, zero_sub, neg_eq_zero,
      L_gct_213_aux_cross_apply, hsumV t, zero_mul, zero_sub, neg_eq_zero] at he
    exact he
  have hcX (x) (hx : x ∈ X) : L_gct_213_aux_cubic w x = 0 := by
    have he := hcubic k.val k.property x hx
    change L_gct_213_aux_cubic (L_gct_213_aux_u k.val) x = L_gct_213_aux_cubic w x at he
    rw [hku] at he
    simpa [L_gct_213_aux_cubic] using he.symm
  obtain ⟨hXdim, hvanish⟩ := L_gct_213_aux_exception X w hw (hsumV k) (hvw k) hsumX hcX hX0
  have hU0 : LinearMap.range U = ⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨t, rfl⟩
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact hvanish _ _ (hsumU t.val t.property) (hsumV t) (hvw t)
      fun x hx => ⟨hdotX t.val t.property x hx, hcubic t.val t.property x hx⟩
  rw [hU0, finrank_bot] at hdim
  omega
