import Mathlib
import PEqualNP.Defs

private abbrev Mat₂ := Fin 2 × Fin 2 → ℂ

private def polarValue (a b : Mat₂) : ℂ :=
  a (0, 0) * b (1, 1) + a (0, 1) * b (1, 0) +
    a (1, 0) * b (0, 1) + a (1, 1) * b (0, 0)

private noncomputable def polar : Mat₂ →ₗ[ℂ] Module.Dual ℂ Mat₂ :=
  LinearMap.mk₂ ℂ polarValue
    (by intro a b x; simp only [polarValue, Pi.add_apply]; ring)
    (by intro c a x; simp only [polarValue, Pi.smul_apply, smul_eq_mul]; ring)
    (by intro a x y; simp only [polarValue, Pi.add_apply]; ring)
    (by intro c a x; simp only [polarValue, Pi.smul_apply, smul_eq_mul]; ring)

private theorem polar_apply (a b : Mat₂) : polar a b = polarValue a b := rfl

private theorem polar_injective : Function.Injective polar := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h (b : Mat₂) : polar a b = 0 := by rw [ha]; rfl
  have h00 : a (0, 0) = 0 := by
    simpa [polar_apply, polarValue, Pi.single_apply] using h (Pi.single (1, 1) 1)
  have h01 : a (0, 1) = 0 := by
    simpa [polar_apply, polarValue, Pi.single_apply] using h (Pi.single (1, 0) 1)
  have h10 : a (1, 0) = 0 := by
    simpa [polar_apply, polarValue, Pi.single_apply] using h (Pi.single (0, 1) 1)
  have h11 : a (1, 1) = 0 := by
    simpa [polar_apply, polarValue, Pi.single_apply] using h (Pi.single (0, 0) 1)
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> assumption

private theorem level_finrank (L : Submodule ℂ Mat₂)
    (hL : ∀ t ∈ L, t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 1) * t (1, 0) = 0) :
    Module.finrank ℂ L ≤ 1 := by
  let J : Mat₂ := fun _ => 1
  let W := L ⊔ Submodule.span ℂ ({J} : Set Mat₂)
  have hJ : J ∉ L := by
    intro h
    have hz := (hL J h).1
    norm_num [J] at hz
  have hJW : J ∈ W :=
    (le_sup_right : Submodule.span ℂ ({J} : Set Mat₂) ≤ W) (Submodule.subset_span (by simp))
  have hstrict : L < W := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    apply hJ
    rwa [hEq]
  have hLL (t u : Mat₂) (ht : t ∈ L) (hu : u ∈ L) : polar t u = 0 := by
    have htQ := (hL t ht).2
    have huQ := (hL u hu).2
    have hadd := (hL (t + u) (L.add_mem ht hu)).2
    simp only [Pi.add_apply] at hadd
    simp only [polar_apply, polarValue]
    linear_combination hadd - htQ - huQ
  have hLJ (t : Mat₂) (ht : t ∈ L) : polar t J = 0 := by
    simpa [polar_apply, polarValue, J] using (hL t ht).1
  have hAnn (t : L) : polar.domRestrict L t ∈ W.dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).2
    intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    change polar t.1 (u + c • J) = 0
    simp [hLL _ _ t.2 hu, hLJ _ t.2]
  have hinj : Function.Injective ((polar.domRestrict L).codRestrict W.dualAnnihilator hAnn) :=
    fun a b hab => Subtype.ext (polar_injective (congrArg Subtype.val hab))
  have hr := LinearMap.finrank_le_finrank_of_injective hinj
  have hc := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hs := Submodule.finrank_lt_finrank_of_lt hstrict
  have hd : Module.finrank ℂ Mat₂ = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  omega

private theorem append_sum_zero_finrank
    (S : Submodule ℂ (Fin 2 → ℂ))
    (hS : ∀ v ∈ S, v 0 + v 1 = 0) :
    Module.finrank ℂ S ≤ 1 := by
  let eval : S →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).comp S.subtype
  have hinj : Function.Injective eval := by
    intro v w h
    change (v : Fin 2 → ℂ) 0 = (w : Fin 2 → ℂ) 0 at h
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h
    · change (v : Fin 2 → ℂ) 1 = (w : Fin 2 → ℂ) 1
      linear_combination hS v v.property - hS w w.property - h
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

private theorem append_exists_nonzero_coordinate
    (S : Submodule ℂ (Fin 2 → ℂ))
    (hS : ∀ v ∈ S, v 0 + v 1 = 0)
    (hpos : 0 < Module.finrank ℂ S) :
    ∃ v ∈ S, v 0 ≠ 0 := by
  have hne : S ≠ ⊥ := Submodule.one_le_finrank_iff.mp hpos
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv, ?_⟩
  intro hzero
  apply hvne
  have hone : v 1 = 0 := by linear_combination hS v hv - hzero
  funext i
  fin_cases i
  · exact hzero
  · exact hone

private theorem append_dimensions
    (L : Submodule ℂ (Fin 2 × Fin 2 → ℂ))
    (X Y : Submodule ℂ (Fin 2 → ℂ))
    (hL : ∀ t ∈ L, t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 1) * t (1, 0) = 0)
    (hX : ∀ t ∈ L, ∀ x ∈ X,
      t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) + x 0 + x 1 = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 1) * t (1, 0) +
        (t (0, 0) + t (1, 0)) * x 1 + (t (0, 1) + t (1, 1)) * x 0 = 0)
    (hY : ∀ t ∈ L, ∀ y ∈ Y,
      t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) + y 0 + y 1 = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 1) * t (1, 0) +
        (t (0, 0) + t (0, 1)) * y 1 + y 0 * (t (1, 0) + t (1, 1)) = 0) :
    Module.finrank ℂ X ≤ 1 ∧ Module.finrank ℂ Y ≤ 1 ∧
      (0 < Module.finrank ℂ X → 0 < Module.finrank ℂ Y → L = ⊥) := by
  have hXsum : ∀ x ∈ X, x 0 + x 1 = 0 := by
    intro x hx
    simpa using (hX 0 L.zero_mem x hx).1
  have hYsum : ∀ y ∈ Y, y 0 + y 1 = 0 := by
    intro y hy
    simpa using (hY 0 L.zero_mem y hy).1
  refine ⟨append_sum_zero_finrank X hXsum, append_sum_zero_finrank Y hYsum, ?_⟩
  intro hXpos hYpos
  obtain ⟨x, hx, hx0⟩ := append_exists_nonzero_coordinate X hXsum hXpos
  obtain ⟨y, hy, hy0⟩ := append_exists_nonzero_coordinate Y hYsum hYpos
  have hx1 : x 1 = -x 0 := by linear_combination hXsum x hx
  have hy1 : y 1 = -y 0 := by linear_combination hYsum y hy
  apply L.eq_bot_iff.mpr
  intro t ht
  obtain ⟨hSum, hPerm⟩ := hL t ht
  have hXperm := (hX t ht x hx).2
  have hYperm := (hY t ht y hy).2
  rw [hx1, hPerm, zero_add] at hXperm
  rw [hy1, hPerm, zero_add] at hYperm
  have hColFactor :
      (t (0, 1) + t (1, 1) - (t (0, 0) + t (1, 0))) * x 0 = 0 := by
    linear_combination hXperm
  have hRowFactor :
      (t (1, 0) + t (1, 1) - (t (0, 0) + t (0, 1))) * y 0 = 0 := by
    linear_combination hYperm
  have hColDiff := (mul_eq_zero.mp hColFactor).resolve_right hx0
  have hRowDiff := (mul_eq_zero.mp hRowFactor).resolve_right hy0
  have hTwo : (2 : ℂ) ≠ 0 := by norm_num
  have hColTwice : 2 * (t (0, 0) + t (1, 0)) = 0 := by
    linear_combination hSum - hColDiff
  have hRowTwice : 2 * (t (0, 0) + t (0, 1)) = 0 := by
    linear_combination hSum - hRowDiff
  have hCol := (mul_eq_zero.mp hColTwice).resolve_left hTwo
  have hRow := (mul_eq_zero.mp hRowTwice).resolve_left hTwo
  have hb : t (0, 1) = -t (0, 0) := by linear_combination hRow
  have hc : t (1, 0) = -t (0, 0) := by linear_combination hCol
  have hd : t (1, 1) = t (0, 0) := by
    linear_combination hSum - hCol - hRow
  rw [hb, hc, hd] at hPerm
  have hSquareTwice : 2 * (t (0, 0) * t (0, 0)) = 0 := by
    linear_combination hPerm
  have hSquare := (mul_eq_zero.mp hSquareTwice).resolve_left hTwo
  have ha : t (0, 0) = 0 := (mul_eq_zero.mp hSquare).elim id id
  rw [ha, neg_zero] at hb hc
  rw [ha] at hd
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> first
    | exact ha
    | exact hb
    | exact hc
    | exact hd

theorem PEqualNP.Outside.L_gct_212 : ∀ (L : Submodule ℂ (Fin 2 × Fin 2 → ℂ)) (X : Submodule ℂ (Fin 2 → ℂ)) (Y : Submodule ℂ (Fin 2 → ℂ)), (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) → (∀ t ∈ L, ∀ x ∈ X, (∑ j, (t (0, j) + t (1, j) + x j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l) + t (0, j) * x l + t (1, j) * x l) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * x m) = 0) → (∀ t ∈ L, ∀ y ∈ Y, (∑ j, (t (0, j) + t (1, j))) + y 0 + y 1 = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) + (∑ j, t (0, j)) * y 1 + y 0 * (∑ j, t (1, j)) = 0) → Module.finrank ℂ L + Module.finrank ℂ X + Module.finrank ℂ Y ≤ 2 := by
  intro L X Y hL hX hY
  have hLn (t : Mat₂) (ht : t ∈ L) :
      t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 1) * t (1, 0) = 0 := by
    obtain ⟨hs, hp⟩ := hL t ht
    simp [Fin.sum_univ_two] at hs hp
    exact ⟨by linear_combination hs, by linear_combination hp⟩
  have hXn (t : Mat₂) (ht : t ∈ L) (x : Fin 2 → ℂ) (hx : x ∈ X) :
      t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) + x 0 + x 1 = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 1) * t (1, 0) +
        (t (0, 0) + t (1, 0)) * x 1 + (t (0, 1) + t (1, 1)) * x 0 = 0 := by
    obtain ⟨hs, hp, _⟩ := hX t ht x hx
    simp [Fin.sum_univ_two] at hs hp
    exact ⟨by linear_combination hs, by linear_combination hp⟩
  have hYn (t : Mat₂) (ht : t ∈ L) (y : Fin 2 → ℂ) (hy : y ∈ Y) :
      t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) + y 0 + y 1 = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 1) * t (1, 0) +
        (t (0, 0) + t (0, 1)) * y 1 + y 0 * (t (1, 0) + t (1, 1)) = 0 := by
    obtain ⟨hs, hp⟩ := hY t ht y hy
    simp [Fin.sum_univ_two] at hs hp
    exact ⟨by linear_combination hs, by linear_combination hp⟩
  have hLdim : Module.finrank ℂ L ≤ 1 := level_finrank L hLn
  obtain ⟨hXdim, hYdim, hbot⟩ := append_dimensions L X Y hLn hXn hYn
  by_cases h : 0 < Module.finrank ℂ X ∧ 0 < Module.finrank ℂ Y
  · rw [hbot h.1 h.2, finrank_bot, zero_add]
    exact Nat.add_le_add hXdim hYdim
  · have hz : Module.finrank ℂ X = 0 ∨ Module.finrank ℂ Y = 0 := by omega
    rcases hz with hx | hy
    · rw [hx, add_zero]
      exact Nat.add_le_add hLdim hYdim
    · rw [hy, add_zero]
      exact Nat.add_le_add hLdim hXdim
