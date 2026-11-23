import Mathlib
import PEqualNP.Defs

private lemma L_meta_226_rank_submatrix_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix β β ℚ) (g h : α → β) :
    (M.submatrix g h).rank ≤ M.rank := by
  let pullL : (β → ℚ) →ₗ[ℚ] (α → ℚ) :=
    { toFun := fun w x => w (g x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let pushR : (α → ℚ) →ₗ[ℚ] (β → ℚ) :=
    { toFun := fun v z => ∑ y : α, if h y = z then v y else 0
      map_add' := fun u v => by
        ext z
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
      map_smul' := fun c v => by
        ext z
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring }
  have hcomp : (M.submatrix g h).mulVecLin = pullL.comp (M.mulVecLin.comp pushR) := by
    ext v x
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      LinearMap.comp_apply, pullL, pushR, LinearMap.coe_mk, AddHom.coe_mk]
    calc
      ∑ y : α, M (g x) (h y) * v y
        = ∑ y : α, ∑ z : β, M (g x) z * (if h y = z then v y else 0) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_eq_single (h y)]
          · simp
          · intro z _ hz
            simp [Ne.symm hz]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
      _ = ∑ z : β, ∑ y : α, M (g x) z * (if h y = z then v y else 0) := Finset.sum_comm
      _ = ∑ z : β, M (g x) z * ∑ y : α, (if h y = z then v y else 0) := by
          refine Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm
  show Module.finrank ℚ (LinearMap.range (M.submatrix g h).mulVecLin) ≤
    Module.finrank ℚ (LinearMap.range M.mulVecLin)
  rw [hcomp, LinearMap.range_comp]
  exact le_trans (Submodule.finrank_map_le pullL _)
    (Submodule.finrank_mono (LinearMap.range_comp_le_range pushR M.mulVecLin))

theorem PEqualNP.Outside.L_meta_226 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (s : ℕ),
      PEqualNP.MetaComplexity.HasTypedRank n f s →
      PEqualNP.MetaComplexity.HasTypedRank n (fun x => f (Function.update x i (!x i))) s := by
  rintro n f i s ⟨τ, hτ, hr⟩
  let flip : (Fin n → Bool) → (Fin n → Bool) := fun x => Function.update x i (!x i)
  refine ⟨fun x y => τ (flip x) (flip y), ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨j, hj, hne⟩ := hτ (flip x) (flip y) hx hy
    refine ⟨j, hj, ?_⟩
    by_cases hji : j = i
    · subst hji
      simp only [flip, Function.update_self] at hne
      intro heq
      exact hne (congrArg (!·) heq)
    · simpa [flip, Function.update_of_ne hji] using hne
  · have hmat : ∀ (j : Fin n) (b : Bool),
        PEqualNP.MetaComplexity.typedMatrix n (fun x => f (flip x))
          (fun x y => τ (flip x) (flip y)) j b =
        (PEqualNP.MetaComplexity.typedMatrix n f τ j (if j = i then !b else b)).submatrix
          flip flip := by
      intro j b
      ext x y
      by_cases hji : j = i
      · subst hji
        simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.submatrix_apply, ite_true, flip,
          Function.update_self]
        have hiff : x j = b ↔ (!x j) = (!b) := by cases x j <;> cases b <;> decide
        simp only [hiff]
      · simp [PEqualNP.MetaComplexity.typedMatrix, Matrix.submatrix_apply, hji, flip]
    have hsum_le :
        (∑ j : Fin n, ∑ b : Bool,
            (PEqualNP.MetaComplexity.typedMatrix n (fun x => f (flip x))
              (fun x y => τ (flip x) (flip y)) j b).rank) ≤
          ∑ j : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hinner :
          ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n (fun x => f (flip x))
            (fun x y => τ (flip x) (flip y)) j b).rank ≤
          ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j (if j = i then !b else b)).rank := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [hmat j b]
        exact L_meta_226_rank_submatrix_le _ flip flip
      refine le_trans hinner ?_
      by_cases hji : j = i
      · simp [hji, add_comm]
      · simp [hji]
    exact le_trans hsum_le hr
