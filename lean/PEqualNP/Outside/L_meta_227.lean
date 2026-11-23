import Mathlib
import PEqualNP.Defs

private lemma L_meta_227_rank_submatrix_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
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

theorem PEqualNP.Outside.L_meta_227 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasTypedRank n f s →
      PEqualNP.MetaComplexity.HasTypedRank n (fun x => f (Function.update x i b)) s := by
  rintro n f i b s ⟨τ, hτ, hr⟩
  let fix : (Fin n → Bool) → (Fin n → Bool) := fun x => Function.update x i b
  refine ⟨fun x y => τ (fix x) (fix y), ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨j, hj, hne⟩ := hτ (fix x) (fix y) hx hy
    have hji : j ≠ i := by
      intro heq
      subst heq
      simp [fix] at hne
    exact ⟨j, hj, by simpa [fix, hji] using hne⟩
  · have hsum_le :
        (∑ j : Fin n, ∑ c : Bool,
            (PEqualNP.MetaComplexity.typedMatrix n (fun x => f (fix x))
              (fun x y => τ (fix x) (fix y)) j c).rank) ≤
          ∑ j : Fin n, ∑ c : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j c).rank := by
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun c _ => ?_
      by_cases hji : j = i
      · subst hji
        have hzero :
            PEqualNP.MetaComplexity.typedMatrix n (fun x => f (fix x))
              (fun x y => τ (fix x) (fix y)) j c = 0 := by
          ext x y
          simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.zero_apply, ite_eq_right_iff,
            one_ne_zero, imp_false]
          rintro ⟨hx, hy, hτeq, _⟩
          obtain ⟨k, hk, hne⟩ := hτ (fix x) (fix y) hx hy
          have hkj : k = j := Fin.ext (hk.symm.trans hτeq)
          subst hkj
          simp [fix] at hne
        rw [hzero, Matrix.rank_zero]
        exact Nat.zero_le _
      · have hmat :
            PEqualNP.MetaComplexity.typedMatrix n (fun x => f (fix x))
              (fun x y => τ (fix x) (fix y)) j c =
            (PEqualNP.MetaComplexity.typedMatrix n f τ j c).submatrix fix fix := by
          ext x y
          simp [PEqualNP.MetaComplexity.typedMatrix, Matrix.submatrix_apply, fix, hji]
        rw [hmat]
        exact L_meta_227_rank_submatrix_le _ fix fix
    exact le_trans hsum_le hr
