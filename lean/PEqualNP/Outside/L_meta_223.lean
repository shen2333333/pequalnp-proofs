import Mathlib
import PEqualNP.Defs

private lemma L_meta_223_rank_mask_le {α : Type} [Fintype α]
    (M : Matrix α α ℚ) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    (Matrix.of fun x y => if P x ∧ Q y then M x y else 0).rank ≤ M.rank := by
  let maskL : (α → ℚ) →ₗ[ℚ] (α → ℚ) :=
    { toFun := fun w x => if P x then w x else 0
      map_add' := fun u v => by ext x; by_cases h : P x <;> simp [h]
      map_smul' := fun c v => by ext x; by_cases h : P x <;> simp [h] }
  let maskR : (α → ℚ) →ₗ[ℚ] (α → ℚ) :=
    { toFun := fun v y => if Q y then v y else 0
      map_add' := fun u v => by ext y; by_cases h : Q y <;> simp [h]
      map_smul' := fun c v => by ext y; by_cases h : Q y <;> simp [h] }
  have hcomp :
      (Matrix.of fun x y => if P x ∧ Q y then M x y else 0).mulVecLin =
        maskL.comp (M.mulVecLin.comp maskR) := by
    ext v x
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      LinearMap.comp_apply, maskL, maskR, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hPx : P x
    · simp only [hPx, true_and, ite_true]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hQy : Q y <;> simp [hQy]
    · simp [hPx]
  show Module.finrank ℚ (LinearMap.range (Matrix.of fun x y => if P x ∧ Q y then M x y else 0).mulVecLin) ≤
    Module.finrank ℚ (LinearMap.range M.mulVecLin)
  rw [hcomp, LinearMap.range_comp]
  exact le_trans (Submodule.finrank_map_le maskL _)
    (Submodule.finrank_mono (LinearMap.range_comp_le_range maskR M.mulVecLin))

private lemma L_meta_223_rank_add_le {α : Type} [Fintype α] (A B : Matrix α α ℚ) :
    (A + B).rank ≤ A.rank + B.rank := by
  show Module.finrank ℚ (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank ℚ (LinearMap.range A.mulVecLin) + Module.finrank ℚ (LinearMap.range B.mulVecLin)
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  omega

theorem PEqualNP.Outside.L_meta_223 :
    ∀ (n : ℕ) (f g : (Fin n → Bool) → Bool) (s t : ℕ),
      PEqualNP.MetaComplexity.HasTypedRank n f s →
      PEqualNP.MetaComplexity.HasTypedRank n g t →
      PEqualNP.MetaComplexity.HasTypedRank n (fun x => f x || g x) (s + t) := by
  rintro n f g s t ⟨τ₁, hτ₁, hr₁⟩ ⟨τ₂, hτ₂, hr₂⟩
  let τ : (Fin n → Bool) → (Fin n → Bool) → ℕ := fun x y => if f x = true then τ₁ x y else τ₂ x y
  refine ⟨τ, ?_, ?_⟩
  · intro x y hx hy
    have hfy : f y = false := by cases hf : f y <;> simp_all
    have hgy : g y = false := by cases hg : g y <;> simp_all
    by_cases hfx : f x = true
    · simpa [τ, hfx] using hτ₁ x y hfx hfy
    · have hgx : g x = true := by cases hf : f x <;> simp_all
      simpa [τ, hfx] using hτ₂ x y hgx hgy
  · have hstep : ∀ (i : Fin n) (b : Bool),
        (PEqualNP.MetaComplexity.typedMatrix n (fun x => f x || g x) τ i b).rank ≤
          (PEqualNP.MetaComplexity.typedMatrix n f τ₁ i b).rank +
          (PEqualNP.MetaComplexity.typedMatrix n g τ₂ i b).rank := by
      intro i b
      let M₁ : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
        Matrix.of fun x y =>
          if True ∧ g y = false then PEqualNP.MetaComplexity.typedMatrix n f τ₁ i b x y else 0
      let M₂ : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
        Matrix.of fun x y =>
          if f x = false ∧ f y = false then PEqualNP.MetaComplexity.typedMatrix n g τ₂ i b x y else 0
      have hsplit : PEqualNP.MetaComplexity.typedMatrix n (fun x => f x || g x) τ i b = M₁ + M₂ := by
        ext x y
        simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.add_apply, M₁, M₂, Matrix.of_apply, τ]
        rcases Bool.eq_false_or_eq_true (f x) with hfx | hfx <;>
        rcases Bool.eq_false_or_eq_true (g x) with hgx | hgx <;>
        rcases Bool.eq_false_or_eq_true (f y) with hfy | hfy <;>
        rcases Bool.eq_false_or_eq_true (g y) with hgy | hgy <;>
        simp [hfx, hgx, hfy, hgy]
      rw [hsplit]
      refine le_trans (L_meta_223_rank_add_le M₁ M₂) ?_
      exact Nat.add_le_add
        (L_meta_223_rank_mask_le _ (fun _ => True) (fun y => g y = false))
        (L_meta_223_rank_mask_le _ (fun x => f x = false) (fun y => f y = false))
    calc
      ∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n (fun x => f x || g x) τ i b).rank
        ≤ ∑ i : Fin n, ∑ b : Bool,
            ((PEqualNP.MetaComplexity.typedMatrix n f τ₁ i b).rank +
             (PEqualNP.MetaComplexity.typedMatrix n g τ₂ i b).rank) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hstep i b
      _ = (∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ₁ i b).rank) +
          (∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n g τ₂ i b).rank) := by
          simp [Finset.sum_add_distrib]
      _ ≤ s + t := Nat.add_le_add hr₁ hr₂
