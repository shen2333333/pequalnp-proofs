import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PEqualNP.Outside

open PEqualNP.MetaComplexity

private lemma hasTypedRank_not (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasTypedRank n f s) : HasTypedRank n (fun x => !f x) s := by
  rcases h with ⟨τ, hτ, hsum⟩
  refine ⟨fun x y => τ y x, ?_, ?_⟩
  · intro x y hx hy
    have hfy : f y = true := by cases hf : f y <;> simp [hf] at hy ⊢
    have hfx : f x = false := by cases hf : f x <;> simp [hf] at hx ⊢
    rcases hτ y x hfy hfx with ⟨i, hi, hne⟩
    exact ⟨i, hi, hne.symm⟩
  · have hmat : ∀ (i : Fin n) (b : Bool),
        typedMatrix n (fun x => !f x) (fun x y => τ y x) i b =
          (typedMatrix n f τ i (!b)).transpose := by
      intro i b
      ext x y
      simp only [typedMatrix, Matrix.transpose_apply]
      have hiff :
          ((!f x) = true ∧ (!f y) = false ∧ τ y x = (i : ℕ) ∧ x i = b) ↔
            (f y = true ∧ f x = false ∧ τ y x = (i : ℕ) ∧ y i = !b) := by
        constructor
        · rintro ⟨hx, hy, hty, hxi⟩
          have hfy : f y = true := by cases hf : f y <;> simp [hf] at hy ⊢
          have hfx : f x = false := by cases hf : f x <;> simp [hf] at hx ⊢
          rcases hτ y x hfy hfx with ⟨j, hj, hne⟩
          have hij : j = i := Fin.ext (hj.symm.trans hty)
          subst hij
          have hyi : y j = !b := by
            cases hb : b <;> cases hyj : y j <;> simp_all
          exact ⟨hfy, hfx, hty, hyi⟩
        · rintro ⟨hfy, hfx, hty, hyi⟩
          rcases hτ y x hfy hfx with ⟨j, hj, hne⟩
          have hij : j = i := Fin.ext (hj.symm.trans hty)
          subst hij
          have hxi : x j = b := by
            cases hb : b <;> cases hxj : x j <;> simp_all
          exact ⟨by simp [hfx], by simp [hfy], hty, hxi⟩
      by_cases h1 : (!f x) = true ∧ (!f y) = false ∧ τ y x = (i : ℕ) ∧ x i = b
      · rw [if_pos h1, if_pos (hiff.mp h1)]
      · rw [if_neg h1, if_neg (mt hiff.mpr h1)]
    have heq :
        (∑ i : Fin n, ∑ b : Bool, (typedMatrix n (fun x => !f x) (fun x y => τ y x) i b).rank) =
          ∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τ i b).rank := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hmat, Matrix.rank_transpose, Fintype.sum_bool, Bool.not_true, Bool.not_false]
      omega
    rw [heq]
    exact hsum

theorem L_meta_225 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasTypedRank n f s ↔
        PEqualNP.MetaComplexity.HasTypedRank n (fun x => !f x) s := by
  intro n f s
  constructor
  · exact hasTypedRank_not n f s
  · intro h
    have h2 := hasTypedRank_not n (fun x => !f x) s h
    have hfun : (fun x : Fin n → Bool => !(!f x)) = f := by
      funext x
      simp
    rwa [hfun] at h2

end PEqualNP.Outside
