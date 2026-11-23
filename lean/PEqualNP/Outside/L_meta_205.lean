import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_205 :
    ∀ (n : ℕ) (c : Bool), PEqualNP.MetaComplexity.HasTypedRank n (fun _ => c) 0 := by
  intro n c
  refine ⟨fun _ _ => 0, ?_, ?_⟩
  · intro x y hx hy
    cases c <;> simp at hx hy
  · have hzero : ∀ (i : Fin n) (b : Bool),
        PEqualNP.MetaComplexity.typedMatrix n (fun _ => c) (fun _ _ => 0) i b = 0 := by
      intro i b
      ext x y
      cases c <;> simp [PEqualNP.MetaComplexity.typedMatrix]
    simp [hzero]
