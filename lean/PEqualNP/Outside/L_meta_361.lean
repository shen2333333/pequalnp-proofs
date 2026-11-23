import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_361 : ∀ (β : Type) (e : β → List Bool) (f : List Bool → β), PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x => e (f x)) → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) e f := by
  rintro β e f ⟨c⟩
  exact ⟨⟨c.toTM2ComputableAux, c.time, c.outputsFun⟩⟩
