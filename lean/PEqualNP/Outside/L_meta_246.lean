import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_246 :
    ∀ C : Circuit,
      C = ⟨[⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.and, [10, 11]⟩], 12⟩ →
      FanInTwo C ∧ C.size = 7 ∧
      circuitFun 6 C = (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 4 && x 5)) ∧
      C.gates.zipIdx.countP (fun p => decide (7 < 6 + p.2) &&
        (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs
          (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains 7) = 2 := by
  rintro C rfl
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply funext
    decide
  · decide
