import Mathlib.Data.List.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_501 : ∀ φ : PEqualNP.Search.CNF, ((fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map List.length = φ.map List.length ∧ ∀ c ∈ (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ, ∀ l ∈ c, l.1 < (((fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) φ).map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum := by
  classical
  intro φ
  let seq : List (Option PEqualNP.Search.Literal) :=
    φ.flatMap (fun c : PEqualNP.Search.Clause => c.map some ++ [none])
  let ren : PEqualNP.Search.CNF :=
    φ.map (fun c : PEqualNP.Search.Clause =>
      c.map (fun l : PEqualNP.Search.Literal =>
        (seq.findIdx (fun o : Option PEqualNP.Search.Literal =>
          o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))
  have hlength (ψ : PEqualNP.Search.CNF) :
      (ψ.flatMap (fun c : PEqualNP.Search.Clause => c.map some ++ [none])).length =
      (ψ.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum := by
    induction ψ with
    | nil => simp
    | cons c cs ih =>
      simp only [List.flatMap_cons, List.map_cons, List.length_append,
        List.length_map, List.length_cons, List.length_nil, List.sum_cons, ih]
  have hseqLen : seq.length = (φ.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum := by
    simpa [seq] using hlength φ
  have hrenLen : (ren.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum =
      (φ.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum := by
    simp [ren, List.map_map, Function.comp_def]
  change ren.map List.length = φ.map List.length ∧
    ∀ c ∈ ren, ∀ l ∈ c, l.1 <
      (ren.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum
  constructor
  · simp [ren]
  · intro c hc l hl
    rcases List.mem_map.mp hc with ⟨orig, horig, hceq⟩
    subst c
    rcases List.mem_map.mp hl with ⟨lit, hlit, hleq⟩
    subst l
    have hmemSeq : some lit ∈ seq := by
      dsimp [seq]
      apply List.mem_flatMap.mpr
      refine ⟨orig, horig, ?_⟩
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨lit, hlit, rfl⟩))
    have hidx : seq.findIdx (fun o : Option PEqualNP.Search.Literal =>
        o.any (fun l' : PEqualNP.Search.Literal => l'.1 == lit.1)) < seq.length := by
      exact List.findIdx_lt_length_of_exists ⟨some lit, hmemSeq, by simp⟩
    change seq.findIdx (fun o : Option PEqualNP.Search.Literal =>
      o.any (fun l' : PEqualNP.Search.Literal => l'.1 == lit.1)) <
        (ren.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum
    exact lt_of_lt_of_eq hidx (hseqLen.trans hrenLen.symm)
