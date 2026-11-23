import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_494_aux

open PEqualNP.Search

/-- A literal's code has at least four bits: the polarity pair and the end-of-literal pair. -/
theorem literal_length (l : Literal) : 4 ≤ (encodeLiteral l).length := by
  simp [encodeLiteral]

/-- A clause's code has at least four bits per literal plus the two-bit end-of-clause pair. -/
theorem clause_length (c : Clause) : 4 * c.length + 2 ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [encodeClause]
  | cons l c ih =>
    have hl := literal_length l
    simp only [encodeClause, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- A formula's code has at least four bits per literal and two per clause. -/
theorem cnf_length (φ : CNF) :
    4 * (φ.map List.length).sum + 2 * φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
    have hc := clause_length c
    simp only [encodeCNF, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- Twice the item count (literals plus one end marker per clause) is at most the bound above. -/
theorem items_le (φ : CNF) :
    2 * (φ.map (fun c => c.length + 1)).sum ≤ 4 * (φ.map List.length).sum + 2 * φ.length := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

end PEqualNP.Outside.L_meta_494_aux

theorem PEqualNP.Outside.L_meta_494 : ∀ φ : PEqualNP.Search.CNF, 4 * (φ.map List.length).sum + 2 * φ.length ≤ (PEqualNP.Search.encodeCNF φ).length ∧ 2 * (φ.map (fun c => c.length + 1)).sum ≤ (PEqualNP.Search.encodeCNF φ).length := by
  intro φ
  have h₁ := PEqualNP.Outside.L_meta_494_aux.cnf_length φ
  have h₂ := PEqualNP.Outside.L_meta_494_aux.items_le φ
  exact ⟨h₁, le_trans h₂ h₁⟩
