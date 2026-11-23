import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_459 : ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] → ∀ τ : Fin 5 × Fin 5 → Finset (Fin 5) → Fin 5, (∀ e ∈ E, ∀ I : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 5 × Fin 5 → ℚ, (∀ I : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 5, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hsum e he
  subst E
  have hI (i : Fin 5) :
      ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5)),
        ¬ (f.1 ∈ ({i} : Finset (Fin 5)) ∧ f.2 ∈ ({i} : Finset (Fin 5))) := by
    fin_cases i <;> decide
  have hchoice (i a b : Fin 5)
      (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5))) :
      τ (a, b) {i} = a ∨ τ (a, b) {i} = b :=
    (hτ (a, b) hab {i} (hI i)).1
  have hnot (i a b : Fin 5)
      (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5))) :
      τ (a, b) {i} ≠ i := by
    simpa using (hτ (a, b) hab {i} (hI i)).2
  have hleft (i b : Fin 5)
      (hab : (i, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5))) :
      τ (i, b) {i} = b := by
    rcases hchoice i i b hab with h | h
    · exact (hnot i i b hab h).elim
    · exact h
  have hright (i a : Fin 5)
      (hab : (a, i) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5))) :
      τ (a, i) {i} = a := by
    rcases hchoice i a i hab with h | h
    · exact h
    · exact (hnot i a i hab h).elim
  have haway (i a b v : Fin 5)
      (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5)))
      (hav : a ≠ v) (hbv : b ≠ v) : τ (a, b) {i} ≠ v := by
    rcases hchoice i a b hab with h | h
    · simpa [h] using hav
    · simpa [h] using hbv
  have h01_0 : τ (0, 1) {0} = 1 := hleft 0 1 (by decide)
  have h02_0 : τ (0, 2) {0} = 2 := hleft 0 2 (by decide)
  have h03_0 : τ (0, 3) {0} = 3 := hleft 0 3 (by decide)
  have h04_0 : τ (0, 4) {0} = 4 := hleft 0 4 (by decide)
  have h34_0_ne1 : τ (3, 4) {0} ≠ 1 := haway 0 3 4 1 (by decide) (by decide) (by decide)
  have h34_0_ne2 : τ (3, 4) {0} ≠ 2 := haway 0 3 4 2 (by decide) (by decide) (by decide)
  have h12_0_ne3 : τ (1, 2) {0} ≠ 3 := haway 0 1 2 3 (by decide) (by decide) (by decide)
  have h12_0_ne4 : τ (1, 2) {0} ≠ 4 := haway 0 1 2 4 (by decide) (by decide) (by decide)
  have h01_1 : τ (0, 1) {1} = 0 := hright 1 0 (by decide)
  have h12_1 : τ (1, 2) {1} = 2 := hleft 1 2 (by decide)
  have h03_1_ne2 : τ (0, 3) {1} ≠ 2 := haway 1 0 3 2 (by decide) (by decide) (by decide)
  have h04_1_ne2 : τ (0, 4) {1} ≠ 2 := haway 1 0 4 2 (by decide) (by decide) (by decide)
  have h34_1_ne2 : τ (3, 4) {1} ≠ 2 := haway 1 3 4 2 (by decide) (by decide) (by decide)
  have h02_2 : τ (0, 2) {2} = 0 := hright 2 0 (by decide)
  have h12_2 : τ (1, 2) {2} = 1 := hright 2 1 (by decide)
  have h03_2_ne1 : τ (0, 3) {2} ≠ 1 := haway 2 0 3 1 (by decide) (by decide) (by decide)
  have h04_2_ne1 : τ (0, 4) {2} ≠ 1 := haway 2 0 4 1 (by decide) (by decide) (by decide)
  have h34_2_ne1 : τ (3, 4) {2} ≠ 1 := haway 2 3 4 1 (by decide) (by decide) (by decide)
  have h01_3_ne4 : τ (0, 1) {3} ≠ 4 := haway 3 0 1 4 (by decide) (by decide) (by decide)
  have h02_3_ne4 : τ (0, 2) {3} ≠ 4 := haway 3 0 2 4 (by decide) (by decide) (by decide)
  have h12_3_ne4 : τ (1, 2) {3} ≠ 4 := haway 3 1 2 4 (by decide) (by decide) (by decide)
  have h03_3 : τ (0, 3) {3} = 0 := hright 3 0 (by decide)
  have h34_3 : τ (3, 4) {3} = 4 := hleft 3 4 (by decide)
  have h01_4_ne3 : τ (0, 1) {4} ≠ 3 := haway 4 0 1 3 (by decide) (by decide) (by decide)
  have h02_4_ne3 : τ (0, 2) {4} ≠ 3 := haway 4 0 2 3 (by decide) (by decide) (by decide)
  have h12_4_ne3 : τ (1, 2) {4} ≠ 3 := haway 4 1 2 3 (by decide) (by decide) (by decide)
  have h04_4 : τ (0, 4) {4} = 0 := hright 4 0 (by decide)
  have h34_4 : τ (3, 4) {4} = 3 := hright 4 3 (by decide)
  have hfirst : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
    rcases hchoice 0 1 2 (by decide) with h12_0 | h12_0
    · have ha := hsum {0} (hI 0) 1
      have hb := hsum {0} (hI 0) 2
      rcases hchoice 1 0 2 (by decide) with h02_1 | h02_1
      · have hc := hsum {1} (hI 1) 2
        simp [h01_0, h02_0, h03_0, h04_0, h12_0, h34_0_ne1, h34_0_ne2,
          h01_1, h02_1, h12_1, h03_1_ne2, h04_1_ne2, h34_1_ne2] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {1} (hI 1) 2
        simp [h01_0, h02_0, h03_0, h04_0, h12_0, h34_0_ne1, h34_0_ne2,
          h01_1, h02_1, h12_1, h03_1_ne2, h04_1_ne2, h34_1_ne2] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
    · have ha := hsum {0} (hI 0) 1
      have hb := hsum {0} (hI 0) 2
      rcases hchoice 2 0 1 (by decide) with h01_2 | h01_2
      · have hc := hsum {2} (hI 2) 1
        simp [h01_0, h02_0, h03_0, h04_0, h12_0, h34_0_ne1, h34_0_ne2,
          h01_2, h02_2, h12_2, h03_2_ne1, h04_2_ne1, h34_2_ne1] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {2} (hI 2) 1
        simp [h01_0, h02_0, h03_0, h04_0, h12_0, h34_0_ne1, h34_0_ne2,
          h01_2, h02_2, h12_2, h03_2_ne1, h04_2_ne1, h34_2_ne1] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
  have hsecond : c (0, 3) = 0 ∧ c (0, 4) = 0 ∧ c (3, 4) = 0 := by
    rcases hchoice 0 3 4 (by decide) with h34_0 | h34_0
    · have ha := hsum {0} (hI 0) 3
      have hb := hsum {0} (hI 0) 4
      rcases hchoice 3 0 4 (by decide) with h04_3 | h04_3
      · have hc := hsum {3} (hI 3) 4
        simp [h01_0, h02_0, h03_0, h04_0, h34_0, h12_0_ne3, h12_0_ne4,
          h01_3_ne4, h02_3_ne4, h12_3_ne4, h03_3, h04_3, h34_3] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {3} (hI 3) 4
        simp [h01_0, h02_0, h03_0, h04_0, h34_0, h12_0_ne3, h12_0_ne4,
          h01_3_ne4, h02_3_ne4, h12_3_ne4, h03_3, h04_3, h34_3] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
    · have ha := hsum {0} (hI 0) 3
      have hb := hsum {0} (hI 0) 4
      rcases hchoice 4 0 3 (by decide) with h03_4 | h03_4
      · have hc := hsum {4} (hI 4) 3
        simp [h01_0, h02_0, h03_0, h04_0, h34_0, h12_0_ne3, h12_0_ne4,
          h01_4_ne3, h02_4_ne3, h12_4_ne3, h03_4, h04_4, h34_4] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {4} (hI 4) 3
        simp [h01_0, h02_0, h03_0, h04_0, h34_0, h12_0_ne3, h12_0_ne4,
          h01_4_ne3, h02_4_ne3, h12_4_ne3, h03_4, h04_4, h34_4] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with h | h | h | h | h | h <;> subst e <;>
    simp only [hfirst.1, hfirst.2.1, hfirst.2.2, hsecond.1, hsecond.2.1, hsecond.2.2]
