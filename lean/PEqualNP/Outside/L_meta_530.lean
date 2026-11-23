import PEqualNP.Defs

open PEqualNP.MetaComplexity

private def rect530Cover {n k : ℕ} (X Y : Finset (Fin n → Bool))
    (A B : Fin k → Finset (Fin n → Bool)) (t : Fin k → Fin n) : Prop :=
  (∀ i : Fin k, ∀ x ∈ A i, x (t i) = true) ∧
  (∀ i : Fin k, ∀ y ∈ B i, y (t i) = false) ∧
  ∀ x ∈ X, ∀ y ∈ Y, ∃! i : Fin k, x ∈ A i ∧ y ∈ B i

private lemma rect530Glue {n k₁ k₂ : ℕ}
    {X Y X₁ Y₁ X₂ Y₂ : Finset (Fin n → Bool)}
    {A₁ B₁ : Fin k₁ → Finset (Fin n → Bool)} {t₁ : Fin k₁ → Fin n}
    {A₂ B₂ : Fin k₂ → Finset (Fin n → Bool)} {t₂ : Fin k₂ → Fin n}
    (h₁ : rect530Cover X₁ Y₁ A₁ B₁ t₁) (h₂ : rect530Cover X₂ Y₂ A₂ B₂ t₂)
    (split : ∀ x ∈ X, ∀ y ∈ Y,
      ((x ∈ X₁ ∧ y ∈ Y₁) ∧ ¬ (x ∈ X₂ ∧ y ∈ Y₂)) ∨
      ((x ∈ X₂ ∧ y ∈ Y₂) ∧ ¬ (x ∈ X₁ ∧ y ∈ Y₁))) :
    ∃ A B : Fin (k₁ + k₂) → Finset (Fin n → Bool),
      ∃ t : Fin (k₁ + k₂) → Fin n, rect530Cover X Y A B t := by
  classical
  let e : Fin k₁ ⊕ Fin k₂ ≃ Fin (k₁ + k₂) := finSumFinEquiv
  let a : Fin k₁ ⊕ Fin k₂ → Finset (Fin n → Bool) :=
    Sum.elim (fun i => A₁ i ∩ X₁) (fun i => A₂ i ∩ X₂)
  let b : Fin k₁ ⊕ Fin k₂ → Finset (Fin n → Bool) :=
    Sum.elim (fun i => B₁ i ∩ Y₁) (fun i => B₂ i ∩ Y₂)
  let label : Fin k₁ ⊕ Fin k₂ → Fin n := Sum.elim t₁ t₂
  refine ⟨a ∘ e.symm, b ∘ e.symm, label ∘ e.symm, ?_, ?_, ?_⟩
  · intro i x hx
    change x ∈ a (e.symm i) at hx
    change x (label (e.symm i)) = true
    cases h : e.symm i with
    | inl j => exact h₁.1 j x (Finset.mem_inter.mp (h ▸ hx)).1
    | inr j => exact h₂.1 j x (Finset.mem_inter.mp (h ▸ hx)).1
  · intro i y hy
    change y ∈ b (e.symm i) at hy
    change y (label (e.symm i)) = false
    cases h : e.symm i with
    | inl j => exact h₁.2.1 j y (Finset.mem_inter.mp (h ▸ hy)).1
    | inr j => exact h₂.2.1 j y (Finset.mem_inter.mp (h ▸ hy)).1
  · intro x hx y hy
    apply (e.existsUnique_congr_right).mp
    change ∃! i : Fin k₁ ⊕ Fin k₂, x ∈ a (e.symm (e i)) ∧ y ∈ b (e.symm (e i))
    simp only [Equiv.symm_apply_apply]
    rcases split x hx y hy with ⟨⟨hx₁, hy₁⟩, not₂⟩ | ⟨⟨hx₂, hy₂⟩, not₁⟩
    · obtain ⟨i, hi, uniq⟩ := h₁.2.2 x hx₁ y hy₁
      refine ⟨Sum.inl i, ⟨Finset.mem_inter.mpr ⟨hi.1, hx₁⟩,
        Finset.mem_inter.mpr ⟨hi.2, hy₁⟩⟩, ?_⟩
      intro j hj
      cases j with
      | inl j => exact congrArg Sum.inl (uniq j ⟨(Finset.mem_inter.mp hj.1).1,
          (Finset.mem_inter.mp hj.2).1⟩)
      | inr j => exact (not₂ ⟨(Finset.mem_inter.mp hj.1).2,
          (Finset.mem_inter.mp hj.2).2⟩).elim
    · obtain ⟨i, hi, uniq⟩ := h₂.2.2 x hx₂ y hy₂
      refine ⟨Sum.inr i, ⟨Finset.mem_inter.mpr ⟨hi.1, hx₂⟩,
        Finset.mem_inter.mpr ⟨hi.2, hy₂⟩⟩, ?_⟩
      intro j hj
      cases j with
      | inl j => exact (not₁ ⟨(Finset.mem_inter.mp hj.1).2,
          (Finset.mem_inter.mp hj.2).2⟩).elim
      | inr j => exact congrArg Sum.inr (uniq j ⟨(Finset.mem_inter.mp hj.1).1,
          (Finset.mem_inter.mp hj.2).1⟩)

theorem PEqualNP.Outside.L_meta_530 :
    ∀ (n : ℕ) (φ : PEqualNP.MetaComplexity.DMFormula n), PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ → ∀ (X Y : Finset (Fin n → Bool)), (∀ x ∈ X, φ.eval x = true) → (∀ y ∈ Y, φ.eval y = false) → ∃ (k : ℕ) (A B : Fin k → Finset (Fin n → Bool)) (t : Fin k → Fin n), k ≤ φ.leaves ∧ (∀ i : Fin k, ∀ x ∈ A i, x (t i) = true) ∧ (∀ i : Fin k, ∀ y ∈ B i, y (t i) = false) ∧ ∀ x ∈ X, ∀ y ∈ Y, ∃! i : Fin k, x ∈ A i ∧ y ∈ B i := by
  classical
  intro n φ
  induction φ with
  | lit i c =>
    intro hc X Y hX hY
    change c = true at hc
    subst c
    refine ⟨1, fun _ => X, fun _ => Y, fun _ => i, le_rfl, ?_, ?_, ?_⟩
    · intro _ x hx
      simpa [DMFormula.eval] using hX x hx
    · intro _ y hy
      simpa [DMFormula.eval] using hY y hy
    · intro x hx y hy
      exact ⟨0, ⟨hx, hy⟩, fun _ _ => Subsingleton.elim _ _⟩
  | and l r il ir =>
    intro h X Y hX hY
    let Y₁ := Y.filter (fun y => l.eval y = false)
    let Y₂ := Y.filter (fun y => l.eval y = true)
    have leftTrue (x) (hx : x ∈ X) : l.eval x = true := by
      have hx' := hX x hx
      simp [DMFormula.eval] at hx'
      exact hx'.1
    have rightTrue (x) (hx : x ∈ X) : r.eval x = true := by
      have hx' := hX x hx
      simp [DMFormula.eval] at hx'
      exact hx'.2
    have rightFalse (y) (hy : y ∈ Y₂) : r.eval y = false := by
      obtain ⟨hy, hl⟩ := Finset.mem_filter.mp hy
      simpa [DMFormula.eval, hl] using hY y hy
    obtain ⟨k₁, A₁, B₁, t₁, hk₁, h₁⟩ := il h.1 X Y₁ leftTrue
      (fun _ hy => (Finset.mem_filter.mp hy).2)
    obtain ⟨k₂, A₂, B₂, t₂, hk₂, h₂⟩ := ir h.2 X Y₂ rightTrue rightFalse
    obtain ⟨A, B, t, cover⟩ := rect530Glue (X := X) (Y := Y) h₁ h₂ (by
      intro x hx y hy
      cases hleft : l.eval y <;> simp [Y₁, Y₂, hx, hy, hleft])
    exact ⟨k₁ + k₂, A, B, t, Nat.add_le_add hk₁ hk₂, cover⟩
  | or l r il ir =>
    intro h X Y hX hY
    let X₁ := X.filter (fun x => l.eval x = true)
    let X₂ := X.filter (fun x => l.eval x = false)
    have rightTrue (x) (hx : x ∈ X₂) : r.eval x = true := by
      obtain ⟨hx, hl⟩ := Finset.mem_filter.mp hx
      simpa [DMFormula.eval, hl] using hX x hx
    have leftFalse (y) (hy : y ∈ Y) : l.eval y = false := by
      have hy' := hY y hy
      simp [DMFormula.eval] at hy'
      exact hy'.1
    have rightFalse (y) (hy : y ∈ Y) : r.eval y = false := by
      have hy' := hY y hy
      simp [DMFormula.eval] at hy'
      exact hy'.2
    obtain ⟨k₁, A₁, B₁, t₁, hk₁, h₁⟩ := il h.1 X₁ Y
      (fun _ hx => (Finset.mem_filter.mp hx).2) leftFalse
    obtain ⟨k₂, A₂, B₂, t₂, hk₂, h₂⟩ := ir h.2 X₂ Y rightTrue rightFalse
    obtain ⟨A, B, t, cover⟩ := rect530Glue (X := X) (Y := Y) h₁ h₂ (by
      intro x hx y hy
      cases hleft : l.eval x <;> simp [X₁, X₂, hx, hy, hleft])
    exact ⟨k₁ + k₂, A, B, t, Nat.add_le_add hk₁ hk₂, cover⟩
