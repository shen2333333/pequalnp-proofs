import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_159 :
    ∀ (k : ℕ) (A : Fin k → Finset (Sym2 (Fin 5))) (B : Fin k → Finset (Finset (Fin 5)))
    (t : Fin k → Fin 5),
    (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).edgeFinset ∧ t i ∈ e) →
    (∀ i, ∀ I ∈ B i, t i ∉ I) →
    (∀ e ∈ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).edgeFinset,
      ∀ I : Finset (Fin 5), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).Adj u w) →
        ∃! i : Fin k, e ∈ A i ∧ I ∈ B i) →
    9 ≤ k := by
  intro k A B t hA hB hcov
  set G := SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4)) with hG
  have hadj : ∀ a b : Fin 5, G.Adj a b ↔ _ := fun a b => SimpleGraph.fromRel_adj _ a b

  have valid : ∀ (a b : Fin 5) (I : Finset (Fin 5)), G.Adj a b →
      (∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) →
      s(a, b) ∈ G.edgeFinset ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w := by
    intro a b I h1 h2
    exact ⟨by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact h1, h2⟩

  have v01_0 := valid 0 1 {0} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v02_0 := valid 0 2 {0} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v03_0 := valid 0 3 {0} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v04_0 := valid 0 4 {0} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v12_1 := valid 1 2 {1} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v12_2 := valid 1 2 {2} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v12_13 := valid 1 2 {1, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v12_14 := valid 1 2 {1, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v12_23 := valid 1 2 {2, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v12_24 := valid 1 2 {2, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v34_3 := valid 3 4 {3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v34_4 := valid 3 4 {4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v34_13 := valid 3 4 {1, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v34_14 := valid 3 4 {1, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v34_23 := valid 3 4 {2, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v34_24 := valid 3 4 {2, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v01_1 := valid 0 1 {1} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v02_2 := valid 0 2 {2} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v03_3 := valid 0 3 {3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v04_4 := valid 0 4 {4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v01_13 := valid 0 1 {1, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v01_14 := valid 0 1 {1, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v02_23 := valid 0 2 {2, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v02_24 := valid 0 2 {2, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v03_13 := valid 0 3 {1, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v03_23 := valid 0 3 {2, 3} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v04_14 := valid 0 4 {1, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)
  have v04_24 := valid 0 4 {2, 4} (by rw [hadj]; decide) (by simp only [hadj]; decide)

  have hne : Nonempty (Fin k) := by
    obtain ⟨i, -⟩ := (hcov _ v01_0.1 _ v01_0.2).exists
    exact ⟨i⟩
  have hcov' : ∀ e ∈ G.edgeFinset, ∀ I : Finset (Fin 5), (∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) →
      ∃ i, (e ∈ A i ∧ I ∈ B i) ∧ ∀ j, (e ∈ A j ∧ I ∈ B j) → j = i := hcov
  choose! σ hσ hσu using hcov'

  have rect : ∀ (e : Sym2 (Fin 5)) (I : Finset (Fin 5)) (e' : Sym2 (Fin 5)) (I' : Finset (Fin 5)),
      (e ∈ G.edgeFinset ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) →
      (e' ∈ G.edgeFinset ∧ ∀ u ∈ I', ∀ w ∈ I', ¬ G.Adj u w) →
      σ e I = σ e' I' → σ e I' = σ e I := by
    intro e I e' I' h h' heq
    refine (hσu e h.1 I' h'.2 (σ e I) ⟨(hσ e h.1 I h.2).1, ?_⟩).symm
    rw [heq]
    exact (hσ e' h'.1 I' h'.2).2

  have sep : ∀ (e : Sym2 (Fin 5)) (J : Finset (Fin 5)) (e' : Sym2 (Fin 5)) (I' : Finset (Fin 5))
      (c : Fin k),
      (e ∈ G.edgeFinset ∧ ∀ u ∈ J, ∀ w ∈ J, ¬ G.Adj u w) →
      (e' ∈ G.edgeFinset ∧ ∀ u ∈ I', ∀ w ∈ I', ¬ G.Adj u w) →
      σ e I' = c → t c ≠ t (σ e J) → σ e J ≠ σ e' I' := by
    intro e J e' I' c hJ hI' hc hne heq
    have h := rect e J e' I' hJ hI' heq
    exact hne (by rw [← hc, h])
  have tmem : ∀ (e : Sym2 (Fin 5)) (I : Finset (Fin 5)),
      (e ∈ G.edgeFinset ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) →
      t (σ e I) ∈ e ∧ t (σ e I) ∉ I := fun e I h =>
    ⟨(hA _ _ (hσ e h.1 I h.2).1).2, hB _ _ (hσ e h.1 I h.2).2⟩
  have tvalL : ∀ (a b : Fin 5) (I : Finset (Fin 5)),
      (s(a, b) ∈ G.edgeFinset ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) → a ∈ I →
      t (σ s(a, b) I) = b := by
    intro a b I h ha
    obtain ⟨h1, h2⟩ := tmem _ _ h
    rw [Sym2.mem_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd (by rw [h1]; exact ha) h2
    · exact h1
  have tvalR : ∀ (a b : Fin 5) (I : Finset (Fin 5)),
      (s(a, b) ∈ G.edgeFinset ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) → b ∈ I →
      t (σ s(a, b) I) = a := by
    intro a b I h hb
    obtain ⟨h1, h2⟩ := tmem _ _ h
    rw [Sym2.mem_iff] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd (by rw [h1]; exact hb) h2

  have t01_0 := tvalL 0 1 {0} v01_0 (by decide)
  have t02_0 := tvalL 0 2 {0} v02_0 (by decide)
  have t03_0 := tvalL 0 3 {0} v03_0 (by decide)
  have t04_0 := tvalL 0 4 {0} v04_0 (by decide)
  have t12_1 := tvalL 1 2 {1} v12_1 (by decide)
  have t12_2 := tvalR 1 2 {2} v12_2 (by decide)
  have t12_13 := tvalL 1 2 {1, 3} v12_13 (by decide)
  have t12_14 := tvalL 1 2 {1, 4} v12_14 (by decide)
  have t12_23 := tvalR 1 2 {2, 3} v12_23 (by decide)
  have t12_24 := tvalR 1 2 {2, 4} v12_24 (by decide)
  have t34_3 := tvalL 3 4 {3} v34_3 (by decide)
  have t34_4 := tvalR 3 4 {4} v34_4 (by decide)
  have t34_13 := tvalL 3 4 {1, 3} v34_13 (by decide)
  have t34_14 := tvalR 3 4 {1, 4} v34_14 (by decide)
  have t34_23 := tvalL 3 4 {2, 3} v34_23 (by decide)
  have t34_24 := tvalR 3 4 {2, 4} v34_24 (by decide)
  have t01_1 := tvalR 0 1 {1} v01_1 (by decide)
  have t02_2 := tvalR 0 2 {2} v02_2 (by decide)
  have t03_3 := tvalR 0 3 {3} v03_3 (by decide)
  have t04_4 := tvalR 0 4 {4} v04_4 (by decide)
  have t01_13 := tvalR 0 1 {1, 3} v01_13 (by decide)
  have t01_14 := tvalR 0 1 {1, 4} v01_14 (by decide)
  have t02_23 := tvalR 0 2 {2, 3} v02_23 (by decide)
  have t02_24 := tvalR 0 2 {2, 4} v02_24 (by decide)
  have t03_13 := tvalR 0 3 {1, 3} v03_13 (by decide)
  have t03_23 := tvalR 0 3 {2, 3} v03_23 (by decide)
  have t04_14 := tvalR 0 4 {1, 4} v04_14 (by decide)
  have t04_24 := tvalR 0 4 {2, 4} v04_24 (by decide)

  have hsum : k = ∑ v : Fin 5, (Finset.univ.filter (fun i => t i = v)).card := by
    have := Finset.card_eq_sum_card_fiberwise (f := t) (s := Finset.univ) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)
    simpa using this
  simp only [Fin.sum_univ_five] at hsum
  have ge1 : ∀ (v : Fin 5) (i : Fin k), t i = v →
      1 ≤ (Finset.univ.filter (fun i => t i = v)).card := fun v i h =>
    Finset.card_pos.mpr ⟨i, by simp [h]⟩
  have ge2 : ∀ (v : Fin 5) (i j : Fin k), t i = v → t j = v → i ≠ j →
      2 ≤ (Finset.univ.filter (fun i => t i = v)).card := fun v i j hi hj hij =>
    Finset.one_lt_card.mpr ⟨i, by simp [hi], j, by simp [hj], hij⟩
  have ge3 : ∀ (v : Fin 5) (i j l : Fin k), t i = v → t j = v → t l = v →
      i ≠ j → i ≠ l → j ≠ l →
      3 ≤ (Finset.univ.filter (fun i => t i = v)).card := fun v i j l hi hj hl hij hil hjl =>
    Finset.two_lt_card.mpr ⟨i, by simp [hi], j, by simp [hj], l, by simp [hl], hij, hil, hjl⟩

  have n0 := ge1 0 _ t01_1
  have n1 := ge1 1 _ t01_0
  have n2 := ge1 2 _ t02_0
  have n3 := ge1 3 _ t03_0
  have n4 := ge1 4 _ t04_0

  have nE1 : ¬ (σ s(1, 2) {2} = σ s(0, 1) {0} ∧ σ s(1, 2) {2, 3} = σ s(0, 1) {0} ∧
      σ s(1, 2) {2, 4} = σ s(0, 1) {0}) → 2 ≤ (Finset.univ.filter (fun i => t i = 1)).card := by
    intro h
    by_contra hlt
    exact h ⟨Classical.byContradiction fun hne => hlt (ge2 1 _ _ t12_2 t01_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 1 _ _ t12_23 t01_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 1 _ _ t12_24 t01_0 hne)⟩
  have nE2 : ¬ (σ s(1, 2) {1} = σ s(0, 2) {0} ∧ σ s(1, 2) {1, 3} = σ s(0, 2) {0} ∧
      σ s(1, 2) {1, 4} = σ s(0, 2) {0}) → 2 ≤ (Finset.univ.filter (fun i => t i = 2)).card := by
    intro h
    by_contra hlt
    exact h ⟨Classical.byContradiction fun hne => hlt (ge2 2 _ _ t12_1 t02_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 2 _ _ t12_13 t02_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 2 _ _ t12_14 t02_0 hne)⟩
  have nE3 : ¬ (σ s(3, 4) {4} = σ s(0, 3) {0} ∧ σ s(3, 4) {1, 4} = σ s(0, 3) {0} ∧
      σ s(3, 4) {2, 4} = σ s(0, 3) {0}) → 2 ≤ (Finset.univ.filter (fun i => t i = 3)).card := by
    intro h
    by_contra hlt
    exact h ⟨Classical.byContradiction fun hne => hlt (ge2 3 _ _ t34_4 t03_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 3 _ _ t34_14 t03_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 3 _ _ t34_24 t03_0 hne)⟩
  have nE4 : ¬ (σ s(3, 4) {3} = σ s(0, 4) {0} ∧ σ s(3, 4) {1, 3} = σ s(0, 4) {0} ∧
      σ s(3, 4) {2, 3} = σ s(0, 4) {0}) → 2 ≤ (Finset.univ.filter (fun i => t i = 4)).card := by
    intro h
    by_contra hlt
    exact h ⟨Classical.byContradiction fun hne => hlt (ge2 4 _ _ t34_3 t04_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 4 _ _ t34_13 t04_0 hne),
      Classical.byContradiction fun hne => hlt (ge2 4 _ _ t34_23 t04_0 hne)⟩

  have E12 : σ s(1, 2) {2} = σ s(0, 1) {0} → σ s(1, 2) {1} = σ s(0, 2) {0} → False := by
    intro e1 e2
    have h1 := rect s(1, 2) {2} s(0, 1) {0} v12_2 v01_0 e1
    have h2 := rect s(1, 2) {1} s(0, 2) {0} v12_1 v02_0 e2
    have h : t (σ s(1, 2) {2}) = t (σ s(1, 2) {1}) := by rw [← h1, h2]
    rw [t12_2, t12_1] at h
    exact absurd h (by decide)
  have E34 : σ s(3, 4) {4} = σ s(0, 3) {0} → σ s(3, 4) {3} = σ s(0, 4) {0} → False := by
    intro e3 e4
    have h1 := rect s(3, 4) {4} s(0, 3) {0} v34_4 v03_0 e3
    have h2 := rect s(3, 4) {3} s(0, 4) {0} v34_3 v04_0 e4
    have h : t (σ s(3, 4) {4}) = t (σ s(3, 4) {3}) := by rw [← h1, h2]
    rw [t34_4, t34_3] at h
    exact absurd h (by decide)

  have E1_0 : σ s(1, 2) {2} = σ s(0, 1) {0} →
      2 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e1
    apply ge2 0 _ _ t01_1 t02_2
    exact sep s(0, 1) {1} s(0, 2) {2} _ v01_1 v02_2
      (rect s(0, 1) {0} s(1, 2) {2} v01_0 v12_2 e1.symm) (by rw [t01_0, t01_1]; decide)
  have E2_0 : σ s(1, 2) {1} = σ s(0, 2) {0} →
      2 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e2
    apply ge2 0 _ _ t02_2 t01_1
    exact sep s(0, 2) {2} s(0, 1) {1} _ v02_2 v01_1
      (rect s(0, 2) {0} s(1, 2) {1} v02_0 v12_1 e2.symm) (by rw [t02_0, t02_2]; decide)
  have E3_0 : σ s(3, 4) {4} = σ s(0, 3) {0} →
      2 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e3
    apply ge2 0 _ _ t03_3 t04_4
    exact sep s(0, 3) {3} s(0, 4) {4} _ v03_3 v04_4
      (rect s(0, 3) {0} s(3, 4) {4} v03_0 v34_4 e3.symm) (by rw [t03_0, t03_3]; decide)
  have E4_0 : σ s(3, 4) {3} = σ s(0, 4) {0} →
      2 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e4
    apply ge2 0 _ _ t04_4 t03_3
    exact sep s(0, 4) {4} s(0, 3) {3} _ v04_4 v03_3
      (rect s(0, 4) {0} s(3, 4) {3} v04_0 v34_3 e4.symm) (by rw [t04_0, t04_4]; decide)

  have E13 : σ s(1, 2) {2, 3} = σ s(0, 1) {0} → σ s(1, 2) {2, 4} = σ s(0, 1) {0} →
      σ s(3, 4) {2, 4} = σ s(0, 3) {0} →
      3 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e1a e1b e3
    apply ge3 0 _ _ _ t01_14 t02_24 t03_23
    · exact sep s(0, 1) {1, 4} s(0, 2) {2, 4} _ v01_14 v02_24
        (rect s(0, 1) {0} s(1, 2) {2, 4} v01_0 v12_24 e1b.symm) (by rw [t01_0, t01_14]; decide)
    · exact sep s(0, 1) {1, 4} s(0, 3) {2, 3} _ v01_14 v03_23
        (rect s(0, 1) {0} s(1, 2) {2, 3} v01_0 v12_23 e1a.symm) (by rw [t01_0, t01_14]; decide)
    · exact (sep s(0, 3) {2, 3} s(0, 2) {2, 4} _ v03_23 v02_24
        (rect s(0, 3) {0} s(3, 4) {2, 4} v03_0 v34_24 e3.symm)
        (by rw [t03_0, t03_23]; decide)).symm
  have E14 : σ s(1, 2) {2, 3} = σ s(0, 1) {0} → σ s(1, 2) {2, 4} = σ s(0, 1) {0} →
      σ s(3, 4) {2, 3} = σ s(0, 4) {0} →
      3 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e1a e1b e4
    apply ge3 0 _ _ _ t01_13 t02_23 t04_24
    · exact sep s(0, 1) {1, 3} s(0, 2) {2, 3} _ v01_13 v02_23
        (rect s(0, 1) {0} s(1, 2) {2, 3} v01_0 v12_23 e1a.symm) (by rw [t01_0, t01_13]; decide)
    · exact sep s(0, 1) {1, 3} s(0, 4) {2, 4} _ v01_13 v04_24
        (rect s(0, 1) {0} s(1, 2) {2, 4} v01_0 v12_24 e1b.symm) (by rw [t01_0, t01_13]; decide)
    · exact (sep s(0, 4) {2, 4} s(0, 2) {2, 3} _ v04_24 v02_23
        (rect s(0, 4) {0} s(3, 4) {2, 3} v04_0 v34_23 e4.symm)
        (by rw [t04_0, t04_24]; decide)).symm
  have E23 : σ s(1, 2) {1, 4} = σ s(0, 2) {0} →
      σ s(3, 4) {1, 4} = σ s(0, 3) {0} → σ s(3, 4) {2, 4} = σ s(0, 3) {0} →
      3 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e2 e3a e3b
    apply ge3 0 _ _ _ t01_14 t02_24 t03_13
    · exact (sep s(0, 2) {2, 4} s(0, 1) {1, 4} _ v02_24 v01_14
        (rect s(0, 2) {0} s(1, 2) {1, 4} v02_0 v12_14 e2.symm)
        (by rw [t02_0, t02_24]; decide)).symm
    · exact (sep s(0, 3) {1, 3} s(0, 1) {1, 4} _ v03_13 v01_14
        (rect s(0, 3) {0} s(3, 4) {1, 4} v03_0 v34_14 e3a.symm)
        (by rw [t03_0, t03_13]; decide)).symm
    · exact (sep s(0, 3) {1, 3} s(0, 2) {2, 4} _ v03_13 v02_24
        (rect s(0, 3) {0} s(3, 4) {2, 4} v03_0 v34_24 e3b.symm)
        (by rw [t03_0, t03_13]; decide)).symm
  have E24 : σ s(1, 2) {1, 3} = σ s(0, 2) {0} →
      σ s(3, 4) {1, 3} = σ s(0, 4) {0} → σ s(3, 4) {2, 3} = σ s(0, 4) {0} →
      3 ≤ (Finset.univ.filter (fun i => t i = 0)).card := by
    intro e2 e4a e4b
    apply ge3 0 _ _ _ t01_13 t02_23 t04_14
    · exact (sep s(0, 2) {2, 3} s(0, 1) {1, 3} _ v02_23 v01_13
        (rect s(0, 2) {0} s(1, 2) {1, 3} v02_0 v12_13 e2.symm)
        (by rw [t02_0, t02_23]; decide)).symm
    · exact (sep s(0, 4) {1, 4} s(0, 1) {1, 3} _ v04_14 v01_13
        (rect s(0, 4) {0} s(3, 4) {1, 3} v04_0 v34_13 e4a.symm)
        (by rw [t04_0, t04_14]; decide)).symm
    · exact (sep s(0, 4) {1, 4} s(0, 2) {2, 3} _ v04_14 v02_23
        (rect s(0, 4) {0} s(3, 4) {2, 3} v04_0 v34_23 e4b.symm)
        (by rw [t04_0, t04_14]; decide)).symm

  rw [hsum]
  by_cases e1 : σ s(1, 2) {2} = σ s(0, 1) {0} ∧ σ s(1, 2) {2, 3} = σ s(0, 1) {0} ∧
      σ s(1, 2) {2, 4} = σ s(0, 1) {0}
  · have h0 := E1_0 e1.1
    by_cases e3 : σ s(3, 4) {4} = σ s(0, 3) {0} ∧ σ s(3, 4) {1, 4} = σ s(0, 3) {0} ∧
        σ s(3, 4) {2, 4} = σ s(0, 3) {0}
    · have h0' := E13 e1.2.1 e1.2.2 e3.2.2
      have h2 := nE2 (fun e2 => E12 e1.1 e2.1)
      have h4 := nE4 (fun e4 => E34 e3.1 e4.1)
      omega
    · have h3 := nE3 e3
      have h2 := nE2 (fun e2 => E12 e1.1 e2.1)
      by_cases e4 : σ s(3, 4) {3} = σ s(0, 4) {0} ∧ σ s(3, 4) {1, 3} = σ s(0, 4) {0} ∧
          σ s(3, 4) {2, 3} = σ s(0, 4) {0}
      · have h0' := E14 e1.2.1 e1.2.2 e4.2.2
        omega
      · have h4 := nE4 e4
        omega
  · have h1 := nE1 e1
    by_cases e2 : σ s(1, 2) {1} = σ s(0, 2) {0} ∧ σ s(1, 2) {1, 3} = σ s(0, 2) {0} ∧
        σ s(1, 2) {1, 4} = σ s(0, 2) {0}
    · have h0 := E2_0 e2.1
      by_cases e3 : σ s(3, 4) {4} = σ s(0, 3) {0} ∧ σ s(3, 4) {1, 4} = σ s(0, 3) {0} ∧
          σ s(3, 4) {2, 4} = σ s(0, 3) {0}
      · have h0' := E23 e2.2.2 e3.2.1 e3.2.2
        have h4 := nE4 (fun e4 => E34 e3.1 e4.1)
        omega
      · have h3 := nE3 e3
        by_cases e4 : σ s(3, 4) {3} = σ s(0, 4) {0} ∧ σ s(3, 4) {1, 3} = σ s(0, 4) {0} ∧
            σ s(3, 4) {2, 3} = σ s(0, 4) {0}
        · have h0' := E24 e2.2.1 e4.2.1 e4.2.2
          omega
        · have h4 := nE4 e4
          omega
    · have h2 := nE2 e2
      by_cases e3 : σ s(3, 4) {4} = σ s(0, 3) {0} ∧ σ s(3, 4) {1, 4} = σ s(0, 3) {0} ∧
          σ s(3, 4) {2, 4} = σ s(0, 3) {0}
      · have h0 := E3_0 e3.1
        have h4 := nE4 (fun e4 => E34 e3.1 e4.1)
        omega
      · have h3 := nE3 e3
        by_cases e4 : σ s(3, 4) {3} = σ s(0, 4) {0} ∧ σ s(3, 4) {1, 3} = σ s(0, 4) {0} ∧
            σ s(3, 4) {2, 3} = σ s(0, 4) {0}
        · have h0 := E4_0 e4.1
          omega
        · have h4 := nE4 e4
          omega
