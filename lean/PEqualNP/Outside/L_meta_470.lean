import Mathlib
import PEqualNP.Defs

private theorem L470_aux (c : ℕ → Bool) : ∀ (m s : ℕ),
    (∀ i, i < m → c (s + 2 * i) = true ∨ c (s + 2 * i + 1) = true) →
    m ≤ ∑ j ∈ Finset.Ico s (s + 2 * m), (if c j = true then 1 else 0) := by
  intro m
  induction m with
  | zero =>
    intro s _
    exact Nat.zero_le _
  | succ m ih =>
    intro s h
    have e : s + 2 * (m + 1) = (s + 2 * m + 1) + 1 := by ring
    rw [e, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
    have h1 := ih s (fun i hi => h i (by omega))
    rcases h m (by omega) with h2 | h2
    · rw [if_pos h2]
      omega
    · rw [if_pos h2]
      omega

private theorem L470_path (k : ℕ) (c : ℕ → Bool)
    (h : ∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) :
    k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤
      ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  have hI : Finset.Icc 1 (2 * k) = Finset.Ico 1 (1 + 2 * k) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Finset.card_filter, hI]
  by_cases hends : c 0 = false ∧ c (2 * k + 1) = false
  · rw [if_pos hends]
    obtain ⟨h0, h1⟩ := hends
    cases k with
    | zero =>
      rcases h 0 (by omega) with h2 | h2
      · rw [h0] at h2
        exact absurd h2 (by decide)
      · rw [h1] at h2
        exact absurd h2 (by decide)
    | succ k =>
      have c1 : c 1 = true := by
        rcases h 0 (by omega) with h2 | h2
        · rw [h0] at h2
          exact absurd h2 (by decide)
        · exact h2
      have e3 : 2 * (k + 1) + 1 = 1 + 1 + 2 * k + 1 := by ring
      rw [e3] at h1
      have c2 : c (1 + 1 + 2 * k) = true := by
        rcases h (1 + 1 + 2 * k) (by omega) with h2 | h2
        · exact h2
        · rw [h1] at h2
          exact absurd h2 (by decide)
      have e : 1 + 2 * (k + 1) = (1 + 1 + 2 * k) + 1 := by ring
      rw [e, Finset.sum_Ico_succ_top (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hs := L470_aux c k (1 + 1) (fun i hi => h (1 + 1 + 2 * i) (by omega))
      rw [if_pos c1, if_pos c2]
      omega
  · rw [if_neg hends, Nat.add_zero]
    exact L470_aux c k 1 (fun i hi => h (1 + 2 * i) (by omega))

private theorem L470_enc (m u v u' v' : ℕ) (hv : v < m) (hv' : v' < m)
    (h : u * m + v = u' * m + v') : u = u' ∧ v = v' := by
  rcases Nat.lt_trichotomy u u' with h1 | h1 | h1
  · have h2 : (u + 1) * m ≤ u' * m := Nat.mul_le_mul_right m h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  · subst h1
    exact ⟨rfl, by omega⟩
  · have h2 : (u' + 1) * m ≤ u * m := Nat.mul_le_mul_right m h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega

private theorem L470_blk (k a a' p p' : ℕ) (hp : 1 ≤ p) (hp2 : p ≤ 2 * k) (hp' : 1 ≤ p')
    (hp2' : p' ≤ 2 * k) (h : 2 * k * a + p = 2 * k * a' + p') : a = a' := by
  rcases Nat.lt_trichotomy a a' with h1 | h1 | h1
  · have h2 : 2 * k * (a + 1) ≤ 2 * k * a' := Nat.mul_le_mul_left (2 * k) h1
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  · exact h1
  · have h2 : 2 * k * (a' + 1) ≤ 2 * k * a := Nat.mul_le_mul_left (2 * k) h1
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega

theorem PEqualNP.Outside.L_meta_470 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ c : ℕ, (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → c ≤ R.card) → ∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro m k H Q S hk hQ hS c hc U hU
  have hmN : m ≤ m + 2 * k * (m * m) := Nat.le_add_right _ _
  obtain ⟨emb, hemb⟩ : ∃ emb : Fin m → Fin (m + 2 * k * (m * m)), ∀ u, (emb u).val = u.val :=
    ⟨Fin.castLE hmN, fun u => rfl⟩
  have emb_inj : Function.Injective emb := by
    intro a b hab
    apply Fin.ext
    rw [← hemb a, ← hemb b, hab]
  have hbound : ∀ u v : Fin m, 2 * k * (u.val * m + v.val) + 2 * k ≤ 2 * k * (m * m) := by
    intro u v
    have h1 : u.val * m + v.val + 1 ≤ m * m := by
      have h2 : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m u.isLt
      rw [Nat.add_mul, Nat.one_mul] at h2
      have h4 := v.isLt
      omega
    have h3 := Nat.mul_le_mul_left (2 * k) h1
    rw [Nat.mul_add, Nat.mul_one] at h3
    exact h3
  have exQ : ∀ (u v : Fin m) (p : ℕ), p ≤ 2 * k + 1 →
      ∃ x : Fin (m + 2 * k * (m * m)), Q u v p x := by
    intro u v p hp
    by_cases h0 : p = 0
    · exact ⟨emb u, (hQ u v p _).mpr (Or.inl ⟨h0, hemb u⟩)⟩
    · by_cases h1 : p = 2 * k + 1
      · exact ⟨emb v, (hQ u v p _).mpr (Or.inr (Or.inl ⟨h1, hemb v⟩))⟩
      · have hb := hbound u v
        refine ⟨⟨m + 2 * k * (u.val * m + v.val) + p - 1, by omega⟩,
          (hQ u v p _).mpr (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))⟩
        show m + 2 * k * (u.val * m + v.val) + p - 1 + 1 = m + 2 * k * (u.val * m + v.val) + p
        omega
  obtain ⟨P, hP⟩ : ∃ P : Finset (Fin m × Fin m), ∀ e, e ∈ P ↔ (e.1 < e.2 ∧ H.Adj e.1 e.2) :=
    ⟨Finset.univ.filter (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2), fun e => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin m × Fin m),
      ∀ e, e ∈ B ↔ (e ∈ P ∧ emb e.1 ∉ U ∧ emb e.2 ∉ U) :=
    ⟨P.filter (fun e => emb e.1 ∉ U ∧ emb e.2 ∉ U), fun e => by
      simp only [Finset.mem_filter]⟩
  obtain ⟨R0, hR0⟩ : ∃ R0 : Finset (Fin m), ∀ u, u ∈ R0 ↔ emb u ∈ U :=
    ⟨Finset.univ.filter (fun u => emb u ∈ U), fun u => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Fin m × Fin m → Finset (Fin (m + 2 * k * (m * m))),
      ∀ e x, x ∈ blk e ↔ (x ∈ U ∧ ∃ p, 1 ≤ p ∧ p ≤ 2 * k ∧
        x.val + 1 = m + 2 * k * (e.1.val * m + e.2.val) + p) :=
    ⟨fun e => U.filter (fun x => ∃ p, 1 ≤ p ∧ p ≤ 2 * k ∧
        x.val + 1 = m + 2 * k * (e.1.val * m + e.2.val) + p), fun e x => by
      simp only [Finset.mem_filter]⟩
  have hedge : ∀ e ∈ P, k + (if e ∈ B then 1 else 0) ≤ (blk e).card := by
    intro e he
    obtain ⟨u, v⟩ := e
    obtain ⟨huv, hadj⟩ := (hP (u, v)).mp he
    obtain ⟨cf, hcf⟩ : ∃ cf : ℕ → Bool, ∀ p, cf p = true ↔ ∃ x ∈ U, Q u v p x :=
      ⟨fun p => decide (∃ x ∈ U, Q u v p x), fun p => decide_eq_true_iff⟩
    have hpath := L470_path k cf (by
      intro j hj
      obtain ⟨x, hx⟩ := exQ u v j (by omega)
      obtain ⟨y, hy⟩ := exQ u v (j + 1) (by omega)
      have hxy : S.Adj x y := (hS x y).mpr ⟨u, v, huv, hadj, j, hj, Or.inl ⟨hx, hy⟩⟩
      rcases hU x y hxy with h | h
      · exact Or.inl ((hcf j).mpr ⟨x, h, hx⟩)
      · exact Or.inr ((hcf (j + 1)).mpr ⟨y, h, hy⟩))
    have hcount : ((Finset.Icc 1 (2 * k)).filter (fun j => cf j = true)).card ≤
        (blk (u, v)).card := by
      apply Finset.card_le_card_of_surjOn
        (fun x : Fin (m + 2 * k * (m * m)) => x.val + 1 - (m + 2 * k * (u.val * m + v.val)))
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hp1, hp2⟩, hcp⟩ := hp
      obtain ⟨x, hxU, hxQ⟩ := (hcf p).mp hcp
      rcases (hQ u v p x).mp hxQ with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩
      · omega
      · omega
      · refine ⟨x, Finset.mem_coe.mpr ((hblk (u, v) x).mpr ⟨hxU, p, hp1, hp2, h⟩), ?_⟩
        show x.val + 1 - (m + 2 * k * (u.val * m + v.val)) = p
        omega
    refine le_trans ?_ (le_trans hpath hcount)
    by_cases hbad : (u, v) ∈ B
    · obtain ⟨_, hbu, hbv⟩ := (hB (u, v)).mp hbad
      have hc0 : cf 0 = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨x, hxU, hxQ⟩ := (hcf 0).mp h
        rcases (hQ u v 0 x).mp hxQ with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
        · have hx : x = emb u := Fin.ext (h.trans (hemb u).symm)
          rw [hx] at hxU
          exact hbu hxU
        · omega
        · omega
      have hc1 : cf (2 * k + 1) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨x, hxU, hxQ⟩ := (hcf (2 * k + 1)).mp h
        rcases (hQ u v (2 * k + 1) x).mp hxQ with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h, _⟩
        · omega
        · have hx : x = emb v := Fin.ext (h.trans (hemb v).symm)
          rw [hx] at hxU
          exact hbv hxU
        · omega
      rw [if_pos hbad, if_pos ⟨hc0, hc1⟩]
    · rw [if_neg hbad]
      exact Nat.add_le_add_left (Nat.zero_le _) k
  have hdisj : (P : Set (Fin m × Fin m)).PairwiseDisjoint blk := by
    intro e _ e' _ hne
    refine Finset.disjoint_left.mpr (fun x hx hx' => hne ?_)
    obtain ⟨_, p, hp1, hp2, hp⟩ := (hblk e x).mp hx
    obtain ⟨_, p', hp1', hp2', hp'⟩ := (hblk e' x).mp hx'
    have ha := L470_blk k (e.1.val * m + e.2.val) (e'.1.val * m + e'.2.val) p p' hp1 hp2 hp1' hp2'
      (by omega)
    obtain ⟨h1, h2⟩ := L470_enc m e.1.val e.2.val e'.1.val e'.2.val e.2.isLt e'.2.isLt ha
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hsum1 : ∑ e ∈ P, (k + (if e ∈ B then 1 else 0)) ≤ ∑ e ∈ P, (blk e).card :=
    Finset.sum_le_sum hedge
  have hsum2 : ∑ e ∈ P, (k + (if e ∈ B then 1 else 0)) = P.card * k + B.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole]
    have hf : P.filter (fun e => e ∈ B) = B := by
      ext e
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨((hB e).mp h).1, h⟩⟩
    rw [hf]
    rfl
  have hsum3 : (P.biUnion blk).card = ∑ e ∈ P, (blk e).card := Finset.card_biUnion hdisj
  have hU1 : (P.biUnion blk ∪ R0.image emb).card ≤ U.card := by
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨e, _, hxe⟩ := Finset.mem_biUnion.mp h
      exact ((hblk e x).mp hxe).1
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
      exact (hR0 u).mp hu
  have hU2 : (P.biUnion blk ∪ R0.image emb).card = (P.biUnion blk).card + R0.card := by
    have hinter : P.biUnion blk ∩ R0.image emb = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
      obtain ⟨e, _, hxe⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨_, p, hp1, _, hp⟩ := (hblk e x).mp hxe
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h2
      have h3 := hemb u
      have h4 := u.isLt
      omega
    have h5 := Finset.card_union_add_card_inter (P.biUnion blk) (R0.image emb)
    rw [hinter, Finset.card_empty, Nat.add_zero, Finset.card_image_of_injective _ emb_inj] at h5
    exact h5
  have hcover : c ≤ (R0 ∪ B.image Prod.fst).card := by
    apply hc
    intro a b hab
    have side : ∀ a b : Fin m, a < b → H.Adj a b →
        a ∈ R0 ∪ B.image Prod.fst ∨ b ∈ R0 ∪ B.image Prod.fst := by
      intro a b hlt hadj
      by_cases ha : emb a ∈ U
      · exact Or.inl (Finset.mem_union_left _ ((hR0 a).mpr ha))
      · by_cases hb : emb b ∈ U
        · exact Or.inr (Finset.mem_union_left _ ((hR0 b).mpr hb))
        · have hmem : (a, b) ∈ B := (hB (a, b)).mpr ⟨(hP (a, b)).mpr ⟨hlt, hadj⟩, ha, hb⟩
          exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩))
    rcases lt_trichotomy a b with h | h | h
    · exact side a b h hab
    · exact absurd h hab.ne
    · exact (side b a h hab.symm).symm
  have hRcard : (R0 ∪ B.image Prod.fst).card ≤ R0.card + B.card :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left Finset.card_image_le _)
  have hE : H.edgeSet.ncard ≤ P.card := by
    have hsub : H.edgeSet ⊆ ((P.image (fun e : Fin m × Fin m => s(e.1, e.2)) :
        Finset (Sym2 (Fin m))) : Set (Sym2 (Fin m))) := by
      intro e
      induction e using Sym2.ind with
      | _ a b =>
        intro hab
        rw [SimpleGraph.mem_edgeSet] at hab
        rw [Finset.mem_coe, Finset.mem_image]
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨(a, b), (hP _).mpr ⟨h, hab⟩, rfl⟩
        · exact absurd h hab.ne
        · exact ⟨(b, a), (hP _).mpr ⟨h, hab.symm⟩, Sym2.eq_swap⟩
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    exact le_trans h1 Finset.card_image_le
  have hmul : k * H.edgeSet.ncard ≤ P.card * k := by
    rw [Nat.mul_comm P.card k]
    exact Nat.mul_le_mul_left k hE
  omega
