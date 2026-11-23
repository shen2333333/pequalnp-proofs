import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_290_aux

lemma encode_lt {k m : ℕ} (u v : Fin m) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
  have hmul : u.val * m + v.val + 1 ≤ m * m := by
    have hu : u.val + 1 ≤ m := u.isLt
    have hv : v.val + 1 ≤ m := v.isLt
    nlinarith
  have h2k : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul_left (2 * k) hmul
  have hassoc : 2 * k * m * m = 2 * k * (m * m) := by ring
  have hexp : 2 * k * (u.val * m + v.val) + 2 * k = 2 * k * (u.val * m + v.val + 1) := by ring
  have hi : i.val < 2 * k := i.isLt
  omega

lemma div_eq {d a₁ b₁ a₂ b₂ : ℕ} (hb₁ : b₁ < d) (hb₂ : b₂ < d)
    (h : d * a₁ + b₁ = d * a₂ + b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ha : a₁ = a₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : d * (a₁ + 1) ≤ d * a₂ := Nat.mul_le_mul_left d hlt
      nlinarith
    · have : d * (a₂ + 1) ≤ d * a₁ := Nat.mul_le_mul_left d hgt
      nlinarith
  subst ha
  exact ⟨rfl, by omega⟩

def incl {k m : ℕ} (u : Fin m) : Fin (m + 2 * k * m * m) :=
  ⟨u.val, by omega⟩

def thread {k m : ℕ} (u v : Fin m) (i : Fin (2 * k)) : Fin (m + 2 * k * m * m) :=
  ⟨m + 2 * k * (u.val * m + v.val) + i.val, encode_lt u v i⟩

lemma incl_inj {k m : ℕ} : Function.Injective (@incl k m) := by
  intro a b h
  exact Fin.ext (by simpa [incl] using congrArg Fin.val h)

lemma thread_inj {k m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} {i₁ i₂ : Fin (2 * k)}
    (h : thread u₁ v₁ i₁ = thread u₂ v₂ i₂) : u₁ = u₂ ∧ v₁ = v₂ ∧ i₁ = i₂ := by
  have hval : m + 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      m + 2 * k * (u₂.val * m + v₂.val) + i₂.val := congrArg Fin.val h
  have h1 : 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      2 * k * (u₂.val * m + v₂.val) + i₂.val := by omega
  obtain ⟨huv, hi⟩ := div_eq i₁.isLt i₂.isLt h1
  have huv' : m * u₁.val + v₁.val = m * u₂.val + v₂.val := by
    linarith [Nat.mul_comm u₁.val m, Nat.mul_comm u₂.val m]
  obtain ⟨hu, hv⟩ := div_eq v₁.isLt v₂.isLt huv'
  exact ⟨Fin.ext hu, Fin.ext hv, Fin.ext hi⟩

lemma incl_ne_thread {k m : ℕ} (w u v : Fin m) (i : Fin (2 * k)) :
    incl w ≠ thread u v i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [incl, thread] at hv
  have := w.isLt
  omega

def subRel (k m : ℕ) (H : SimpleGraph (Fin m)) :
    Fin (m + 2 * k * m * m) → Fin (m + 2 * k * m * m) → Prop :=
  fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
     (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
     (i.val + 1 = 2 * k ∧ y.val = v.val))

lemma adj_first {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) :
    (SimpleGraph.fromRel (subRel k m H)).Adj (thread u v ⟨0, by omega⟩) (incl u) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨(incl_ne_thread u u v ⟨0, by omega⟩).symm, Or.inl ?_⟩
  exact ⟨u, v, huv, hadj, ⟨0, by omega⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma adj_step {k m : ℕ} {H : SimpleGraph (Fin m)}
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) {i : ℕ} (hi : i + 1 < 2 * k) :
    (SimpleGraph.fromRel (subRel k m H)).Adj (thread u v ⟨i, by omega⟩) (thread u v ⟨i + 1, hi⟩) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨fun h => by have := congrArg Fin.val h; dsimp [thread] at this; omega, Or.inl ?_⟩
  exact ⟨u, v, huv, hadj, ⟨i, by omega⟩, rfl, Or.inr (Or.inl ⟨hi, rfl⟩)⟩

lemma adj_last {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) :
    (SimpleGraph.fromRel (subRel k m H)).Adj (thread u v ⟨2 * k - 1, by omega⟩) (incl v) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨(incl_ne_thread v u v ⟨2 * k - 1, by omega⟩).symm, Or.inl ?_⟩
  exact ⟨u, v, huv, hadj, ⟨2 * k - 1, by omega⟩, rfl, Or.inr (Or.inr ⟨by dsimp; omega, rfl⟩)⟩

lemma path_cover_ge {k : ℕ} (A : Finset (Fin (2 * k)))
    (hstep : ∀ i : ℕ, (hi : i + 1 < 2 * k) → (⟨i, by omega⟩ : Fin (2 * k)) ∈ A ∨ ⟨i + 1, hi⟩ ∈ A) :
    k ≤ A.card := by
  classical
  let pick : Fin k → Fin (2 * k) := fun j =>
    if (⟨2 * j.val, by omega⟩ : Fin (2 * k)) ∈ A then ⟨2 * j.val, by omega⟩
    else ⟨2 * j.val + 1, by omega⟩
  have hmem : ∀ j : Fin k, pick j ∈ A := by
    intro j
    dsimp only [pick]
    split_ifs with h
    · exact h
    · exact (hstep (2 * j.val) (by omega)).resolve_left h
  have hinj : Function.Injective pick := by
    intro j₁ j₂ heq
    have hval : (pick j₁).val = (pick j₂).val := congrArg Fin.val heq
    have h1 : (pick j₁).val / 2 = j₁.val := by
      dsimp only [pick]; split_ifs <;> dsimp <;> omega
    have h2 : (pick j₂).val / 2 = j₂.val := by
      dsimp only [pick]; split_ifs <;> dsimp <;> omega
    exact Fin.ext (by omega)
  calc
    k = (Finset.univ : Finset (Fin k)).card := by simp
    _ = (Finset.univ.image pick).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ A.card := Finset.card_le_card (by intro x hx; rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩; exact hmem j)

lemma path_cover_ge_succ {k : ℕ} (hk : 1 ≤ k) (A : Finset (Fin (2 * k)))
    (h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ A)
    (hlast : (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) ∈ A)
    (hstep : ∀ i : ℕ, (hi : i + 1 < 2 * k) → (⟨i, by omega⟩ : Fin (2 * k)) ∈ A ∨ ⟨i + 1, hi⟩ ∈ A) :
    k + 1 ≤ A.card := by
  classical
  let pick : Fin (k + 1) → Fin (2 * k) := fun j =>
    if hj0 : j.val = 0 then ⟨0, by omega⟩
    else if hjk : j.val = k then ⟨2 * k - 1, by omega⟩
    else if (⟨2 * j.val - 1, by omega⟩ : Fin (2 * k)) ∈ A then ⟨2 * j.val - 1, by omega⟩
    else ⟨2 * j.val, by omega⟩
  have hmem : ∀ j : Fin (k + 1), pick j ∈ A := by
    intro j
    dsimp only [pick]
    by_cases hj0 : j.val = 0
    · rw [dif_pos hj0]; exact h0
    · rw [dif_neg hj0]
      by_cases hjk : j.val = k
      · rw [dif_pos hjk]; exact hlast
      · rw [dif_neg hjk]
        split_ifs with h
        · exact h
        · have hs := hstep (2 * j.val - 1) (by omega)
          have heq : (⟨2 * j.val - 1 + 1, by omega⟩ : Fin (2 * k)) = ⟨2 * j.val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [heq] at hs
          exact hs.resolve_left h
  have hinj : Function.Injective pick := by
    intro j₁ j₂ heq
    have hval : (pick j₁).val = (pick j₂).val := congrArg Fin.val heq
    have hbucket : ∀ j : Fin (k + 1), ((pick j).val + 1) / 2 = j.val := by
      intro j
      dsimp only [pick]
      by_cases hj0 : j.val = 0
      · rw [dif_pos hj0]; dsimp; omega
      · rw [dif_neg hj0]
        by_cases hjk : j.val = k
        · rw [dif_pos hjk]; dsimp; omega
        · rw [dif_neg hjk]
          split_ifs <;> dsimp <;> omega
    exact Fin.ext (by have := hbucket j₁; have := hbucket j₂; omega)
  calc
    k + 1 = (Finset.univ : Finset (Fin (k + 1))).card := by simp
    _ = (Finset.univ.image pick).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ A.card := Finset.card_le_card (by intro x hx; rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩; exact hmem j)

end PEqualNP.Outside.L_meta_290_aux

theorem PEqualNP.Outside.L_meta_290 :
    ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
      (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
            x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
            ((i.val = 0 ∧ y.val = u.val) ∨
             (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
             (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        ∀ U : Finset (Fin (m + 2 * k * m * m)),
          (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) →
          c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro k m c H hk hcoverH S hS U hcoverS
  subst hS
  let ordEdges : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)
  have hcard_ord : ordEdges.card = H.edgeSet.ncard := by
    have eH : {p : Fin m × Fin m // p ∈ ordEdges} ≃ H.edgeSet :=
      Equiv.ofBijective
        (fun p => ⟨s(p.1.1, p.1.2), by
          have hp := (Finset.mem_filter.mp p.2).2
          simpa [SimpleGraph.mem_edgeSet] using hp.2⟩)
        ⟨by
          rintro ⟨⟨u₁, v₁⟩, hp₁⟩ ⟨⟨u₂, v₂⟩, hp₂⟩ h
          have hlt₁ := (Finset.mem_filter.mp hp₁).2.1
          have hlt₂ := (Finset.mem_filter.mp hp₂).2.1
          have hs : s(u₁, v₁) = s(u₂, v₂) := congrArg Subtype.val h
          rw [Sym2.eq_iff] at hs
          rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact absurd (lt_trans hlt₁ hlt₂) (lt_irrefl _),
         by
          rintro ⟨e, he⟩
          induction e using Sym2.ind with
          | _ a b =>
            rw [SimpleGraph.mem_edgeSet] at he
            rcases lt_or_gt_of_ne (H.ne_of_adj he) with hab | hba
            · exact ⟨⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, he⟩⟩, rfl⟩
            · exact ⟨⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba, he.symm⟩⟩,
                Subtype.ext Sym2.eq_swap⟩⟩
    rw [Set.ncard_eq_toFinset_card']
    simp only [Set.toFinset_card]
    rw [← Fintype.card_congr eH, Fintype.card_coe]
  let Uorig : Finset (Fin m) :=
    Finset.univ.filter (fun u : Fin m => PEqualNP.Outside.L_meta_290_aux.incl (k := k) u ∈ U)
  let Uinner : Fin m × Fin m → Finset (Fin (2 * k)) := fun e =>
    Finset.univ.filter (fun i : Fin (2 * k) => PEqualNP.Outside.L_meta_290_aux.thread e.1 e.2 i ∈ U)
  let imgOrig : Finset (Fin (m + 2 * k * m * m)) :=
    Uorig.image (PEqualNP.Outside.L_meta_290_aux.incl (k := k))
  let imgEdge : Fin m × Fin m → Finset (Fin (m + 2 * k * m * m)) := fun e =>
    (Uinner e).image (PEqualNP.Outside.L_meta_290_aux.thread e.1 e.2)
  have hcard_orig : imgOrig.card = Uorig.card :=
    Finset.card_image_of_injective _ PEqualNP.Outside.L_meta_290_aux.incl_inj
  have hcard_edge : ∀ e : Fin m × Fin m, (imgEdge e).card = (Uinner e).card := fun e =>
    Finset.card_image_of_injective _ fun i₁ i₂ h => (PEqualNP.Outside.L_meta_290_aux.thread_inj h).2.2
  have hdisj_edges : Set.PairwiseDisjoint (ordEdges : Set (Fin m × Fin m)) imgEdge := by
    intro e₁ _ e₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨i₁, _, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨i₂, _, heq⟩
    obtain ⟨h1, h2, _⟩ := PEqualNP.Outside.L_meta_290_aux.thread_inj heq
    exact hne (Prod.ext h1.symm h2.symm)
  have hdisj_orig : Disjoint imgOrig (ordEdges.biUnion imgEdge) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨u, _, rfl⟩
    rcases Finset.mem_biUnion.mp hx₂ with ⟨e, _, hxe⟩
    rcases Finset.mem_image.mp hxe with ⟨i, _, heq⟩
    exact PEqualNP.Outside.L_meta_290_aux.incl_ne_thread u e.1 e.2 i heq.symm
  have hsub_U : imgOrig ∪ ordEdges.biUnion imgEdge ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · rcases Finset.mem_image.mp hx₁ with ⟨u, hu, rfl⟩
      exact (Finset.mem_filter.mp hu).2
    · rcases Finset.mem_biUnion.mp hx₂ with ⟨e, _, hxe⟩
      rcases Finset.mem_image.mp hxe with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
  have hU_ge : Uorig.card + ∑ e ∈ ordEdges, (Uinner e).card ≤ U.card := by
    have h1 := Finset.card_le_card hsub_U
    rw [Finset.card_union_of_disjoint hdisj_orig, Finset.card_biUnion hdisj_edges, hcard_orig] at h1
    simpa only [hcard_edge] using h1
  let badEdges : Finset (Fin m × Fin m) :=
    ordEdges.filter (fun e => e.1 ∉ Uorig ∧ e.2 ∉ Uorig)
  let T : Finset (Fin m) := Uorig ∪ badEdges.image Prod.fst
  have hT_cov : ∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v hadj
    by_cases hu : u ∈ Uorig
    · exact Or.inl (Finset.mem_union_left _ hu)
    · by_cases hv : v ∈ Uorig
      · exact Or.inr (Finset.mem_union_left _ hv)
      · rcases lt_or_gt_of_ne (H.ne_of_adj hadj) with huv | hvu
        · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, hu, hv⟩
        · refine Or.inr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v, u), ?_, rfl⟩))
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, hadj.symm⟩, hv, hu⟩
  have hc_le : c ≤ Uorig.card + badEdges.card := by
    calc
      c ≤ T.card := hcoverH T hT_cov
      _ ≤ Uorig.card + (badEdges.image Prod.fst).card := Finset.card_union_le _ _
      _ ≤ Uorig.card + badEdges.card := Nat.add_le_add_left Finset.card_image_le _
  have hinner_ge : ∀ e ∈ ordEdges, (if e ∈ badEdges then k + 1 else k) ≤ (Uinner e).card := by
    intro e he
    have hp := (Finset.mem_filter.mp he).2
    have hstep : ∀ i : ℕ, (hi : i + 1 < 2 * k) →
        (⟨i, by omega⟩ : Fin (2 * k)) ∈ Uinner e ∨ ⟨i + 1, hi⟩ ∈ Uinner e := by
      intro i hi
      rcases hcoverS _ _ (PEqualNP.Outside.L_meta_290_aux.adj_step hp.1 hp.2 hi) with h1 | h2
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
    split_ifs with hbad
    · have hnb := (Finset.mem_filter.mp hbad).2
      have hnu : PEqualNP.Outside.L_meta_290_aux.incl (k := k) e.1 ∉ U := fun h =>
        hnb.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hnv : PEqualNP.Outside.L_meta_290_aux.incl (k := k) e.2 ∉ U := fun h =>
        hnb.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ Uinner e :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hcoverS _ _ (PEqualNP.Outside.L_meta_290_aux.adj_first hk hp.1 hp.2)).resolve_right hnu⟩
      have hlast : (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) ∈ Uinner e :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hcoverS _ _ (PEqualNP.Outside.L_meta_290_aux.adj_last hk hp.1 hp.2)).resolve_right hnv⟩
      exact PEqualNP.Outside.L_meta_290_aux.path_cover_ge_succ hk (Uinner e) h0 hlast hstep
    · exact PEqualNP.Outside.L_meta_290_aux.path_cover_ge (Uinner e) hstep
  have hsum_ge : k * ordEdges.card + badEdges.card ≤ ∑ e ∈ ordEdges, (Uinner e).card := by
    have h1 := Finset.sum_le_sum hinner_ge
    have hsplit : ∑ e ∈ ordEdges, (if e ∈ badEdges then k + 1 else k) =
        k * ordEdges.card + badEdges.card := by
      have hrew : ∀ e ∈ ordEdges, (if e ∈ badEdges then k + 1 else k) =
          k + (if e ∈ badEdges then 1 else 0) := by
        intro e _; split_ifs <;> omega
      rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
        mul_comm, Finset.sum_boole]
      have hfilt : ordEdges.filter (fun e => e ∈ badEdges) = badEdges := by
        ext e
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
      rw [hfilt]
      simp
    omega
  rw [← hcard_ord]
  omega
