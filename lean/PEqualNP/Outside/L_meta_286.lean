import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_286_aux

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

lemma subRel_irrefl (k m : ℕ) (H : SimpleGraph (Fin m)) (x : Fin (m + 2 * k * m * m)) :
    ¬ subRel k m H x x := by
  rintro ⟨u, v, _, _, i, hx, ⟨_, hy⟩ | ⟨_, hy⟩ | ⟨_, hy⟩⟩
  · have := u.isLt; omega
  · omega
  · have := v.isLt; omega

def edgeImg {k m : ℕ} (hk : 1 ≤ k) (u v : Fin m) (r : Fin (2 * k + 1)) :
    Sym2 (Fin (m + 2 * k * m * m)) :=
  if h0 : r.val = 0 then
    s(thread u v ⟨0, by omega⟩, incl u)
  else if hlt : r.val < 2 * k then
    s(thread u v ⟨r.val - 1, by omega⟩, thread u v ⟨r.val, hlt⟩)
  else
    s(thread u v ⟨2 * k - 1, by omega⟩, incl v)

lemma edgeImg_mem {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) (r : Fin (2 * k + 1)) :
    edgeImg hk u v r ∈ (SimpleGraph.fromRel (subRel k m H)).edgeSet := by
  unfold edgeImg
  split_ifs with h0 hlt
  · rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
    refine ⟨(incl_ne_thread u u v ⟨0, by omega⟩).symm, Or.inl ?_⟩
    exact ⟨u, v, huv, hadj, ⟨0, by omega⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
    have hne : thread u v ⟨r.val - 1, by omega⟩ ≠ thread u v ⟨r.val, hlt⟩ := by
      intro h
      have hv := congrArg Fin.val h
      dsimp only [thread] at hv
      omega
    refine ⟨hne, Or.inl ?_⟩
    exact ⟨u, v, huv, hadj, ⟨r.val - 1, by omega⟩, rfl,
      Or.inr (Or.inl ⟨by dsimp; omega, by dsimp [thread]; omega⟩)⟩
  · rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
    refine ⟨(incl_ne_thread v u v ⟨2 * k - 1, by omega⟩).symm, Or.inl ?_⟩
    exact ⟨u, v, huv, hadj, ⟨2 * k - 1, by omega⟩, rfl,
      Or.inr (Or.inr ⟨by dsimp; omega, rfl⟩)⟩

lemma edgeImg_inj {k m : ℕ} (hk : 1 ≤ k)
    {u₁ v₁ u₂ v₂ : Fin m} {r₁ r₂ : Fin (2 * k + 1)}
    (h : edgeImg hk u₁ v₁ r₁ = edgeImg hk u₂ v₂ r₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ r₁ = r₂ := by
  unfold edgeImg at h
  split_ifs at h with h1_0 h2_0 h2_lt h1_lt h2_0' h2_lt' h2_0'' h2_lt''
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨ht, _⟩ | ⟨hbad, _⟩
    · obtain ⟨rfl, rfl, _⟩ := thread_inj ht
      exact ⟨rfl, rfl, Fin.ext (by omega)⟩
    · exact absurd hbad.symm (incl_ne_thread _ _ _ _)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨_, hbad⟩ | ⟨_, hbad⟩ <;> exact absurd hbad (incl_ne_thread _ _ _ _)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨ht, _⟩ | ⟨hbad, _⟩
    · obtain ⟨_, _, hi⟩ := thread_inj ht
      have := congrArg Fin.val hi; dsimp at this; omega
    · exact absurd hbad.symm (incl_ne_thread _ _ _ _)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨_, hbad⟩ | ⟨hbad, _⟩ <;> exact absurd hbad.symm (incl_ne_thread _ _ _ _)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨ht₁, ht₂⟩ | ⟨ht₁, ht₂⟩
    · obtain ⟨rfl, rfl, hi⟩ := thread_inj ht₂
      exact ⟨rfl, rfl, Fin.ext (by simpa using congrArg Fin.val hi)⟩
    · obtain ⟨_, _, hi₁⟩ := thread_inj ht₁
      obtain ⟨_, _, hi₂⟩ := thread_inj ht₂
      have hv₁ := congrArg Fin.val hi₁
      have hv₂ := congrArg Fin.val hi₂
      dsimp at hv₁ hv₂; omega
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨_, hbad⟩ | ⟨hbad, _⟩ <;> exact absurd hbad.symm (incl_ne_thread _ _ _ _)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨ht, _⟩ | ⟨hbad, _⟩
    · obtain ⟨_, _, hi⟩ := thread_inj ht
      have := congrArg Fin.val hi; dsimp at this; omega
    · exact absurd hbad.symm (incl_ne_thread _ _ _ _)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨_, hbad⟩ | ⟨_, hbad⟩ <;> exact absurd hbad (incl_ne_thread _ _ _ _)
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨ht, _⟩ | ⟨hbad, _⟩
    · obtain ⟨rfl, rfl, _⟩ := thread_inj ht
      have h1 : r₁.val = 2 * k := by have := r₁.isLt; omega
      have h2 : r₂.val = 2 * k := by have := r₂.isLt; omega
      exact ⟨rfl, rfl, Fin.ext (by omega)⟩
    · exact absurd hbad.symm (incl_ne_thread _ _ _ _)

lemma edgeImg_surj {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    (e : Sym2 (Fin (m + 2 * k * m * m)))
    (he : e ∈ (SimpleGraph.fromRel (subRel k m H)).edgeSet) :
    ∃ (u v : Fin m) (r : Fin (2 * k + 1)), u < v ∧ H.Adj u v ∧ edgeImg hk u v r = e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
    obtain ⟨_, hrel | hrel⟩ := he
    · obtain ⟨u, v, huv, hadj, i, hx, ⟨hi0, hy⟩ | ⟨hilt, hy⟩ | ⟨hitop, hy⟩⟩ := hrel
      · refine ⟨u, v, ⟨0, by omega⟩, huv, hadj, ?_⟩
        simp only [edgeImg, dite_true]
        have hx' : thread u v ⟨0, by omega⟩ = x := Fin.ext (by dsimp [thread]; omega)
        have hy' : incl u = y := Fin.ext (by dsimp [incl]; omega)
        rw [hx', hy']
      · refine ⟨u, v, ⟨i.val + 1, by omega⟩, huv, hadj, ?_⟩
        unfold edgeImg
        rw [dif_neg (by dsimp; omega), dif_pos (by dsimp; exact hilt)]
        have hx' : thread u v ⟨i.val + 1 - 1, by omega⟩ = x := Fin.ext (by dsimp [thread]; omega)
        have hy' : thread u v ⟨i.val + 1, hilt⟩ = y := Fin.ext (by dsimp [thread]; omega)
        rw [hx', hy']
      · refine ⟨u, v, ⟨2 * k, by omega⟩, huv, hadj, ?_⟩
        unfold edgeImg
        rw [dif_neg (by dsimp; omega), dif_neg (by dsimp; omega)]
        have hx' : thread u v ⟨2 * k - 1, by omega⟩ = x := Fin.ext (by dsimp [thread]; omega)
        have hy' : incl v = y := Fin.ext (by dsimp [incl]; omega)
        rw [hx', hy']
    · obtain ⟨u, v, huv, hadj, i, hy, ⟨hi0, hx⟩ | ⟨hilt, hx⟩ | ⟨hitop, hx⟩⟩ := hrel
      · refine ⟨u, v, ⟨0, by omega⟩, huv, hadj, ?_⟩
        simp only [edgeImg, dite_true]
        have hy' : thread u v ⟨0, by omega⟩ = y := Fin.ext (by dsimp [thread]; omega)
        have hx' : incl u = x := Fin.ext (by dsimp [incl]; omega)
        rw [hy', hx', Sym2.eq_swap]
      · refine ⟨u, v, ⟨i.val + 1, by omega⟩, huv, hadj, ?_⟩
        unfold edgeImg
        rw [dif_neg (by dsimp; omega), dif_pos (by dsimp; exact hilt)]
        have hy' : thread u v ⟨i.val + 1 - 1, by omega⟩ = y := Fin.ext (by dsimp [thread]; omega)
        have hx' : thread u v ⟨i.val + 1, hilt⟩ = x := Fin.ext (by dsimp [thread]; omega)
        rw [hy', hx', Sym2.eq_swap]
      · refine ⟨u, v, ⟨2 * k, by omega⟩, huv, hadj, ?_⟩
        unfold edgeImg
        rw [dif_neg (by dsimp; omega), dif_neg (by dsimp; omega)]
        have hy' : thread u v ⟨2 * k - 1, by omega⟩ = y := Fin.ext (by dsimp [thread]; omega)
        have hx' : incl v = x := Fin.ext (by dsimp [incl]; omega)
        rw [hy', hx', Sym2.eq_swap]

end PEqualNP.Outside.L_meta_286_aux

theorem PEqualNP.Outside.L_meta_286 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
            x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
            ((i.val = 0 ∧ y.val = u.val) ∨
             (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
             (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  classical
  intro k m H hk S hS
  subst hS
  let ordEdges := {p : Fin m × Fin m // p.1 < p.2 ∧ H.Adj p.1 p.2}
  have eH : ordEdges ≃ H.edgeSet :=
    Equiv.ofBijective
      (fun p => ⟨s(p.1.1, p.1.2), by simpa [SimpleGraph.mem_edgeSet] using p.2.2⟩)
      ⟨by
        rintro ⟨⟨u₁, v₁⟩, hlt₁, _⟩ ⟨⟨u₂, v₂⟩, hlt₂, _⟩ h
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
          · exact ⟨⟨(a, b), hab, he⟩, rfl⟩
          · exact ⟨⟨(b, a), hba, he.symm⟩, Subtype.ext Sym2.eq_swap⟩⟩
  have eS : Fin (2 * k + 1) × ordEdges ≃ (SimpleGraph.fromRel (PEqualNP.Outside.L_meta_286_aux.subRel k m H)).edgeSet :=
    Equiv.ofBijective
      (fun p => ⟨PEqualNP.Outside.L_meta_286_aux.edgeImg hk p.2.1.1 p.2.1.2 p.1,
        PEqualNP.Outside.L_meta_286_aux.edgeImg_mem hk p.2.2.1 p.2.2.2 p.1⟩)
      ⟨by
        rintro ⟨r₁, ⟨⟨u₁, v₁⟩, _⟩⟩ ⟨r₂, ⟨⟨u₂, v₂⟩, _⟩⟩ h
        obtain ⟨rfl, rfl, rfl⟩ := PEqualNP.Outside.L_meta_286_aux.edgeImg_inj hk (congrArg Subtype.val h)
        rfl,
       by
        rintro ⟨e, he⟩
        obtain ⟨u, v, r, huv, hadj, rfl⟩ := PEqualNP.Outside.L_meta_286_aux.edgeImg_surj hk e he
        exact ⟨⟨r, ⟨(u, v), huv, hadj⟩⟩, rfl⟩⟩
  change (SimpleGraph.fromRel (PEqualNP.Outside.L_meta_286_aux.subRel k m H)).edgeSet.ncard =
    (2 * k + 1) * H.edgeSet.ncard
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_card]
  rw [← Fintype.card_congr eS, ← Fintype.card_congr eH, Fintype.card_prod, Fintype.card_fin]
