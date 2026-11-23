import Mathlib
import PEqualNP.Defs

private abbrev V492 (k m : ℕ) := Fin (m + 2 * k * m * m)

private def Rel492 (k m : ℕ) (H : SimpleGraph (Fin m)) (x y : V492 k m) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
     (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
     (i.val + 1 = 2 * k ∧ y.val = v.val))

private abbrev G492 (k m : ℕ) (H : SimpleGraph (Fin m)) :=
  SimpleGraph.fromRel (Rel492 k m H)

private def pos492 {k m : ℕ} (u v : Fin m) (p : ℕ) (x : V492 k m) : Prop :=
  (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
  (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)

private lemma adj492 {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k) (x y : V492 k m)
    (h : (G492 k m H).Adj x y) :
    ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((pos492 u v p x ∧ pos492 u v (p + 1) y) ∨
       (pos492 u v p y ∧ pos492 u v (p + 1) x)) := by
  have directed (a b : V492 k m) (hab : Rel492 k m H a b) :
      ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((pos492 u v p a ∧ pos492 u v (p + 1) b) ∨
         (pos492 u v p b ∧ pos492 u v (p + 1) a)) := by
    obtain ⟨u, v, huv, he, i, ha, hnext⟩ := hab
    refine ⟨u, v, huv, he, ?_⟩
    rcases hnext with ⟨hi, hb⟩ | ⟨hi, hb⟩ | ⟨hi, hb⟩
    · refine ⟨0, by omega, Or.inr ⟨Or.inl ⟨rfl, hb⟩, ?_⟩⟩
      exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
    · refine ⟨i.val + 1, by omega, Or.inl ⟨?_, ?_⟩⟩
      · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
    · refine ⟨2 * k, le_rfl, Or.inl ⟨?_, Or.inr (Or.inl ⟨rfl, hb⟩)⟩⟩
      exact Or.inr (Or.inr ⟨by omega, le_rfl, by omega⟩)
  rcases h.2 with hxy | hyx
  · exact directed x y hxy
  · obtain ⟨u, v, huv, he, p, hp, hpos⟩ := directed y x hyx
    exact ⟨u, v, huv, he, p, hp, hpos.symm⟩

-- The degree bound and the distance function adapt the proof of L-meta-460.
private lemma decode (m K u v p z : ℕ) (hK : 0 < K) (hv : v < m) (hp1 : 1 ≤ p) (hp2 : p ≤ K)
    (hz : z + 1 = m + K * (u * m + v) + p) :
    m ≤ z ∧ (z - m) / K = u * m + v ∧ (z - m) % K = p - 1 ∧
      (u * m + v) / m = u ∧ (u * m + v) % m = v := by
  have hm : 0 < m := by omega
  have hmz : m ≤ z := by
    generalize K * (u * m + v) = T at hz
    omega
  have h1 : (z - m) / K = u * m + v ∧ (z - m) % K = p - 1 := by
    rw [Nat.div_mod_unique hK]
    constructor
    · generalize K * (u * m + v) = T at hz ⊢
      omega
    · omega
  have h2 : (u * m + v) / m = u ∧ (u * m + v) % m = v := by
    rw [Nat.div_mod_unique hm]
    exact ⟨by ring, hv⟩
  exact ⟨hmz, h1.1, h1.2, h2.1, h2.2⟩

private def gpot (m k xv z : ℕ) : ℕ :=
  if z = xv then 0
  else if z < m then 2 * k + 1
  else if (z - m) / (2 * k) / m = xv then (z - m) % (2 * k) + 1
  else if (z - m) / (2 * k) % m = xv then 2 * k + 1 - ((z - m) % (2 * k) + 1)
  else 2 * k + 1

private lemma g_path {m k xv u v p z : ℕ} (hk : 1 ≤ k) (hxv : xv < m) (hu : u < m) (hv : v < m)
    (huv : u < v)
    (hQ : (p = 0 ∧ z = u) ∨ (p = 2 * k + 1 ∧ z = v) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ z + 1 = m + 2 * k * (u * m + v) + p)) :
    gpot m k xv z = if u = xv then p else if v = xv then 2 * k + 1 - p else 2 * k + 1 := by
  rcases hQ with ⟨hp, hz⟩ | ⟨hp, hz⟩ | ⟨hp1, hp2, hz⟩
  · subst hp hz
    unfold gpot
    split_ifs <;> omega
  · subst hp hz
    unfold gpot
    split_ifs <;> omega
  · obtain ⟨hmz, hb, hr, hbu, hbv⟩ := decode m (2 * k) u v p z (by omega) hv hp1 hp2 hz
    unfold gpot
    rw [hb, hr, hbu, hbv]
    split_ifs <;> omega

theorem PEqualNP.Outside.L_meta_492 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ u v : Fin (m + 2 * k * m * m), u ≠ v → 3 ≤ (S.neighborSet u).ncard → 3 ≤ (S.neighborSet v).ncard → ∀ p : S.Walk u v, 2 * k + 1 ≤ p.length := by
  intro k m H hk S hS x y hxy hx3 hy3 w
  change S = G492 k m H at hS
  subst S
  have deg : ∀ z : V492 k m, m ≤ z.val → ((G492 k m H).neighborSet z).ncard ≤ 2 := by
    intro z hmz
    have hsub : (G492 k m H).neighborSet z ⊆
        {w | w.val = if (z.val - m) % (2 * k) = 0 then (z.val - m) / (2 * k) / m
          else z.val - 1} ∪
        {w | w.val = if (z.val - m) % (2 * k) + 1 = 2 * k then (z.val - m) / (2 * k) % m
          else z.val + 1} := by
      intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      obtain ⟨u, v, huv, -, p, hp, h⟩ := adj492 hk z w hw
      have hu := u.isLt
      have hv := v.isLt
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      rcases h with ⟨hz, hw'⟩ | ⟨hw', hz⟩
      · unfold pos492 at hz hw'
        rcases hz with ⟨-, hz⟩ | ⟨hp', -⟩ | ⟨hp1, hp2, hz⟩
        · omega
        · omega
        · obtain ⟨-, hb, hr, -, hbv⟩ :=
            decode m (2 * k) u.val v.val p z.val (by omega) hv hp1 hp2 hz
          right
          rw [hr, hb, hbv]
          rcases hw' with ⟨h0, -⟩ | ⟨h1, hw'⟩ | ⟨-, h2, hw'⟩
          · omega
          · rw [ite_eq_left (by omega)]
            exact hw'
          · rw [ite_eq_right (by omega)]
            generalize 2 * k * (u.val * m + v.val) = T at hz hw'
            omega
      · unfold pos492 at hz hw'
        rcases hz with ⟨h0, -⟩ | ⟨hp', hz⟩ | ⟨hp1, hp2, hz⟩
        · omega
        · omega
        · obtain ⟨-, hb, hr, hbu, -⟩ :=
            decode m (2 * k) u.val v.val (p + 1) z.val (by omega) hv hp1 hp2 hz
          left
          rw [hr, hb, hbu]
          rcases hw' with ⟨h0, hw'⟩ | ⟨h1, -⟩ | ⟨h1, -, hw'⟩
          · rw [ite_eq_left (by omega)]
            exact hw'
          · omega
          · rw [ite_eq_right (by omega)]
            generalize 2 * k * (u.val * m + v.val) = T at hz hw'
            omega
    have hone : ∀ c : ℕ, ({w | w.val = c} : Set (V492 k m)).ncard ≤ 1 := by
      intro c
      rw [Set.ncard_le_one]
      intro a ha b hb
      simp only [Set.mem_ofPred_eq] at ha hb
      exact Fin.ext (ha.trans hb.symm)
    calc ((G492 k m H).neighborSet z).ncard ≤ _ := Set.ncard_le_ncard hsub
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add (hone _) (hone _)
  have orig : ∀ z : V492 k m, 3 ≤ ((G492 k m H).neighborSet z).ncard → z.val < m := by
    intro z hz
    by_contra hzm
    have := deg z (by omega)
    omega
  have hxm := orig x hx3
  have hym := orig y hy3
  have lip : ∀ a b : V492 k m, (G492 k m H).Adj a b →
      gpot m k x.val b.val ≤ gpot m k x.val a.val + 1 := by
    intro a b hab
    obtain ⟨u, v, huv, -, p, hp, h⟩ := adj492 hk a b hab
    have huv' : u.val < v.val := huv
    rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · unfold pos492 at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
    · unfold pos492 at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
  have hwalk : ∀ (a b : V492 k m) (q : (G492 k m H).Walk a b),
      gpot m k x.val b.val ≤ gpot m k x.val a.val + q.length := by
    intro a b q
    induction q with
    | nil => simp
    | cons hadj q ih =>
      rw [SimpleGraph.Walk.length_cons]
      have := lip _ _ hadj
      omega
  have hgx : gpot m k x.val x.val = 0 := by
    unfold gpot
    simp
  have hgy : gpot m k x.val y.val = 2 * k + 1 := by
    have hne : y.val ≠ x.val := fun h => hxy (Fin.ext h).symm
    unfold gpot
    rw [ite_eq_right hne, ite_eq_left hym]
  simpa only [hgx, hgy, Nat.zero_add] using hwalk x y w
