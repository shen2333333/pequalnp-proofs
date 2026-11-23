import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_460_aux

lemma decode (m K u v p z : ℕ) (hK : 0 < K) (hv : v < m) (hp1 : 1 ≤ p) (hp2 : p ≤ K)
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

def gpot (m k xv z : ℕ) : ℕ :=
  if z = xv then 0
  else if z < m then 2 * k + 1
  else if (z - m) / (2 * k) / m = xv then (z - m) % (2 * k) + 1
  else if (z - m) / (2 * k) % m = xv then 2 * k + 1 - ((z - m) % (2 * k) + 1)
  else 2 * k + 1

lemma g_path {m k xv u v p z : ℕ} (hk : 1 ≤ k) (hxv : xv < m) (hu : u < m) (hv : v < m)
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

end PEqualNP.Outside.L_meta_460_aux

open PEqualNP.Outside.L_meta_460_aux in
theorem PEqualNP.Outside.L_meta_460 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x ≠ y → 3 ≤ (S.neighborSet x).ncard → 3 ≤ (S.neighborSet y).ncard → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hxy hx3 hy3 w
  have deg : ∀ z : Fin (m + 2 * k * (m * m)), m ≤ z.val → (S.neighborSet z).ncard ≤ 2 := by
    intro z hmz
    have hsub : S.neighborSet z ⊆
        {w | w.val = if (z.val - m) % (2 * k) = 0 then (z.val - m) / (2 * k) / m
          else z.val - 1} ∪
        {w | w.val = if (z.val - m) % (2 * k) + 1 = 2 * k then (z.val - m) / (2 * k) % m
          else z.val + 1} := by
      intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      obtain ⟨u, v, huv, -, p, hp, h⟩ := (hS z w).1 hw
      have hu := u.isLt
      have hv := v.isLt
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      rcases h with ⟨hz, hw'⟩ | ⟨hw', hz⟩
      · rw [hQ] at hz hw'
        rcases hz with ⟨-, hz⟩ | ⟨hp', -⟩ | ⟨hp1, hp2, hz⟩
        · omega
        · omega
        · obtain ⟨-, hb, hr, -, hbv⟩ :=
            decode m (2 * k) u.val v.val p z.val (by omega) hv hp1 hp2 hz
          right
          rw [hr, hb, hbv]
          rcases hw' with ⟨h0, -⟩ | ⟨h1, hw'⟩ | ⟨-, h2, hw'⟩
          · omega
          · rw [if_pos (by omega)]
            exact hw'
          · rw [if_neg (by omega)]
            generalize 2 * k * (u.val * m + v.val) = T at hz hw'
            omega
      · rw [hQ] at hz hw'
        rcases hz with ⟨h0, -⟩ | ⟨hp', hz⟩ | ⟨hp1, hp2, hz⟩
        · omega
        · omega
        · obtain ⟨-, hb, hr, hbu, -⟩ :=
            decode m (2 * k) u.val v.val (p + 1) z.val (by omega) hv hp1 hp2 hz
          left
          rw [hr, hb, hbu]
          rcases hw' with ⟨h0, hw'⟩ | ⟨h1, -⟩ | ⟨h1, -, hw'⟩
          · rw [if_pos (by omega)]
            exact hw'
          · omega
          · rw [if_neg (by omega)]
            generalize 2 * k * (u.val * m + v.val) = T at hz hw'
            omega
    have hone : ∀ c : ℕ, ({w | w.val = c} : Set (Fin (m + 2 * k * (m * m)))).ncard ≤ 1 := by
      intro c
      rw [Set.ncard_le_one]
      intro a ha b hb
      simp only [Set.mem_ofPred_eq] at ha hb
      exact Fin.ext (ha.trans hb.symm)
    calc (S.neighborSet z).ncard ≤ _ := Set.ncard_le_ncard hsub
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add (hone _) (hone _)
  have orig : ∀ z : Fin (m + 2 * k * (m * m)), 3 ≤ (S.neighborSet z).ncard → z.val < m := by
    intro z hz
    by_contra hzm
    have := deg z (by omega)
    omega
  have hxm := orig x hx3
  have hym := orig y hy3
  have lip : ∀ a b : Fin (m + 2 * k * (m * m)), S.Adj a b →
      gpot m k x.val b.val ≤ gpot m k x.val a.val + 1 := by
    intro a b hab
    obtain ⟨u, v, huv, -, p, hp, h⟩ := (hS a b).1 hab
    have huv' : u.val < v.val := huv
    rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [hQ] at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
    · rw [hQ] at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
  have hwalk : ∀ (a b : Fin (m + 2 * k * (m * m))) (q : S.Walk a b),
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
    rw [if_neg hne, if_pos hym]
  have := hwalk x y w
  omega
