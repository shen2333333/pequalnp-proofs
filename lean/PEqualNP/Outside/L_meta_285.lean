import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside

private lemma subdiv285_div_mod {m k : ℕ} (u : ℕ) {v i : ℕ} (hk : 1 ≤ k) (hv : v < m)
    (hi : i < 2 * k) :
    ((m + 2 * k * (u * m + v) + i - m) / (2 * k) / m = u) ∧
    ((m + 2 * k * (u * m + v) + i - m) / (2 * k) % m = v) ∧
    ((m + 2 * k * (u * m + v) + i - m) % (2 * k) = i) := by
  have h1 : m + 2 * k * (u * m + v) + i - m = 2 * k * (u * m + v) + i := by omega
  rw [h1]
  have h2k : 0 < 2 * k := by omega
  have hdiv : (2 * k * (u * m + v) + i) / (2 * k) = u * m + v := by
    rw [Nat.mul_add_div h2k, Nat.div_eq_of_lt hi, Nat.add_zero]
  have hmod : (2 * k * (u * m + v) + i) % (2 * k) = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have hm : 0 < m := by omega
  rw [hdiv, hmod]
  refine ⟨?_, ?_, rfl⟩
  · rw [Nat.mul_comm u m, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero]
  · rw [Nat.mul_comm u m, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]

private lemma mod_add_lt_eq {a b L : ℕ} (ha : a < L) (hb : b < L) :
    (a + b) % L = if a + b < L then a + b else a + b - L := by
  by_cases h : a + b < L
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    have hsplit : a + b = (a + b - L) + L := by omega
    conv_lhs => rw [hsplit]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private lemma mod_add_sub_lt_eq {a b L : ℕ} (ha : a < L) (hb : b ≤ L) (hpos : 0 < b) :
    (a + L - b) % L = if b ≤ a then a - b else a + L - b := by
  by_cases h : b ≤ a
  · rw [if_pos h]
    have hsplit : a + L - b = (a - b) + L := by omega
    conv_lhs => rw [hsplit]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

private def subdiv285Phi (m k : ℕ) (x z : Fin (m + 2 * k * m * m)) : ℕ :=
  if z.val < m then
    if z.val = x.val then 0 else 2 * k + 1
  else
    let q := (z.val - m) / (2 * k)
    let r := (z.val - m) % (2 * k)
    if q / m = x.val then r + 1
    else if q % m = x.val then 2 * k - r
    else 2 * k + 1

theorem L_meta_285 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
            ∃ i : Fin (2 * k),
              x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
              ((i.val = 0 ∧ y.val = u.val) ∨
                (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
                (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        ∀ (L : ℕ) (c : ℕ → Fin (m + 2 * k * m * m)),
          3 ≤ L →
          (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) →
          (∀ i : ℕ, i < L → S.Adj (c i) (c ((i + 1) % L))) →
          6 * k + 3 ≤ L := by
  intro k m H hk S hS L c hL3 hc_inj hc_adj
  let R : Fin (m + 2 * k * m * m) → Fin (m + 2 * k * m * m) → Prop :=
    fun x y =>
      ∃ u0 v0 : Fin m, u0 < v0 ∧ H.Adj u0 v0 ∧
        ∃ i : Fin (2 * k),
          x.val = m + 2 * k * (u0.val * m + v0.val) + i.val ∧
          ((i.val = 0 ∧ y.val = u0.val) ∨
            (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u0.val * m + v0.val) + i.val + 1) ∨
            (i.val + 1 = 2 * k ∧ y.val = v0.val))
  have hS_adj : ∀ a b : Fin (m + 2 * k * m * m), S.Adj a b ↔ a ≠ b ∧ (R a b ∨ R b a) := by
    intro a b
    rw [hS, SimpleGraph.fromRel_adj]
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_eq : m = 0 := by omega
    have hwlt := (c 0).isLt
    have h0 : m + 2 * k * m * m = 0 := by simp [hm_eq]
    omega
  have h2k_pos : 0 < 2 * k := by omega
  have hno_orig_adj : ∀ a b : Fin (m + 2 * k * m * m),
      a.val < m → b.val < m → ¬ S.Adj a b := by
    intro a b ha hb hab
    rcases ((hS_adj a b).mp hab).2 with ⟨u, v, _, _, i, hax, _⟩ | ⟨u, v, _, _, i, hbx, _⟩ <;> omega
  have hstep_internal : ∀ a b : Fin (m + 2 * k * m * m),
      m ≤ a.val → m ≤ b.val → S.Adj a b →
      (a.val - m) / (2 * k) = (b.val - m) / (2 * k) ∧
      ((b.val - m) % (2 * k) = (a.val - m) % (2 * k) + 1 ∨
        (a.val - m) % (2 * k) = (b.val - m) % (2 * k) + 1) := by
    intro a b ham hbm hab
    rcases ((hS_adj a b).mp hab).2 with ⟨u, v, _, _, i, ha, hbr⟩ | ⟨u, v, _, _, i, hb, hbr⟩
    · rcases hbr with ⟨_, hbu⟩ | ⟨hi1, hb⟩ | ⟨_, hbv⟩
      · have := u.isLt; omega
      · have hda := subdiv285_div_mod u.val hk v.isLt i.isLt
        have hdb := subdiv285_div_mod u.val hk v.isLt hi1
        have hb' : b.val = m + 2 * k * (u.val * m + v.val) + (i.val + 1) := by omega
        rw [← ha] at hda
        rw [← hb'] at hdb
        have hqa : (a.val - m) / (2 * k) = u.val * m + v.val := by
          have h1 : a.val - m = 2 * k * (u.val * m + v.val) + i.val := by omega
          rw [h1, Nat.mul_add_div h2k_pos, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
        have hqb : (b.val - m) / (2 * k) = u.val * m + v.val := by
          have h1 : b.val - m = 2 * k * (u.val * m + v.val) + (i.val + 1) := by omega
          rw [h1, Nat.mul_add_div h2k_pos, Nat.div_eq_of_lt hi1, Nat.add_zero]
        exact ⟨hqa.trans hqb.symm, Or.inl (by omega)⟩
      · have := v.isLt; omega
    · rcases hbr with ⟨_, hau⟩ | ⟨hi1, ha⟩ | ⟨_, hav⟩
      · have := u.isLt; omega
      · have hdb := subdiv285_div_mod u.val hk v.isLt i.isLt
        have hda := subdiv285_div_mod u.val hk v.isLt hi1
        have ha' : a.val = m + 2 * k * (u.val * m + v.val) + (i.val + 1) := by omega
        rw [← hb] at hdb
        rw [← ha'] at hda
        have hqa : (a.val - m) / (2 * k) = u.val * m + v.val := by
          have h1 : a.val - m = 2 * k * (u.val * m + v.val) + (i.val + 1) := by omega
          rw [h1, Nat.mul_add_div h2k_pos, Nat.div_eq_of_lt hi1, Nat.add_zero]
        have hqb : (b.val - m) / (2 * k) = u.val * m + v.val := by
          have h1 : b.val - m = 2 * k * (u.val * m + v.val) + i.val := by omega
          rw [h1, Nat.mul_add_div h2k_pos, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
        exact ⟨hqa.trans hqb.symm, Or.inr (by omega)⟩
      · have := v.isLt; omega
  have horig_int_adj : ∀ a b : Fin (m + 2 * k * m * m),
      a.val < m → m ≤ b.val → S.Adj a b →
      ∃ u v : Fin m, u < v ∧
        ((a.val = u.val ∧ b.val = m + 2 * k * (u.val * m + v.val)) ∨
          (a.val = v.val ∧ b.val = m + 2 * k * (u.val * m + v.val) + (2 * k - 1))) := by
    intro a b ha hb hab
    rcases ((hS_adj a b).mp hab).2 with ⟨u, v, huv, _, i, hax, _⟩ | ⟨u, v, huv, _, i, hbx, hbr⟩
    · omega
    · rcases hbr with ⟨hi0, hau⟩ | ⟨_, ha_ge⟩ | ⟨hitop, hav⟩
      · exact ⟨u, v, huv, Or.inl ⟨hau, by omega⟩⟩
      · omega
      · exact ⟨u, v, huv, Or.inr ⟨hav, by omega⟩⟩
  have hR_lip : ∀ (x a b : Fin (m + 2 * k * m * m)), R a b →
      subdiv285Phi m k x b ≤ subdiv285Phi m k x a + 1 ∧
      subdiv285Phi m k x a ≤ subdiv285Phi m k x b + 1 := by
    rintro x a b ⟨ua, va, huava, _, i, ha_eq, hbr⟩
    have huava_ne : ua.val ≠ va.val := by
      have : ua.val < va.val := huava
      omega
    have hdm_a := subdiv285_div_mod ua.val hk va.isLt i.isLt
    rw [← ha_eq] at hdm_a
    have hphi_a : subdiv285Phi m k x a =
        if ua.val = x.val then i.val + 1
        else if va.val = x.val then 2 * k - i.val
        else 2 * k + 1 := by
      unfold subdiv285Phi
      have ha_ge : ¬ a.val < m := by omega
      rw [if_neg ha_ge]
      simp only [hdm_a.1, hdm_a.2.1, hdm_a.2.2]
    rcases hbr with ⟨hi0, hb_eq⟩ | ⟨hi1, hb_eq⟩ | ⟨hi2, hb_eq⟩
    · have hphi_b : subdiv285Phi m k x b =
          if ua.val = x.val then 0 else 2 * k + 1 := by
        unfold subdiv285Phi
        have hb_lt : b.val < m := by omega
        rw [if_pos hb_lt, hb_eq]
      rw [hphi_a, hphi_b]
      split_ifs <;> omega
    · have hdm_b := subdiv285_div_mod ua.val hk va.isLt hi1
      have hb_eq' : b.val = m + 2 * k * (ua.val * m + va.val) + (i.val + 1) := by omega
      rw [← hb_eq'] at hdm_b
      have hphi_b : subdiv285Phi m k x b =
          if ua.val = x.val then i.val + 2
          else if va.val = x.val then 2 * k - (i.val + 1)
          else 2 * k + 1 := by
        unfold subdiv285Phi
        have hb_ge : ¬ b.val < m := by omega
        rw [if_neg hb_ge]
        simp only [hdm_b.1, hdm_b.2.1, hdm_b.2.2]
      rw [hphi_a, hphi_b]
      split_ifs <;> omega
    · have hphi_b : subdiv285Phi m k x b =
          if va.val = x.val then 0 else 2 * k + 1 := by
        unfold subdiv285Phi
        have hb_lt : b.val < m := by omega
        rw [if_pos hb_lt, hb_eq]
      rw [hphi_a, hphi_b]
      split_ifs <;> omega
  have hstep_phi : ∀ (x a b : Fin (m + 2 * k * m * m)), S.Adj a b →
      subdiv285Phi m k x b ≤ subdiv285Phi m k x a + 1 := by
    intro x a b hab
    rcases ((hS_adj a b).mp hab).2 with h1 | h2
    · exact (hR_lip x a b h1).1
    · exact (hR_lip x b a h2).2
  have hdist_arc : ∀ (a d : ℕ), a < L →
      subdiv285Phi m k (c a) (c ((a + d) % L)) ≤ subdiv285Phi m k (c a) (c a) + d := by
    intro a d ha
    induction d with
    | zero =>
      simp [Nat.mod_eq_of_lt ha]
    | succ d ih =>
      have hmod_lt : (a + d) % L < L := Nat.mod_lt _ (by omega)
      have hnext : ((a + d) % L + 1) % L = (a + (d + 1)) % L := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
      have hadj := hc_adj ((a + d) % L) hmod_lt
      rw [hnext] at hadj
      have h1 := hstep_phi (c a) (c ((a + d) % L)) (c ((a + (d + 1)) % L)) hadj
      omega
  have hdist_orig : ∀ (a d : ℕ), a < L → (c a).val < m → (c ((a + d) % L)).val < m →
      c a ≠ c ((a + d) % L) → 2 * k + 1 ≤ d := by
    intro a d ha hca hcb hne
    have h1 := hdist_arc a d ha
    have hpa : subdiv285Phi m k (c a) (c a) = 0 := by
      unfold subdiv285Phi
      rw [if_pos hca, if_pos rfl]
    have hpb : subdiv285Phi m k (c a) (c ((a + d) % L)) = 2 * k + 1 := by
      unfold subdiv285Phi
      have hne_val : (c ((a + d) % L)).val ≠ (c a).val := fun h => hne (Fin.ext h).symm
      rw [if_pos hcb, if_neg hne_val]
    omega
  have harc_unique : ∀ (f : ℕ → Fin (m + 2 * k * m * m)) (d : ℕ),
      1 ≤ d →
      (f 0 ≠ f d ∨ 3 ≤ d) →
      (∀ i j, i < d → j < d → f i = f j → i = j) →
      (∀ i, i < d → S.Adj (f i) (f (i + 1))) →
      (f 0).val < m → (f d).val < m →
      (∀ i, 1 ≤ i → i < d → m ≤ (f i).val) →
      f 0 ≠ f d ∧
      ((f 0).val < (f d).val ∧ (f 1).val = m + 2 * k * ((f 0).val * m + (f d).val) ∨
        (f d).val < (f 0).val ∧ (f 1).val = m + 2 * k * ((f d).val * m + (f 0).val) + (2 * k - 1)) := by
    intro f d hd1 hne_or hf_inj hf_adj hf0 hfd hf_int
    have hd2 : 2 ≤ d := by
      by_contra hlt
      have hd_eq : d = 1 := by omega
      subst hd_eq
      exact hno_orig_adj (f 0) (f 1) hf0 hfd (hf_adj 0 (by omega))
    rcases horig_int_adj (f 0) (f 1) hf0 (hf_int 1 (le_refl 1) (by omega)) (hf_adj 0 (by omega)) with
      ⟨u, v, huv, ⟨hf0u, hf1eq⟩ | ⟨hf0v, hf1eq⟩⟩
    · have hchain : ∀ n r, r ≤ n → 1 ≤ r → r < d →
          (f r).val = m + 2 * k * (u.val * m + v.val) + (r - 1) ∧ r - 1 < 2 * k := by
        intro n
        induction n with
        | zero => intro r hr hr1; omega
        | succ n ih =>
          intro r hrn hr1 hrd
          by_cases hr1eq : r = 1
          · subst hr1eq
            exact ⟨by omega, by omega⟩
          · have ⟨hprev, hprev_lt⟩ := ih (r - 1) (by omega) (by omega) (by omega)
            have hadj := hf_adj (r - 1) (by omega)
            have hr_eq : r - 1 + 1 = r := by omega
            rw [hr_eq] at hadj
            have ⟨hq, hrem⟩ := hstep_internal (f (r - 1)) (f r)
              (hf_int (r - 1) (by omega) (by omega)) (hf_int r hr1 hrd) hadj
            have hqa : (f (r - 1)).val - m = 2 * k * (u.val * m + v.val) + (r - 2) := by omega
            have hdiva : ((f (r - 1)).val - m) / (2 * k) = u.val * m + v.val := by
              rw [hqa, Nat.mul_add_div h2k_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
            have hmoda : ((f (r - 1)).val - m) % (2 * k) = r - 2 := by
              rw [hqa, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
            have hdivb : ((f r).val - m) / (2 * k) = u.val * m + v.val := by omega
            have hremb : ((f r).val - m) % (2 * k) < 2 * k := Nat.mod_lt _ h2k_pos
            have hdecomp : 2 * k * (((f r).val - m) / (2 * k)) +
                ((f r).val - m) % (2 * k) = (f r).val - m :=
              Nat.div_add_mod _ _
            have hfm_ge := hf_int r hr1 hrd
            rcases hrem with hinc | hdec
            · rw [hdivb] at hdecomp
              exact ⟨by omega, by omega⟩
            · exfalso
              by_cases hr2 : r = 2
              · omega
              · have ⟨hprev2, _⟩ := ih (r - 2) (by omega) (by omega) (by omega)
                rw [hdivb] at hdecomp
                have heq_f : f r = f (r - 2) := Fin.ext (by omega)
                have := hf_inj r (r - 2) hrd (by omega) heq_f
                omega
      have ⟨hlast, hlast_lt⟩ := hchain (d - 1) (d - 1) (le_refl _) (by omega) (by omega)
      have hadj_end : S.Adj (f d) (f (d - 1)) := by
        have h1 := hf_adj (d - 1) (by omega)
        have hd_eq : d - 1 + 1 = d := by omega
        rw [hd_eq] at h1
        exact S.symm.symm _ _ h1
      rcases horig_int_adj (f d) (f (d - 1)) hfd (hf_int (d - 1) (by omega) (by omega)) hadj_end with
        ⟨u', v', huv', ⟨hfdu', hlast'⟩ | ⟨hfdv', hlast'⟩⟩
      · have hdm1 := subdiv285_div_mod u.val hk v.isLt hlast_lt
        have hdm2 := subdiv285_div_mod u'.val hk v'.isLt (i := 0) h2k_pos
        have hlast_eq : m + 2 * k * (u.val * m + v.val) + (d - 1 - 1) =
            m + 2 * k * (u'.val * m + v'.val) + 0 := by omega
        rw [hlast_eq] at hdm1
        have hu_eq : u.val = u'.val := hdm1.1.symm.trans hdm2.1
        have hrem_eq : d - 1 - 1 = 0 := hdm1.2.2.symm.trans hdm2.2.2
        have hfd_eq : f 0 = f d := Fin.ext (by omega)
        rcases hne_or with hne | hd3
        · exact False.elim (hne hfd_eq)
        · omega
      · have hdm1 := subdiv285_div_mod u.val hk v.isLt hlast_lt
        have hdm2 := subdiv285_div_mod u'.val hk v'.isLt (i := 2 * k - 1) (by omega)
        have hlast_eq : m + 2 * k * (u.val * m + v.val) + (d - 1 - 1) =
            m + 2 * k * (u'.val * m + v'.val) + (2 * k - 1) := by omega
        rw [hlast_eq] at hdm1
        have hu_eq : u.val = u'.val := hdm1.1.symm.trans hdm2.1
        have hv_eq : v.val = v'.val := hdm1.2.1.symm.trans hdm2.2.1
        have huv_lt : u.val < v.val := huv
        refine ⟨fun heq => by have := congrArg Fin.val heq; omega,
          Or.inl ⟨by omega, by rw [hf0u, hfdv', ← hv_eq]; exact hf1eq⟩⟩
    · have hchain : ∀ n r, r ≤ n → 1 ≤ r → r < d →
          (f r).val = m + 2 * k * (u.val * m + v.val) + (2 * k - r) ∧ r ≤ 2 * k := by
        intro n
        induction n with
        | zero => intro r hr hr1; omega
        | succ n ih =>
          intro r hrn hr1 hrd
          by_cases hr1eq : r = 1
          · subst hr1eq
            exact ⟨by omega, by omega⟩
          · have ⟨hprev, hprev_le⟩ := ih (r - 1) (by omega) (by omega) (by omega)
            have hadj := hf_adj (r - 1) (by omega)
            have hr_eq : r - 1 + 1 = r := by omega
            rw [hr_eq] at hadj
            have ⟨hq, hrem⟩ := hstep_internal (f (r - 1)) (f r)
              (hf_int (r - 1) (by omega) (by omega)) (hf_int r hr1 hrd) hadj
            have hqa : (f (r - 1)).val - m = 2 * k * (u.val * m + v.val) + (2 * k - (r - 1)) := by omega
            have hdiva : ((f (r - 1)).val - m) / (2 * k) = u.val * m + v.val := by
              rw [hqa, Nat.mul_add_div h2k_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
            have hmoda : ((f (r - 1)).val - m) % (2 * k) = 2 * k - (r - 1) := by
              rw [hqa, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
            have hdivb : ((f r).val - m) / (2 * k) = u.val * m + v.val := by omega
            have hremb : ((f r).val - m) % (2 * k) < 2 * k := Nat.mod_lt _ h2k_pos
            have hdecomp : 2 * k * (((f r).val - m) / (2 * k)) +
                ((f r).val - m) % (2 * k) = (f r).val - m :=
              Nat.div_add_mod _ _
            have hfm_ge := hf_int r hr1 hrd
            rcases hrem with hinc | hdec
            · exfalso
              by_cases hr2 : r = 2
              · omega
              · have ⟨hprev2, _⟩ := ih (r - 2) (by omega) (by omega) (by omega)
                rw [hdivb] at hdecomp
                have heq_f : f r = f (r - 2) := Fin.ext (by omega)
                have := hf_inj r (r - 2) hrd (by omega) heq_f
                omega
            · rw [hdivb] at hdecomp
              exact ⟨by omega, by omega⟩
      have ⟨hlast, hlast_le⟩ := hchain (d - 1) (d - 1) (le_refl _) (by omega) (by omega)
      have hadj_end : S.Adj (f d) (f (d - 1)) := by
        have h1 := hf_adj (d - 1) (by omega)
        have hd_eq : d - 1 + 1 = d := by omega
        rw [hd_eq] at h1
        exact S.symm.symm _ _ h1
      rcases horig_int_adj (f d) (f (d - 1)) hfd (hf_int (d - 1) (by omega) (by omega)) hadj_end with
        ⟨u', v', huv', ⟨hfdu', hlast'⟩ | ⟨hfdv', hlast'⟩⟩
      · have hdm1 := subdiv285_div_mod u.val hk v.isLt (i := 2 * k - (d - 1)) (by omega)
        have hdm2 := subdiv285_div_mod u'.val hk v'.isLt (i := 0) h2k_pos
        have hlast_eq : m + 2 * k * (u.val * m + v.val) + (2 * k - (d - 1)) =
            m + 2 * k * (u'.val * m + v'.val) + 0 := by omega
        rw [hlast_eq] at hdm1
        have hu_eq : u.val = u'.val := hdm1.1.symm.trans hdm2.1
        have hv_eq : v.val = v'.val := hdm1.2.1.symm.trans hdm2.2.1
        have huv_lt : u.val < v.val := huv
        refine ⟨fun heq => by have := congrArg Fin.val heq; omega,
          Or.inr ⟨by omega, by rw [hf0v, hfdu', ← hu_eq]; exact hf1eq⟩⟩
      · have hdm1 := subdiv285_div_mod u.val hk v.isLt (i := 2 * k - (d - 1)) (by omega)
        have hdm2 := subdiv285_div_mod u'.val hk v'.isLt (i := 2 * k - 1) (by omega)
        have hlast_eq : m + 2 * k * (u.val * m + v.val) + (2 * k - (d - 1)) =
            m + 2 * k * (u'.val * m + v'.val) + (2 * k - 1) := by omega
        rw [hlast_eq] at hdm1
        have hv_eq : v.val = v'.val := hdm1.2.1.symm.trans hdm2.2.1
        have hrem_eq : 2 * k - (d - 1) = 2 * k - 1 := hdm1.2.2.symm.trans hdm2.2.2
        have hfd_eq : f 0 = f d := Fin.ext (by omega)
        rcases hne_or with hne | hd3
        · exact False.elim (hne hfd_eq)
        · omega
  let Orig : Finset ℕ := (Finset.range L).filter fun t => (c t).val < m
  have hOrig_ge3 : 3 ≤ Orig.card := by
    by_contra hlt3
    by_cases h0 : Orig.card = 0
    · have hall_int : ∀ t < L, m ≤ (c t).val := by
        intro t ht
        by_contra hlt
        have hmem : t ∈ Orig := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, by omega⟩
        have := Finset.card_pos.mpr ⟨t, hmem⟩
        omega
      have hne_rng : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
      rcases Finset.exists_min_image (Finset.range L) (fun t => ((c t).val - m) % (2 * k)) hne_rng with
        ⟨t0, ht0_mem, ht0_min⟩
      have ht0 : t0 < L := Finset.mem_range.mp ht0_mem
      let t1 := (t0 + 1) % L
      let t2 := (t0 + L - 1) % L
      have ht1 : t1 < L := Nat.mod_lt _ (by omega)
      have ht2 : t2 < L := Nat.mod_lt _ (by omega)
      have ht12_ne : t1 ≠ t2 := by
        intro heq
        have h1 : t1 = if t0 + 1 < L then t0 + 1 else t0 + 1 - L :=
          mod_add_lt_eq ht0 (by omega)
        have h2 : t2 = if 1 ≤ t0 then t0 - 1 else t0 + L - 1 :=
          mod_add_sub_lt_eq ht0 (by omega) (by omega)
        split_ifs at h1 h2 <;> omega
      have hadj1 : S.Adj (c t0) (c t1) := hc_adj t0 ht0
      have hadj2 : S.Adj (c t0) (c t2) := by
        have h := hc_adj t2 ht2
        have hnext : (t2 + 1) % L = t0 := by
          show ((t0 + L - 1) % L + 1) % L = t0
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : t0 + L - 1 + 1 = t0 + L := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ht0]
        rw [hnext] at h
        exact S.symm.symm _ _ h
      have ⟨hq1, hr1⟩ := hstep_internal (c t0) (c t1) (hall_int t0 ht0) (hall_int t1 ht1) hadj1
      have ⟨hq2, hr2⟩ := hstep_internal (c t0) (c t2) (hall_int t0 ht0) (hall_int t2 ht2) hadj2
      have hmin1 := ht0_min t1 (Finset.mem_range.mpr ht1)
      have hmin2 := ht0_min t2 (Finset.mem_range.mpr ht2)
      have hr1_eq : ((c t1).val - m) % (2 * k) = ((c t0).val - m) % (2 * k) + 1 := by omega
      have hr2_eq : ((c t2).val - m) % (2 * k) = ((c t0).val - m) % (2 * k) + 1 := by omega
      have hd1 := Nat.div_add_mod ((c t1).val - m) (2 * k)
      have hd2 := Nat.div_add_mod ((c t2).val - m) (2 * k)
      have hm1 := hall_int t1 ht1
      have hm2 := hall_int t2 ht2
      have hq12 : ((c t1).val - m) / (2 * k) = ((c t2).val - m) / (2 * k) := hq1.symm.trans hq2
      rw [hq12] at hd1
      have hceq : c t1 = c t2 := Fin.ext (by omega)
      exact ht12_ne (hc_inj t1 t2 ht1 ht2 hceq)
    · by_cases h1 : Orig.card = 1
      · rcases Finset.card_eq_one.mp h1 with ⟨t0, hOrig_eq⟩
        have ht0_mem : t0 ∈ Orig := by rw [hOrig_eq]; exact Finset.mem_singleton_self t0
        have ht0 : t0 < L := Finset.mem_range.mp (Finset.mem_filter.mp ht0_mem).1
        have hct0 : (c t0).val < m := (Finset.mem_filter.mp ht0_mem).2
        let f : ℕ → Fin (m + 2 * k * m * m) := fun r => c ((t0 + r) % L)
        have hf0L : f 0 = f L := by
          simp [f, Nat.add_mod_right]
        have ⟨hne, _⟩ := harc_unique f L (by omega) (Or.inr hL3)
          (by
            intro i j hi hj heq
            have hmod := hc_inj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) heq
            have hmi := mod_add_lt_eq ht0 hi
            have hmj := mod_add_lt_eq ht0 hj
            split_ifs at hmi hmj <;> omega)
          (by
            intro i hi
            have hnext : ((t0 + i) % L + 1) % L = (t0 + (i + 1)) % L := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
            have hadj := hc_adj ((t0 + i) % L) (Nat.mod_lt _ (by omega))
            rwa [hnext] at hadj)
          (by simpa [f, Nat.mod_eq_of_lt ht0] using hct0)
          (by simpa [f, Nat.add_mod_right, Nat.mod_eq_of_lt ht0] using hct0)
          (by
            intro i hi1 hiL
            by_contra hlt
            dsimp [f] at hlt
            have hmem : (t0 + i) % L ∈ Orig :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), by omega⟩
            rw [hOrig_eq, Finset.mem_singleton] at hmem
            have hmi := mod_add_lt_eq ht0 hiL
            split_ifs at hmi <;> omega)
        exact hne hf0L
      · have h2 : Orig.card = 2 := by omega
        rcases Finset.card_eq_two.mp h2 with ⟨t0, t1, ht01, hOrig_eq⟩
        have ht0_mem : t0 ∈ Orig := by rw [hOrig_eq]; simp
        have ht1_mem : t1 ∈ Orig := by rw [hOrig_eq]; simp
        have ht0 : t0 < L := Finset.mem_range.mp (Finset.mem_filter.mp ht0_mem).1
        have ht1 : t1 < L := Finset.mem_range.mp (Finset.mem_filter.mp ht1_mem).1
        have hct0 : (c t0).val < m := (Finset.mem_filter.mp ht0_mem).2
        have hct1 : (c t1).val < m := (Finset.mem_filter.mp ht1_mem).2
        let d1 : ℕ := if t0 < t1 then t1 - t0 else L + t1 - t0
        let d2 : ℕ := L - d1
        have hd1_pos : 1 ≤ d1 := by dsimp [d1]; split_ifs <;> omega
        have hd1_lt : d1 < L := by dsimp [d1]; split_ifs <;> omega
        have hd2_pos : 1 ≤ d2 := by omega
        have hd1_end : (t0 + d1) % L = t1 := by
          dsimp [d1]
          split_ifs
          · have : t0 + (t1 - t0) = t1 := by omega
            rw [this, Nat.mod_eq_of_lt ht1]
          · have : t0 + (L + t1 - t0) = t1 + L := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ht1]
        have hct01_ne : c t0 ≠ c t1 := fun h => ht01 (hc_inj t0 t1 ht0 ht1 h)
        let f1 : ℕ → Fin (m + 2 * k * m * m) := fun r => c ((t0 + r) % L)
        let f2 : ℕ → Fin (m + 2 * k * m * m) := fun r => c ((t0 + L - r) % L)
        have hres1 := harc_unique f1 d1 hd1_pos
          (Or.inl (by simpa [f1, Nat.mod_eq_of_lt ht0, hd1_end] using hct01_ne))
          (by
            intro i j hi hj heq
            have hmod := hc_inj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) heq
            have hmi := mod_add_lt_eq ht0 (lt_trans hi hd1_lt)
            have hmj := mod_add_lt_eq ht0 (lt_trans hj hd1_lt)
            split_ifs at hmi hmj <;> omega)
          (by
            intro i hi
            have hnext : ((t0 + i) % L + 1) % L = (t0 + (i + 1)) % L := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
            have hadj := hc_adj ((t0 + i) % L) (Nat.mod_lt _ (by omega))
            rwa [hnext] at hadj)
          (by simpa [f1, Nat.mod_eq_of_lt ht0] using hct0)
          (by simpa [f1, hd1_end] using hct1)
          (by
            intro i hi1 hid1
            by_contra hlt
            dsimp [f1] at hlt
            have hmem : (t0 + i) % L ∈ Orig :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), by omega⟩
            rw [hOrig_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
            have hmi := mod_add_lt_eq ht0 (lt_trans hid1 hd1_lt)
            dsimp [d1] at hid1
            rcases hmem with hm0 | hm1 <;> split_ifs at hmi hid1 <;> omega)
        have hd2_end : (t0 + L - d2) % L = t1 := by
          have : t0 + L - d2 = t0 + d1 := by omega
          rw [this, hd1_end]
        have hres2 := harc_unique f2 d2 hd2_pos
          (Or.inl (by simpa [f2, Nat.add_mod_right, Nat.mod_eq_of_lt ht0, hd2_end] using hct01_ne))
          (by
            intro i j hi hj heq
            have hmod := hc_inj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) heq
            by_cases hi0 : i = 0
            · by_cases hj0 : j = 0
              · omega
              · have hmi : (t0 + L - i) % L = t0 := by
                  rw [hi0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt ht0]
                have hmj := mod_add_sub_lt_eq ht0 (by omega : j ≤ L) (by omega : 0 < j)
                split_ifs at hmj <;> omega
            · by_cases hj0 : j = 0
              · have hmj : (t0 + L - j) % L = t0 := by
                  rw [hj0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt ht0]
                have hmi := mod_add_sub_lt_eq ht0 (by omega : i ≤ L) (by omega : 0 < i)
                split_ifs at hmi <;> omega
              · have hmi := mod_add_sub_lt_eq ht0 (by omega : i ≤ L) (by omega : 0 < i)
                have hmj := mod_add_sub_lt_eq ht0 (by omega : j ≤ L) (by omega : 0 < j)
                split_ifs at hmi hmj <;> omega)
          (by
            intro i hi
            have hnext : ((t0 + L - (i + 1)) % L + 1) % L = (t0 + L - i) % L := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have : t0 + L - (i + 1) + 1 = t0 + L - i := by omega
              rw [this]
            have hadj := hc_adj ((t0 + L - (i + 1)) % L) (Nat.mod_lt _ (by omega))
            rw [hnext] at hadj
            exact S.symm.symm _ _ hadj)
          (by simpa [f2, Nat.add_mod_right, Nat.mod_eq_of_lt ht0] using hct0)
          (by simpa [f2, hd2_end] using hct1)
          (by
            intro i hi1 hid2
            by_contra hlt
            dsimp [f2] at hlt
            have hmem : (t0 + L - i) % L ∈ Orig :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), by omega⟩
            rw [hOrig_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
            have hmi := mod_add_sub_lt_eq ht0 (by omega : i ≤ L) (by omega : 0 < i)
            dsimp [d2, d1] at hid2
            rcases hmem with hm0 | hm1 <;> split_ifs at hmi hid2 <;> omega)
        have hf10 : f1 0 = c t0 := by simp [f1, Nat.mod_eq_of_lt ht0]
        have hf1d : f1 d1 = c t1 := by simp [f1, hd1_end]
        have hf20 : f2 0 = c t0 := by simp [f2, Nat.add_mod_right, Nat.mod_eq_of_lt ht0]
        have hf2d : f2 d2 = c t1 := by simp [f2, hd2_end]
        rw [hf10, hf1d] at hres1
        rw [hf20, hf2d] at hres2
        have hf12_eq : f1 1 = f2 1 := by
          apply Fin.ext
          rcases hres1.2 with ⟨hlt1, heq1⟩ | ⟨hgt1, heq1⟩ <;>
            rcases hres2.2 with ⟨hlt2, heq2⟩ | ⟨hgt2, heq2⟩ <;> omega
        have hidx_eq := hc_inj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hf12_eq
        have h1 := mod_add_lt_eq ht0 (by omega : 1 < L)
        have h2' := mod_add_sub_lt_eq ht0 (by omega : 1 ≤ L) (by omega : 0 < 1)
        split_ifs at h1 h2' <;> omega
  have hex3 : ∃ a b e, a ∈ Orig ∧ b ∈ Orig ∧ e ∈ Orig ∧ a < b ∧ b < e := by
    have hgt2 : 2 < Orig.card := by omega
    rcases Finset.two_lt_card.mp hgt2 with ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
    rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
      rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
      rcases lt_or_gt_of_ne hyz with h3 | h3
    · exact ⟨x, y, z, hx, hy, hz, h1, h3⟩
    · exact ⟨x, z, y, hx, hz, hy, h2, h3⟩
    · omega
    · exact ⟨z, x, y, hz, hx, hy, h2, h1⟩
    · exact ⟨y, x, z, hy, hx, hz, h1, h2⟩
    · omega
    · exact ⟨y, z, x, hy, hz, hx, h3, h2⟩
    · exact ⟨z, y, x, hz, hy, hx, h3, h1⟩
  rcases hex3 with ⟨a, b, e, ha, hb, he, hab, hbe⟩
  have ha_lt : a < L := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hb_lt : b < L := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have he_lt : e < L := Finset.mem_range.mp (Finset.mem_filter.mp he).1
  have hca : (c a).val < m := (Finset.mem_filter.mp ha).2
  have hcb : (c b).val < m := (Finset.mem_filter.mp hb).2
  have hce : (c e).val < m := (Finset.mem_filter.mp he).2
  have hd_ab : 2 * k + 1 ≤ b - a := by
    have hmod : (a + (b - a)) % L = b := by
      have : a + (b - a) = b := by omega
      rw [this, Nat.mod_eq_of_lt hb_lt]
    apply hdist_orig a (b - a) ha_lt hca (by rw [hmod]; exact hcb)
    rw [hmod]
    intro h; have := hc_inj a b ha_lt hb_lt h; omega
  have hd_be : 2 * k + 1 ≤ e - b := by
    have hmod : (b + (e - b)) % L = e := by
      have : b + (e - b) = e := by omega
      rw [this, Nat.mod_eq_of_lt he_lt]
    apply hdist_orig b (e - b) hb_lt hcb (by rw [hmod]; exact hce)
    rw [hmod]
    intro h; have := hc_inj b e hb_lt he_lt h; omega
  have hd_ea : 2 * k + 1 ≤ L - e + a := by
    have hmod : (e + (L - e + a)) % L = a := by
      have : e + (L - e + a) = a + L := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha_lt]
    apply hdist_orig e (L - e + a) he_lt hce (by rw [hmod]; exact hca)
    rw [hmod]
    intro h; have := hc_inj e a he_lt ha_lt h; omega
  omega

end PEqualNP.Outside
