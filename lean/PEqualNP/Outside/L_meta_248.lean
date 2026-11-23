import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_248 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → ∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → c L = c 0 → (∀ i : ℕ, i < L → E (c i) (c (i + 1))) → (∀ i j : ℕ, i < j → j < L → c i ≠ c j) → 2 * k + 1 ≤ L := by
  classical
  intro N k E pos hk ⟨hs, he, hd⟩ L c hL hc hedge hinj
  let S := (Finset.range L).image (fun i => pos (c i))
  have mem (i : ℕ) (hi : i < L) : pos (c i) ∈ S :=
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have step (n : ℕ) (hn : n ∈ S) (hn0 : n ≠ 0) :
      n - 1 ∈ S ∧ (n + 1) % (2 * k + 1) ∈ S := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have hiL := Finset.mem_range.mp hi
    let p := if i = 0 then L - 1 else i - 1
    let q := if i + 1 = L then 0 else i + 1
    have hp : p < L := by dsimp [p]; split <;> omega
    have hq : q < L := by dsimp [q]; split <;> omega
    have hpq : p ≠ q := by dsimp [p,q]; split_ifs <;> omega
    have hneq : c p ≠ c q := by
      rcases lt_or_gt_of_ne hpq with h | h
      · exact hinj _ _ h hq
      · exact (hinj _ _ h hp).symm
    have hep : E (c i) (c p) := by
      apply hs
      dsimp [p]
      split
      · next hz =>
          subst i
          simpa only [Nat.sub_add_cancel (show 1 ≤ L by omega), hc] using
            hedge (L-1) (by omega)
      · next hz =>
          simpa only [Nat.sub_add_cancel (show 1 ≤ i by omega)] using
            hedge (i-1) (by omega)
    have heq : E (c i) (c q) := by
      dsimp [q]
      split
      · next h => simpa only [h, hc] using hedge i hiL
      · exact hedge i hiL
    obtain ⟨_, a, b, hab, ha, hb⟩ := hd (c i) hn0
    have hm : pos a ∈ S ∧ pos b ∈ S := by
      rcases (hab _).mp hep with u | u <;> rcases (hab _).mp heq with v | v
      · exact (hneq (u.trans v.symm)).elim
      · exact ⟨u ▸ mem p hp, v ▸ mem q hq⟩
      · exact ⟨v ▸ mem q hq, u ▸ mem p hp⟩
      · exact (hneq (u.trans v.symm)).elim
    rw [← hb, show pos (c i) - 1 = pos a by omega]
    exact hm
  have descend : ∀ n : ℕ, n + 1 ∈ S → 1 ∈ S := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih =>
      intro h
      exact ih ((step _ h (by omega)).1)
  have getOne (n : ℕ) (hn : n ∈ S) (h : n ≠ 0) : 1 ∈ S := by
    cases n with
    | zero => contradiction
    | succ n => exact descend n hn
  have one : 1 ∈ S := by
    rcases he _ _ (hedge 0 (by omega)) with h | h
    · exact getOne _ (mem 0 (by omega)) h
    · exact getOne _ (mem 1 (by omega)) h
  have allpos : ∀ n : ℕ, n + 1 ≤ 2 * k → n + 1 ∈ S := by
    intro n
    induction n with
    | zero => exact fun _ => one
    | succ n ih =>
      intro hn
      have h := (step _ (ih (by omega)) (by omega)).2
      rwa [Nat.mod_eq_of_lt (by omega)] at h
  have sub : Finset.range (2 * k + 1) ⊆ S := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    cases n with
    | zero => exact (step _ one (by decide)).1
    | succ n => exact allpos n (by omega)
  have hcard := Finset.card_le_card sub
  have hsize : S.card ≤ (Finset.range L).card := Finset.card_image_le
  simpa using hcard.trans hsize
