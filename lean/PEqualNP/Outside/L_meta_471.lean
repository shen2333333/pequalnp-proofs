import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Lift471

private theorem mul_add_inj {d a b i j : ℕ} (hi : i < d) (hj : j < d)
    (h : d * a + i = d * b + j) : a = b ∧ i = j := by
  have hab : a = b := by
    rcases lt_trichotomy a b with hab | hab | hba
    · have hmul := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hab)
      simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
      omega
    · exact hab
    · have hmul := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hba)
      simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
      omega
  subst b
  exact ⟨rfl, Nat.add_left_cancel h⟩

private theorem internal_lt {m k : ℕ} (u v : Fin m) {i : ℕ} (hi : i < 2 * k) :
    m + 2 * k * (u.val * m + v.val) + i < m + 2 * k * (m * m) := by
  have hu : u.val + 1 ≤ m := u.isLt
  have hv : v.val < m := v.isLt
  have huv : u.val * m + v.val + 1 ≤ m * m := by
    calc
      u.val * m + v.val + 1 ≤ u.val * m + m := by omega
      _ = (u.val + 1) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right m hu
  calc
    m + 2 * k * (u.val * m + v.val) + i <
        m + 2 * k * (u.val * m + v.val) + 2 * k := by omega
    _ = m + 2 * k * (u.val * m + v.val + 1) := by ring
    _ ≤ m + 2 * k * (m * m) := Nat.add_le_add_left (Nat.mul_le_mul_left _ huv) _

end PEqualNP.Outside.Lift471

theorem PEqualNP.Outside.L_meta_471 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → ∀ x ∈ T', ∃ y : Fin (m + 2 * k * (m * m)), S.Adj x y ∧ y ∉ T' := by
  classical
  intro m k H Q S hk hQ hS T T' hcover houtside hT' x hx
  rcases (hT' x).1 hx with horiginal | hinternal
  · obtain ⟨u, hu, hxu⟩ := horiginal
    obtain ⟨w, huw, hw⟩ := houtside u hu
    by_cases hlt : u < w
    · have hi : 0 < 2 * k := by omega
      let y : Fin (m + 2 * k * (m * m)) :=
        ⟨m + 2 * k * (u.val * m + w.val), PEqualNP.Outside.Lift471.internal_lt u w hi⟩
      refine ⟨y, ?_, ?_⟩
      · apply (hS x y).2
        refine ⟨u, w, hlt, huw, 0, by omega, Or.inl ⟨?_, ?_⟩⟩
        · apply (hQ u w 0 x).2
          exact Or.inl ⟨rfl, hxu⟩
        · apply (hQ u w 1 y).2
          refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
          simp [y]
      · intro hy
        rcases (hT' y).1 hy with hyoriginal | hyinternal
        · obtain ⟨z, hz, hyz⟩ := hyoriginal
          have hzlt := z.isLt
          simp only [y] at hyz
          omega
        · obtain ⟨a, b, i, hi, hab, hEdge, hyval, hparity⟩ := hyinternal
          have henc : 2 * k * (a.val * m + b.val) + i =
              2 * k * (u.val * m + w.val) + 0 := by
            simp only [y] at hyval
            omega
          obtain ⟨hblock, hi0⟩ :=
            PEqualNP.Outside.Lift471.mul_add_inj hi (by omega : 0 < 2 * k) henc
          have hpair : m * a.val + b.val = m * u.val + w.val := by
            simpa only [Nat.mul_comm m] using hblock
          obtain ⟨hau, hbw⟩ := PEqualNP.Outside.Lift471.mul_add_inj b.isLt w.isLt hpair
          have hae : a = u := Fin.ext hau
          subst a
          subst i
          have ha : u ∉ T := by simpa using hparity
          exact ha hu
    · have hwu : w < u := lt_of_le_of_ne (le_of_not_gt hlt) huw.ne.symm
      have hi : 2 * k - 1 < 2 * k := by omega
      let y : Fin (m + 2 * k * (m * m)) :=
        ⟨m + 2 * k * (w.val * m + u.val) + (2 * k - 1),
          PEqualNP.Outside.Lift471.internal_lt w u hi⟩
      refine ⟨y, ?_, ?_⟩
      · apply (hS x y).2
        refine ⟨w, u, hwu, huw.symm, 2 * k, le_rfl, Or.inr ⟨?_, ?_⟩⟩
        · apply (hQ w u (2 * k) y).2
          refine Or.inr (Or.inr ⟨by omega, le_rfl, ?_⟩)
          simp only [y]
          omega
        · apply (hQ w u (2 * k + 1) x).2
          exact Or.inr (Or.inl ⟨rfl, hxu⟩)
      · intro hy
        rcases (hT' y).1 hy with hyoriginal | hyinternal
        · obtain ⟨z, hz, hyz⟩ := hyoriginal
          have hzlt := z.isLt
          simp only [y] at hyz
          omega
        · obtain ⟨a, b, i, hi', hab, hEdge, hyval, hparity⟩ := hyinternal
          have henc : 2 * k * (a.val * m + b.val) + i =
              2 * k * (w.val * m + u.val) + (2 * k - 1) := by
            simp only [y] at hyval
            omega
          obtain ⟨hblock, hiLast⟩ :=
            PEqualNP.Outside.Lift471.mul_add_inj hi' hi henc
          have hpair : m * a.val + b.val = m * w.val + u.val := by
            simpa only [Nat.mul_comm m] using hblock
          obtain ⟨haw, hbu⟩ := PEqualNP.Outside.Lift471.mul_add_inj b.isLt u.isLt hpair
          have hae : a = w := Fin.ext haw
          subst a
          subst i
          have hodd : (2 * k - 1) % 2 = 1 := by omega
          exact hw (hparity.1 hodd)
  · obtain ⟨u, v, i, hi, huv, hEdge, hxval, hparity⟩ := hinternal
    by_cases hi0 : i = 0
    · subst i
      have huNot : u ∉ T := by simpa using hparity
      let y : Fin (m + 2 * k * (m * m)) := ⟨u.val, by have := u.isLt; omega⟩
      refine ⟨y, ?_, ?_⟩
      · apply (hS x y).2
        refine ⟨u, v, huv, hEdge, 0, by omega, Or.inr ⟨?_, ?_⟩⟩
        · apply (hQ u v 0 y).2
          exact Or.inl ⟨rfl, rfl⟩
        · apply (hQ u v 1 x).2
          refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
          omega
      · intro hy
        rcases (hT' y).1 hy with hyoriginal | hyinternal
        · obtain ⟨z, hz, hyz⟩ := hyoriginal
          have hzu : z = u := Fin.ext (by simpa only [y] using hyz.symm)
          subst z
          exact huNot hz
        · obtain ⟨a, b, j, hj, hab, hEdge', hyval, hparity'⟩ := hyinternal
          have halt := a.isLt
          simp only [y] at hyval
          omega
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hipred : i - 1 < 2 * k := by omega
      let y : Fin (m + 2 * k * (m * m)) :=
        ⟨m + 2 * k * (u.val * m + v.val) + (i - 1),
          PEqualNP.Outside.Lift471.internal_lt u v hipred⟩
      refine ⟨y, ?_, ?_⟩
      · apply (hS x y).2
        refine ⟨u, v, huv, hEdge, i, by omega, Or.inr ⟨?_, ?_⟩⟩
        · apply (hQ u v i y).2
          refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
          simp only [y]
          omega
        · apply (hQ u v (i + 1) x).2
          refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
          omega
      · intro hy
        rcases (hT' y).1 hy with hyoriginal | hyinternal
        · obtain ⟨z, hz, hyz⟩ := hyoriginal
          have hzlt := z.isLt
          simp only [y] at hyz
          omega
        · obtain ⟨a, b, j, hj, hab, hEdge', hyval, hparity'⟩ := hyinternal
          have henc : 2 * k * (a.val * m + b.val) + j =
              2 * k * (u.val * m + v.val) + (i - 1) := by
            simp only [y] at hyval
            omega
          obtain ⟨hblock, hji⟩ := PEqualNP.Outside.Lift471.mul_add_inj hj hipred henc
          have hpair : m * a.val + b.val = m * u.val + v.val := by
            simpa only [Nat.mul_comm m] using hblock
          obtain ⟨hau, hbv⟩ := PEqualNP.Outside.Lift471.mul_add_inj b.isLt v.isLt hpair
          have hae : a = u := Fin.ext hau
          have hbe : b = v := Fin.ext hbv
          subst a
          subst b
          subst j
          by_cases hu : u ∈ T
          · have hodd := hparity.2 hu
            have hodd' := hparity'.2 hu
            omega
          · have heven : ¬i % 2 = 1 := fun h => hu (hparity.1 h)
            have heven' : ¬(i - 1) % 2 = 1 := fun h => hu (hparity'.1 h)
            omega
