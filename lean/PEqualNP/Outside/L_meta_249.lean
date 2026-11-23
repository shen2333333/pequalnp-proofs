import Mathlib.Data.Nat.Init
import Mathlib.Tactic.ByContra

namespace PEqualNP.Outside

private lemma shortWalkSameHub {N k : ℕ} {E : Fin N → Fin N → Prop}
    {pos : Fin N → ℕ} (hk : 1 ≤ k)
    (hsym : ∀ u v, E u v → E v u)
    (hnoHubEdge : ∀ u v, E u v → pos u ≠ 0 ∨ pos v ≠ 0)
    (hinner : ∀ v, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b,
      (∀ w, E v w ↔ w = a ∨ w = b) ∧
      pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1))
    (L : ℕ) (w : ℕ → Fin N) (hshort : L < 2 * k + 1)
    (hstart : pos (w 0) = 0) (hend : pos (w L) = 0)
    (hwalk : ∀ i, i < L → E (w i) (w (i + 1))) : w 0 = w L := by
  induction L using Nat.strong_induction_on generalizing w with
  | ind L ih =>
    by_contra hdistinct
    have hL : 0 < L := by
      by_contra h
      exact hdistinct (by rw [show L = 0 by omega])
    have hnoBacktrack : ∀ i, i + 1 < L → w i ≠ w (i + 2) := by
      intro i hi hbacktrack
      let shorter (j : ℕ) := if j ≤ i then w j else w (j + 2)
      have hfirst : shorter 0 = w 0 := by simp [shorter]
      have hlast : shorter (L - 2) = w L := by
        by_cases hle : L - 2 ≤ i
        · simp only [shorter, ite_eq_left hle]
          rw [show L - 2 = i by omega, hbacktrack, show i + 2 = L by omega]
        · simp only [shorter, ite_eq_right hle]
          rw [show L - 2 + 2 = L by omega]
      have hshorterWalk : ∀ j, j < L - 2 → E (shorter j) (shorter (j + 1)) := by
        intro j hj
        by_cases hright : j + 1 ≤ i
        · simpa only [shorter, ite_eq_left (show j ≤ i by omega), ite_eq_left hright] using
            hwalk j (by omega)
        · by_cases hleft : j ≤ i
          · have hji : j = i := by omega
            subst j
            simp only [shorter, ite_eq_left (Nat.le_refl i), ite_eq_right hright]
            rw [hbacktrack, show i + 1 + 2 = i + 2 + 1 by omega]
            exact hwalk (i + 2) (by omega)
          · simpa only [shorter, ite_eq_right hleft, ite_eq_right hright,
                show j + 1 + 2 = j + 2 + 1 by omega] using hwalk (j + 2) (by omega)
      have heq := ih (L - 2) (by omega) shorter (by omega)
        (by simpa only [hfirst] using hstart) (by simpa only [hlast] using hend) hshorterWalk
      exact hdistinct (hfirst.symm.trans (heq.trans hlast))
    have hfirstInner : pos (w 1) ≠ 0 :=
      (hnoHubEdge _ _ (hwalk 0 hL)).resolve_left (fun h => h hstart)
    obtain ⟨hfirstBound, a, b, hab, ha, hb⟩ := hinner (w 1) hfirstInner
    have hfirstPos : pos (w 1) = 1 ∨ pos (w 1) = 2 * k := by
      rcases (hab (w 0)).mp (hsym _ _ (hwalk 0 hL)) with heq | heq
      · left
        rw [← ha, ← heq, hstart]
      · right
        have hmod : (pos (w 1) + 1) % (2 * k + 1) = 0 := by
          rw [← hb, ← heq, hstart]
        by_contra hne
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
    rcases hfirstPos with hforward | hbackward
    · have hpos : ∀ j, j ≤ L → pos (w j) = j := by
        intro j
        induction j using Nat.strong_induction_on with
        | ind j earlier =>
          intro hj
          rcases j with _ | _ | i
          · exact hstart
          · exact hforward
          have hprev := earlier i (by omega) (by omega)
          have hcur := earlier (i + 1) (by omega) (by omega)
          obtain ⟨_, p, q, hadj, hp, hq⟩ := hinner (w (i + 1)) (by omega)
          rw [hcur, Nat.mod_eq_of_lt (by omega)] at hq
          have hprevEq : w i = p := by
            rcases (hadj (w i)).mp (hsym _ _ (hwalk i (by omega))) with heq | heq
            · exact heq
            · have := congrArg pos heq
              omega
          rcases (hadj (w (i + 2))).mp (hwalk (i + 1) (by omega)) with heq | heq
          · exact (hnoBacktrack i (by omega) (hprevEq.trans heq.symm)).elim
          · rwa [heq]
      have := hpos L (Nat.le_refl L)
      omega
    · have hpos : ∀ j, 1 ≤ j → j ≤ L → pos (w j) = 2 * k + 1 - j := by
        intro j
        induction j using Nat.strong_induction_on with
        | ind j earlier =>
          intro hjpos hj
          rcases j with _ | _ | i
          · omega
          · change pos (w 1) = 2 * k + 1 - 1
            omega
          have hcur := earlier (i + 1) (by omega) (by omega) (by omega)
          obtain ⟨_, p, q, hadj, hp, _⟩ := hinner (w (i + 1)) (by omega)
          have hprevEq : w i = q := by
            rcases (hadj (w i)).mp (hsym _ _ (hwalk i (by omega))) with heq | heq
            · have hposEq := congrArg pos heq
              by_cases hi : i = 0
              · rw [hi, hstart] at hposEq
                omega
              · have hprev := earlier i (by omega) (by omega) (by omega)
                omega
            · exact heq
          rcases (hadj (w (i + 2))).mp (hwalk (i + 1) (by omega)) with heq | heq
          · rw [heq]
            omega
          · exact (hnoBacktrack i (by omega) (hprevEq.trans heq.symm)).elim
      have := hpos L (by omega) (Nat.le_refl L)
      omega

theorem L_meta_249 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ),
      1 ≤ k →
      ((∀ u v : Fin N, E u v → E v u) ∧
        (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧
        ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N,
          (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧
          pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) →
      (∀ (L : ℕ) (w : ℕ → Fin N), pos (w 0) = 0 → pos (w L) = 0 →
        w 0 ≠ w L → (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L) ∧
      ∀ v a b c : Fin N, E v a → E v b → E v c →
        a ≠ b → a ≠ c → b ≠ c → pos v = 0 := by
  intro N k E pos hk ⟨hsym, hnoHubEdge, hinner⟩
  constructor
  · intro L w hstart hend hdistinct hwalk
    by_contra hshort
    exact hdistinct (shortWalkSameHub hk hsym hnoHubEdge hinner L w (by omega) hstart hend hwalk)
  · intro v a b c hva hvb hvc hab hac hbc
    by_contra hnonzero
    obtain ⟨_, p, q, hadj, _, _⟩ := hinner v hnonzero
    rcases (hadj a).mp hva with ha | ha <;>
      rcases (hadj b).mp hvb with hb | hb <;>
      rcases (hadj c).mp hvc with hc | hc <;>
      first | exact hab (ha.trans hb.symm) | exact hac (ha.trans hc.symm) |
        exact hbc (hb.trans hc.symm)

end PEqualNP.Outside
