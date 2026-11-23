import Mathlib.Data.Nat.Basic

theorem PEqualNP.Outside.L_meta_294 : ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k → m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' → u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' heq
  have hpos : 0 < 2 * k := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
  have houter : 2 * k * (u.val * m + v.val) + i =
      2 * k * (u'.val * m + v'.val) + i' :=
    Nat.add_left_cancel (by simpa only [Nat.add_assoc] using heq)
  have hmod := congrArg (fun z : ℕ => z % (2 * k)) houter
  have hii : i = i' := by
    simpa only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hi'] using hmod
  have hmul : 2 * k * (u.val * m + v.val) =
      2 * k * (u'.val * m + v'.val) := by
    apply Nat.add_right_cancel
    simpa only [hii] using houter
  have hbase : u.val * m + v.val = u'.val * m + v'.val :=
    Nat.mul_left_cancel hpos hmul
  have hmod2 := congrArg (fun z : ℕ => z % m) hbase
  have hval : v.val = v'.val := by
    simpa only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt v.isLt,
      Nat.mod_eq_of_lt v'.isLt] using hmod2
  have hleft : u.val * m = u'.val * m := by
    apply Nat.add_right_cancel
    simpa only [← hval] using hbase
  have hu : u.val = u'.val := Nat.mul_right_cancel hmpos hleft
  exact ⟨Fin.ext hu, Fin.ext hval, hii⟩
