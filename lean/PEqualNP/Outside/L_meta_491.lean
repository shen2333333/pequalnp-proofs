import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k →
    3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧
    3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  have hsq : 2 * k * (3 * (E + 1)) ^ 2 = 18 * k * (E + 1) ^ 2 := by ring
  refine ⟨?_, by rw [hsq]⟩
  rw [← hsq]
  have hu : u + 1 ≤ 3 * (E + 1) := by omega
  have h1 : u * (3 * (E + 1)) + 3 * (E + 1) ≤ 3 * (E + 1) * (3 * (E + 1)) := by
    have := Nat.mul_le_mul_right (3 * (E + 1)) hu
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have h2 : u * (3 * (E + 1)) + v + 1 ≤ (3 * (E + 1)) ^ 2 := by
    rw [sq]
    omega
  have h3 : 2 * k * (u * (3 * (E + 1)) + v + 1) ≤ 2 * k * (3 * (E + 1)) ^ 2 :=
    Nat.mul_le_mul_left (2 * k) h2
  rw [Nat.mul_add (2 * k) _ 1, Nat.mul_one] at h3
  omega
