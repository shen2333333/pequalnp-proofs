import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private lemma readDigits (xs ys : List Bool)
    (h : xs.flatMap (fun b => [true,b]) = ys.flatMap (fun b => [true,b])) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp at h
      exact congrArg₂ List.cons h.1 (ih _ h.2)

private lemma readNat (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => simp [Nat.bits_append_bit _ _ hn, ih]

theorem L_meta_368 :
    ∀ l l' : PEqualNP.Search.Literal, (PEqualNP.Search.encodeLiteral l).tail.tail = (PEqualNP.Search.encodeLiteral l').tail.tail ↔ l.1 = l'.1 := by
  intro l l'
  simp only [PEqualNP.Search.encodeLiteral, List.cons_append, List.nil_append,
    List.tail_cons, List.append_cancel_right_eq]
  constructor
  · intro h
    simpa only [readNat] using congrArg (fun xs : List Bool => xs.foldr Nat.bit 0) (readDigits _ _ h)
  · intro h
    rw [h]

end PEqualNP.Outside
