import Mathlib
import PEqualNP.Defs

open PEqualNP.Search
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverPromise

private lemma L_meta_489_lit_len (l : Literal) : 1 ≤ (encodeLiteral l).length := by
  simp [encodeLiteral]

private lemma L_meta_489_flat_len_bound (c : Clause) :
    c.length ≤ (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [List.flatMap_cons, List.length_cons, List.length_append]
    have h := L_meta_489_lit_len l
    have h2 := Nat.add_le_add ih h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2

private lemma L_meta_489_clause_bound (c : Clause) :
    (c.map some ++ [none]).length ≤ (encodeClause c).length := by
  have h := L_meta_489_flat_len_bound c
  simp only [encodeClause, List.length_append, List.length_map, List.length_singleton]
  simp only [List.length_cons, List.length_nil]
  omega

private lemma L_meta_489_flat_bound (φ : CNF) :
    (φ.flatMap (fun c => c.map some ++ [none])).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
    have h := Nat.add_le_add (L_meta_489_clause_bound c) ih
    simpa [encodeCNF, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private lemma L_meta_489_exists (φ : CNF) (z : ℕ) (hz : z ∈ vars φ) :
    ∃ o ∈ φ.flatMap (fun c => c.map some ++ [none]),
      o.any (fun l => l.1 == z) = true := by
  obtain ⟨c, hc, l, hl, rfl⟩ : ∃ c ∈ φ, ∃ l ∈ c, l.1 = z := by
    simpa [vars] using hz
  refine ⟨some l, ?_, ?_⟩
  · rw [List.mem_flatMap]
    exact ⟨c, hc, by simp [hl]⟩
  · simp

private lemma L_meta_489_injective (φ : CNF) (e : ℕ → ℕ)
    (he : ∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx
      (fun o => o.any (fun l => l.1 == z))) :
    ∀ z ∈ vars φ, ∀ z' ∈ vars φ, e z = e z' → z = z' := by
  intro z hz z' hz' heq
  let L := φ.flatMap (fun c => c.map some ++ [none])
  let pz : Option Literal → Bool := fun o => o.any (fun l => l.1 == z)
  let pz' : Option Literal → Bool := fun o => o.any (fun l => l.1 == z')
  have hexz : ∃ o ∈ L, pz o = true := by
    obtain ⟨c, hc, l, hl, rfl⟩ : ∃ c ∈ φ, ∃ l ∈ c, l.1 = z := by
      simpa [vars] using hz
    refine ⟨some l, ?_, ?_⟩
    · rw [List.mem_flatMap]
      exact ⟨c, hc, by simp [hl]⟩
    · simp [pz]
  have hexz' : ∃ o ∈ L, pz' o = true := by
    obtain ⟨c, hc, l, hl, rfl⟩ : ∃ c ∈ φ, ∃ l ∈ c, l.1 = z' := by
      simpa [vars] using hz'
    refine ⟨some l, ?_, ?_⟩
    · rw [List.mem_flatMap]
      exact ⟨c, hc, by simp [hl]⟩
    · simp [pz']
  have hzidx : L.findIdx pz < L.length := List.findIdx_lt_length_of_exists hexz
  have hzidx' : L.findIdx pz' < L.length := List.findIdx_lt_length_of_exists hexz'
  have hpred := List.findIdx_getElem (p := pz) (xs := L) (w := hzidx)
  have hpred' := List.findIdx_getElem (p := pz') (xs := L) (w := hzidx')
  have hfind : L.findIdx pz = L.findIdx pz' := by
    simpa [pz, pz', L, he z, he z'] using heq
  have hpred_common : pz' L[L.findIdx pz] = true := by
    simpa [hfind] using hpred'
  have hval : pz L[L.findIdx pz] = true := hpred
  have hval' : pz' L[L.findIdx pz] = true := hpred_common
  cases ho : L[L.findIdx pz] with
  | none => simp [pz, pz', ho] at hval hval'
  | some l =>
    simp [pz, pz', ho] at hval hval'
    exact hval.symm.trans hval'

theorem PEqualNP.Outside.L_meta_489 : ∀ (φ : PEqualNP.Search.CNF) (e : ℕ → ℕ),
    (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx
      (fun o => o.any (fun l => l.1 == z))) →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
        e z < (PEqualNP.Search.encodeCNF φ).length) ∧
      ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
        ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z' := by
  intro φ e he
  constructor
  · intro z hz
    have hi := List.findIdx_lt_length_of_exists (L_meta_489_exists φ z hz)
    have hb := L_meta_489_flat_bound φ
    have hlt := lt_of_lt_of_le hi hb
    rw [he z]
    exact hlt
  · exact L_meta_489_injective φ e he
