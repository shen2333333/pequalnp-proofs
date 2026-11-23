import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta251

open PEqualNP.CircuitLowerBounds

def reaches (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  ∃ (l : ℕ) (u : ℕ → ℕ), u 0 = C.output ∧ u l = v ∧
    ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : Gate),
      u i = n + m ∧ C.gates[m]? = some g ∧ g.op = .or ∧
        u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m

def top (n : ℕ) (C : Circuit) : Set ℕ :=
  {m | ∃ g : Gate, C.gates[m]? = some g ∧ g.op = .or ∧ reaches n C (n + m)}

def liftCircuit (n : ℕ) (C : Circuit) (j a h : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨.or, [a]⟩ ++ [⟨.or, [C.output, h]⟩], n + C.size⟩

theorem get_bound {C : Circuit} {m : ℕ} {g : Gate}
    (hg : C.gates[m]? = some g) : m < C.gates.length :=
  (List.getElem?_eq_some_iff.mp hg).choose

theorem top_bound {n : ℕ} {C : Circuit} {m : ℕ} (hm : m ∈ top n C) :
    m < C.gates.length := by
  obtain ⟨g, hg, _, _⟩ := hm
  exact get_bound hg

theorem top_finite (n : ℕ) (C : Circuit) : (top n C).Finite := by
  apply (Finset.range C.gates.length).finite_toSet.subset
  intro m hm
  exact Finset.mem_range.mpr (top_bound hm)

theorem lift_get {n j a h m : ℕ} {C : Circuit} {g : Gate}
    (hg : C.gates[m]? = some g) (hmj : m ≠ j) :
    (liftCircuit n C j a h).gates[m]? = some g := by
  change (C.gates.set j ⟨.or, [a]⟩ ++ [⟨.or, [C.output, h]⟩])[m]? = some g
  rw [List.getElem?_append_left (by simpa using get_bound hg),
    List.getElem?_set_ne hmj.symm]
  exact hg

theorem lift_root (n j a h : ℕ) (C : Circuit) :
    (liftCircuit n C j a h).gates[C.size]? = some ⟨.or, [C.output, h]⟩ := by
  simp [liftCircuit, Circuit.size, List.getElem?_append]

theorem output_bound {n : ℕ} {C : Circuit} {m : ℕ} (hm : m ∈ top n C) :
    C.output < n + C.size := by
  obtain ⟨g, hg, _, l, u, hu0, hul, hstep⟩ := hm
  cases l with
  | zero =>
    have hb := get_bound hg
    simp only [Circuit.size]
    omega
  | succ l =>
    obtain ⟨k, g', hk, hg', _, _, _⟩ := hstep 0 (Nat.zero_lt_succ l)
    have hb := get_bound hg'
    simp only [Circuit.size]
    omega

theorem reaches_lift {n j a h v : ℕ} {C : Circuit}
    (hnot : ¬ reaches n C (n + j)) (hout : C.output < n + C.size)
    (hr : reaches n C v) : reaches n (liftCircuit n C j a h) v := by
  obtain ⟨l, u, hu0, hul, hstep⟩ := hr
  let w : ℕ → ℕ := fun i => Nat.casesOn i (n + C.size) u
  refine ⟨l + 1, w, rfl, ?_, ?_⟩
  · simpa [w] using hul
  · intro i hi
    cases i with
    | zero =>
      refine ⟨C.size, ⟨.or, [C.output, h]⟩, rfl, lift_root n j a h C, rfl, ?_, ?_⟩
      · simp [w, hu0]
      · simpa [w, hu0] using hout
    | succ i =>
      have hi' : i < l := by omega
      obtain ⟨k, g, huk, hg, hop, hnext, hdec⟩ := hstep i hi'
      have hkj : k ≠ j := by
        intro he
        apply hnot
        refine ⟨i, u, hu0, ?_, ?_⟩
        · simpa [he] using huk
        · intro z hz
          exact hstep z (by omega)
      refine ⟨k, g, ?_, lift_get hg hkj, hop, ?_, ?_⟩
      · simpa [w] using huk
      · simpa [w, Nat.add_assoc] using hnext
      · simpa [w, Nat.add_assoc] using hdec

theorem top_preserved {n j a h : ℕ} {C : Circuit}
    (hnot : ¬ reaches n C (n + j)) : top n C ⊆ top n (liftCircuit n C j a h) := by
  intro m hm
  have hout := output_bound hm
  obtain ⟨g, hg, hop, hr⟩ := hm
  have hmj : m ≠ j := by
    intro he
    subst m
    exact hnot hr
  exact ⟨g, lift_get hg hmj, hop, reaches_lift hnot hout hr⟩

theorem root_in_top (n j a h : ℕ) (C : Circuit) :
    C.size ∈ top n (liftCircuit n C j a h) := by
  refine ⟨⟨.or, [C.output, h]⟩, lift_root n j a h C, rfl, ?_⟩
  refine ⟨0, fun _ => n + C.size, rfl, rfl, ?_⟩
  intro i hi
  omega

theorem card_increases {n j a h : ℕ} {C : Circuit}
    (hnot : ¬ reaches n C (n + j)) :
    (top n C).ncard + 1 ≤ (top n (liftCircuit n C j a h)).ncard := by
  have hnew : C.size ∉ top n C := by
    intro hm
    have hb := top_bound hm
    simp only [Circuit.size] at hb
    omega
  have hsub : insert C.size (top n C) ⊆ top n (liftCircuit n C j a h) := by
    intro m hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · exact root_in_top n j a h C
    · exact top_preserved hnot hm
  calc
    (top n C).ncard + 1 = (insert C.size (top n C)).ncard :=
      (Set.ncard_insert_of_notMem hnew (top_finite n C)).symm
    _ ≤ (top n (liftCircuit n C j a h)).ncard :=
      Set.ncard_le_ncard hsub (top_finite n _)

end PEqualNP.Outside.Meta251

theorem PEqualNP.Outside.L_meta_251 : ∀ (n j a h : ℕ) (C C2 : PEqualNP.CircuitLowerBounds.Circuit), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → ¬ (∃ (l : ℕ) (u : ℕ → ℕ), u 0 = C.output ∧ u l = n + j ∧ ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), u i = n + m ∧ C.gates[m]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m) → C2 = ⟨C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], n + C.size⟩ → {m : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[m]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ (l : ℕ) (u : ℕ → ℕ), u 0 = C.output ∧ u l = n + m ∧ ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), u i = n + m ∧ C.gates[m]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m)}.ncard + 1 ≤ {m : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C2.gates[m]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ (l : ℕ) (u : ℕ → ℕ), u 0 = C2.output ∧ u l = n + m ∧ ∀ i : ℕ, i < l → ∃ (m : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), u i = n + m ∧ C2.gates[m]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ u (i + 1) ∈ g.inputs ∧ u (i + 1) < n + m)}.ncard := by
  intro n j a h C C2 _ hnot hC2
  subst C2
  change (PEqualNP.Outside.Meta251.top n C).ncard + 1 ≤
    (PEqualNP.Outside.Meta251.top n (PEqualNP.Outside.Meta251.liftCircuit n C j a h)).ncard
  exact PEqualNP.Outside.Meta251.card_increases hnot
