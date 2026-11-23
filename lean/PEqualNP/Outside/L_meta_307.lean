import Mathlib

theorem PEqualNP.Outside.L_meta_307 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ c : ℕ, (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔ (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  classical
  intro V G N num G' bounded inj edges c
  have small {A B : Type} [DecidableEq B] (S : Finset A) (f : A → Finset B) (h : ∀ a, (f a).card ≤ 1) :
      (S.biUnion f).card ≤ S.card := calc
    _ ≤ ∑ a ∈ S, (f a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, 1 := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp
  constructor
  · intro lower S cover
    let pre (a : Fin N) := ∃ u v, G.Adj u v ∧ num u = a.val
    let pick (a : Fin N) : Finset V := if h : pre a then {h.choose} else ∅
    have card (a : Fin N) : (pick a).card ≤ 1 := by dsimp [pick]; split <;> simp
    have endpoint (u v : V) (huv : G.Adj u v) (a : Fin N) (eq : num u = a.val) (ha : a ∈ S) :
        u ∈ S.biUnion pick := by
      have h : pre a := ⟨u,v,huv,eq⟩
      obtain ⟨w,hw,hn⟩ := h.choose_spec
      have he := inj u v h.choose w huv hw (eq.trans hn.symm)
      exact Finset.mem_biUnion.mpr ⟨a,ha,by simp [pick,h,he]⟩
    apply le_trans (lower (S.biUnion pick) ?_) (small S pick card)
    intro u v huv
    let a : Fin N := ⟨num u,bounded _ _ huv⟩
    let b : Fin N := ⟨num v,bounded _ _ huv.symm⟩
    rcases cover a b ((edges a b).2 ⟨u,v,huv,rfl,rfl⟩) with ha | hb
    · exact Or.inl (endpoint u v huv a rfl ha)
    · exact Or.inr (endpoint v u huv.symm b rfl hb)
  · intro lower S cover
    let send (u : V) : Finset (Fin N) := if h : num u < N then {⟨num u,h⟩} else ∅
    have card (u : V) : (send u).card ≤ 1 := by dsimp [send]; split <;> simp
    have member (u : V) (a : Fin N) (eq : num u = a.val) (hu : u ∈ S) : a ∈ S.biUnion send := by
      have hb : num u < N := eq ▸ a.isLt
      refine Finset.mem_biUnion.mpr ⟨u,hu,?_⟩
      simpa [send,hb] using (Fin.ext eq.symm : a = ⟨num u,hb⟩)
    apply le_trans (lower (S.biUnion send) ?_) (small S send card)
    intro a b hab
    obtain ⟨u,v,h,hu,hv⟩ := (edges a b).1 hab
    exact (cover u v h).imp (member u a hu) (member v b hv)
