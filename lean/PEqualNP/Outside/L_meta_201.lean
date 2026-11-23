import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_201_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]; simp

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false
      = if i < w.length then w.getD i false else if i = w.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · apply List.getD_eq_default
    simp only [List.length_append, List.length_singleton]
    omega

def Sep (Wu Wv : List Bool) (a b : ℕ) : Prop :=
  (Wu.getD a false = true ∧ Wv.getD a false = false ∧ Wv.getD b false = true ∧
      Wu.getD b false = false) ∨
  (Wv.getD a false = true ∧ Wu.getD a false = false ∧ Wu.getD b false = true ∧
      Wv.getD b false = false)

theorem Sep_lt (wu wv : List Bool) (hvl : wv.length = wu.length) (a b : ℕ)
    (h : Sep wu wv a b) : a < wu.length ∧ b < wu.length := by
  constructor
  · by_contra hc
    have hc' : wu.length ≤ a := not_lt.mp hc
    have h1 : wu.getD a false = false := List.getD_eq_default _ _ hc'
    have h2 : wv.getD a false = false := List.getD_eq_default _ _ (hvl ▸ hc')
    rcases h with ⟨h3, -, -, -⟩ | ⟨h3, -, -, -⟩ <;> simp_all
  · by_contra hc
    have hc' : wu.length ≤ b := not_lt.mp hc
    have h1 : wu.getD b false = false := List.getD_eq_default _ _ hc'
    have h2 : wv.getD b false = false := List.getD_eq_default _ _ (hvl ▸ hc')
    rcases h with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ <;> simp_all

theorem gate_step (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (wu wv wuv : List Bool) (hvl : wv.length = wu.length)
    (hinv : ∀ i, wuv.getD i false = (wu.getD i false || wv.getD i false)) :
    g.op.eval (g.inputs.map fun i => wuv.getD i false)
        = (g.op.eval (g.inputs.map fun i => wu.getD i false)
          || g.op.eval (g.inputs.map fun i => wv.getD i false)) ∨
      (g.op = GateOp.and ∧ ∃ a b, g.inputs = [a, b] ∧ a < wu.length ∧ b < wu.length ∧
        Sep wu wv a b) := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen ⊢
  match inputs, hlen with
  | [], _ =>
    left
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a], _ =>
    left
    rcases hop with rfl | rfl <;>
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, id, hinv] <;>
      cases wu.getD a false <;> cases wv.getD a false <;> simp
  | [a, b], _ =>
    rcases hop with rfl | rfl
    ·
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        hinv]
      have key : ((wu.getD a false || wv.getD a false) && ((wu.getD b false || wv.getD b false)
          && true)) = ((wu.getD a false && (wu.getD b false && true))
          || (wv.getD a false && (wv.getD b false && true))) ∨ Sep wu wv a b := by
        unfold Sep
        cases wu.getD a false <;> cases wv.getD a false <;> cases wu.getD b false <;>
          cases wv.getD b false <;> simp
      rcases key with key | key
      · exact Or.inl key
      · right
        obtain ⟨ha, hb⟩ := Sep_lt wu wv hvl a b key
        exact ⟨trivial, a, b, rfl, ha, hb, key⟩
    ·
      left
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        hinv]
      cases wu.getD a false <;> cases wv.getD a false <;> cases wu.getD b false <;>
        cases wv.getD b false <;> simp

theorem main (gs : List Gate) : ∀ (wu wv wuv : List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    wv.length = wu.length → wuv.length = wu.length →
    (∀ i, wuv.getD i false = (wu.getD i false || wv.getD i false)) →
    (∃ (j : ℕ) (g : Gate) (a b : ℕ), gs[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
        a < wu.length + j ∧ b < wu.length + j ∧ Sep (wiresFrom gs wu) (wiresFrom gs wv) a b) ∨
    ∀ i, (wiresFrom gs wuv).getD i false
      = ((wiresFrom gs wu).getD i false || (wiresFrom gs wv).getD i false) := by
  induction gs with
  | nil =>
    intro wu wv wuv _ _ _ hinv
    right
    intro i
    simpa [wiresFrom] using hinv i
  | cons g gs ih =>
    intro wu wv wuv hok hvl huvl hinv
    have hg := hok g (List.mem_cons_self ..)
    have hok' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    rcases gate_step g hg.1 hg.2 wu wv wuv hvl hinv with heq | ⟨hand, a, b, hin, ha, hb, hsep⟩
    ·
      have hinv' : ∀ i, (wuv ++ [g.op.eval (g.inputs.map fun i => wuv.getD i false)]).getD i false
          = ((wu ++ [g.op.eval (g.inputs.map fun i => wu.getD i false)]).getD i false
            || (wv ++ [g.op.eval (g.inputs.map fun i => wv.getD i false)]).getD i false) := by
        intro i
        rw [getD_snoc, getD_snoc, getD_snoc, hvl, huvl]
        split_ifs with h1 h2
        · exact hinv i
        · exact heq
        · rfl
      rcases ih _ _ _ hok' (by simp [hvl]) (by simp [huvl]) hinv' with
        ⟨j, g', a, b, hj, h1, h2, ha, hb, hsep⟩ | hall
      · left
        refine ⟨j + 1, g', a, b, hj, h1, h2, ?_, ?_, hsep⟩
        · simp only [List.length_append, List.length_singleton] at ha; omega
        · simp only [List.length_append, List.length_singleton] at hb; omega
      · right
        exact hall
    ·
      left
      refine ⟨0, g, a, b, rfl, hand, hin, by simpa using ha, by simpa using hb, ?_⟩
      rw [wiresFrom_cons, wiresFrom_cons]
      have e : ∀ (w : List Bool) (c : ℕ), c < w.length →
          (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD c false
            = w.getD c false := by
        intro w c hc
        rw [getD_wiresFrom _ _ _ (by simp; omega), List.getD_append _ _ _ _ hc]
      unfold Sep at hsep ⊢
      rw [e wu a ha, e wu b hb, e wv a (hvl ▸ ha), e wv b (hvl ▸ hb)]
      exact hsep

end PEqualNP.Outside.L_meta_201_aux

open PEqualNP.Outside.L_meta_201_aux in
theorem PEqualNP.Outside.L_meta_201 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∀ u v : Fin n, G.Adj u v → ∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ (((C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = false) ∨ ((C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = false))) := by
  intro n G _ C hfan hnot hC u v huv
  have hok : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    have h3 := hnot g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h3
  have hinv : ∀ i, (List.ofFn (fun i : Fin n => (decide (i = u) || decide (i = v)))).getD i false
      = ((List.ofFn (fun i : Fin n => decide (i = u))).getD i false
        || (List.ofFn (fun i : Fin n => decide (i = v))).getD i false) := by
    intro i
    by_cases h : i < n
    · simp [List.getD_eq_getElem?_getD, h]
    · simp [List.getD_eq_getElem?_getD, h]
  rcases main C.gates (List.ofFn (fun i : Fin n => decide (i = u)))
      (List.ofFn (fun i : Fin n => decide (i = v)))
      (List.ofFn (fun i : Fin n => (decide (i = u) || decide (i = v)))) hok
      (by simp) (by simp) hinv with ⟨j, g, a, b, hj, h1, h2, ha, hb, hsep⟩ | hall
  · refine ⟨j, g, a, b, hj, h1, h2, by simpa using ha, by simpa using hb, ?_⟩
    rw [wires_eq, wires_eq]
    exact hsep
  · exfalso
    have h := hall C.output
    have e1 := congrFun hC (fun i : Fin n => (decide (i = u) || decide (i = v)))
    have e2 := congrFun hC (fun i : Fin n => decide (i = u))
    have e3 := congrFun hC (fun i : Fin n => decide (i = v))
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      wires_eq] at e1 e2 e3
    rw [e1, e2, e3] at h
    have t1 : decide (∃ i j : Fin n, G.Adj i j ∧ (decide (i = u) || decide (i = v)) = true ∧
        (decide (j = u) || decide (j = v)) = true) = true := by
      rw [decide_eq_true_iff]
      exact ⟨u, v, huv, by simp, by simp⟩
    have t2 : decide (∃ i j : Fin n, G.Adj i j ∧ decide (i = u) = true ∧
        decide (j = u) = true) = false := by
      rw [decide_eq_false_iff_not]
      rintro ⟨i, j, hij, hi, hj⟩
      rw [decide_eq_true_iff] at hi hj
      subst hi; subst hj
      exact G.irrefl hij
    have t3 : decide (∃ i j : Fin n, G.Adj i j ∧ decide (i = v) = true ∧
        decide (j = v) = true) = false := by
      rw [decide_eq_false_iff_not]
      rintro ⟨i, j, hij, hi, hj⟩
      rw [decide_eq_true_iff] at hi hj
      subst hi; subst hj
      exact G.irrefl hij
    rw [t1, t2, t3] at h
    simp at h
