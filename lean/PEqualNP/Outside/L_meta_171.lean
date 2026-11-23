import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace L171

/-- One evaluation step of `Circuit.wires`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

/-- The value of the gate at position `t` of `G` as read in the wires. -/
theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

/-- The wires a gate's value depends on: all inputs, or the head for `NOT`. -/
def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

/-- Renaming of wire indices after the wire `p` is deleted, its readers sent to `r`. -/
def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

/-- The gates with gate `t` (wire `p`) deleted and the later gates renamed. -/
def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

theorem deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem fanInTwo_del (G : List Gate) (o : ℕ) (t p r o' : ℕ) (h : FanInTwo ⟨G, o⟩) :
    FanInTwo ⟨del G t p r, o'⟩ := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [renG] using h2⟩

/-- A constant-true gate: `AND` of no wires. -/
def src : Gate := ⟨GateOp.and, []⟩

/-- `C` with the last input replaced by a constant-true gate at the same wire. -/
def plus (C : Circuit) : Circuit := ⟨src :: C.gates, C.output⟩

theorem ofFn_snoc {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem plus_foldl (C : Circuit) {n : ℕ} (y : Fin n → Bool) :
    (plus C).gates.foldl step (List.ofFn y) = C.gates.foldl step (List.ofFn (Fin.snoc y true)) := by
  simp only [plus, List.foldl_cons, step, src, GateOp.eval, List.map_nil, List.all_nil, ofFn_snoc]

theorem plus_circuitFun (C : Circuit) (n : ℕ) :
    circuitFun n (plus C) = fun y => circuitFun (n + 1) C (Fin.snoc y true) := by
  funext y
  simp only [circuitFun, Circuit.eval, wires_eq, plus_foldl]
  rfl

theorem plus_fanInTwo (C : Circuit) (h : FanInTwo C) : FanInTwo (plus C) := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [plus, List.mem_cons] at hg
  rcases hg with rfl | hg
  · simp [src]
  · exact h g hg

theorem plus_size (C : Circuit) : (plus C).size = C.size + 1 := by
  simp [plus, Circuit.size]

theorem plus_getD_src (C : Circuit) {n : ℕ} (y : Fin n → Bool) :
    ((plus C).gates.foldl step (List.ofFn y)).getD n false = true := by
  rw [plus_foldl, ofFn_snoc, foldl_step_getD _ _ _ (by simp), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

/-- The value of gate `t`: its operation on the wires it reads, among those that exist. -/
theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

theorem del_getElem_lt (G : List Gate) (t p r t' : ℕ) (h : t' < t) (ht : t < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r ht]; omega) = G[t']'(by omega) := by
  simp only [del]
  rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]

theorem del_getElem_ge (G : List Gate) (t p r t' : ℕ) (h : t ≤ t') (ht : t' + 1 < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r (by omega)]; omega) = renG p r (G[t' + 1]'ht) := by
  simp only [del]
  rw [List.getElem_append_right (by simp [List.length_take]; omega), List.getElem_map, List.getElem_drop]
  congr 2
  simp [List.length_take]
  omega

/-- Delete the gates listed (positions and replacement wires), largest position first. -/
def delMany (m : ℕ) : List Gate → ℕ → List (ℕ × ℕ) → List Gate × ℕ
  | G, o, [] => (G, o)
  | G, o, d :: rest => delMany m (del G d.1 (m + d.1) d.2) (ren (m + d.1) d.2 o) rest

/-- A deletion is justified by equal values on every input, or by nobody reading the wire. -/
def Just (m : ℕ) (G : List Gate) (o : ℕ) (ds : List (ℕ × ℕ)) (d : ℕ × ℕ) : Prop :=
  (∀ x : List Bool, x.length = m →
      (G.foldl step x).getD (m + d.1) false = (G.foldl step x).getD d.2 false) ∨
  ((∀ t, (ht : t < G.length) → d.1 < t → (∀ d' ∈ ds, t ≠ d'.1) → m + d.1 ∉ deps (G[t])) ∧
    o ≠ m + d.1 ∧ ∀ d' ∈ ds, d' ≠ d → d'.2 ≠ m + d.1)

theorem delMany_spec (m : ℕ) : ∀ (ds : List (ℕ × ℕ)) (G : List Gate) (o : ℕ),
    ds.Pairwise (fun a b => b.1 < a.1) →
    (∀ d ∈ ds, d.1 < G.length) →
    (∀ d ∈ ds, d.2 < m + d.1 ∨ m + G.length ≤ d.2) →
    (∀ d ∈ ds, Just m G o ds d) →
    (delMany m G o ds).1.length = G.length - ds.length ∧
    (∀ o₀, FanInTwo ⟨G, o₀⟩ → FanInTwo ⟨(delMany m G o ds).1, (delMany m G o ds).2⟩) ∧
    (∀ x : List Bool, x.length = m →
      Circuit.eval ⟨(delMany m G o ds).1, (delMany m G o ds).2⟩ x = Circuit.eval ⟨G, o⟩ x) := by
  intro ds
  induction ds with
  | nil =>
    intro G o _ _ _ _
    exact ⟨by simp [delMany], fun o₀ h => by simpa [delMany, FanInTwo] using h, fun x _ => rfl⟩
  | cons d rest ih =>
    intro G o hsort hlt hval hjust
    obtain ⟨t, r⟩ := d
    rw [List.pairwise_cons] at hsort
    obtain ⟨hgt, hsort'⟩ := hsort
    simp only at hgt
    have ht : t < G.length := hlt (t, r) (by simp)
    have hr : r < m + t ∨ m + G.length ≤ r := hval (t, r) (by simp)
    have hjt := hjust (t, r) (by simp)
    -- the value hypothesis for the head deletion, on every input
    have hhead : ∀ x : List Bool, x.length = m →
        (∀ g ∈ G.drop (t + 1), m + t ∈ deps g →
          (G.foldl step x).getD (m + t) false = (G.foldl step x).getD r false) ∧
        (o = m + t → (G.foldl step x).getD (m + t) false = (G.foldl step x).getD r false) := by
      intro x hx
      rcases hjt with hv | ⟨hun, ho, _⟩
      · exact ⟨fun _ _ _ => hv x hx, fun _ => hv x hx⟩
      · refine ⟨fun g hg hmem => ?_, fun h => absurd h ho⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
        rw [List.getElem_drop] at hmem
        exact absurd hmem (hun (t + 1 + i) (by simp at hi; omega) (by omega)
          (fun d' hd' => by
            simp only [List.mem_cons] at hd'
            rcases hd' with rfl | hd'
            · simp; omega
            · have := hgt d' hd'; omega))
    have hW' : ∀ x : List Bool, x.length = m →
        (del G t (m + t) r).foldl step x = (G.foldl step x).eraseIdx (m + t) := by
      intro x hx
      have := del_foldl G x t r ht (by rw [hx]; exact hr) (by rw [hx]; exact (hhead x hx).1)
      rwa [hx] at this
    have hlen' : (del G t (m + t) r).length = G.length - 1 := del_length G t (m + t) r ht
    have hlt' : ∀ d' ∈ rest, d'.1 < (del G t (m + t) r).length := by
      intro d' hd'; rw [hlen']; have := hgt d' hd'; omega
    have hval' : ∀ d' ∈ rest, d'.2 < m + d'.1 ∨ m + (del G t (m + t) r).length ≤ d'.2 := by
      intro d' hd'; rw [hlen']
      rcases hval d' (List.mem_cons_of_mem _ hd') with h | h
      · exact Or.inl h
      · right; omega
    have hjust' : ∀ d' ∈ rest, Just m (del G t (m + t) r) (ren (m + t) r o) rest d' := by
      intro d' hd'
      have hd't : d'.1 < t := hgt d' hd'
      rcases hjust d' (List.mem_cons_of_mem _ hd') with hv | ⟨hun, ho, hrep⟩
      · left
        intro x hx
        rw [hW' x hx, getD_eraseIdx_lt _ _ _ (by omega)]
        rcases hval d' (List.mem_cons_of_mem _ hd') with h | h
        · rw [getD_eraseIdx_lt ((G.foldl step x)) (m + t) d'.2 (by omega)]; exact hv x hx
        · rw [getD_of_length_le ((G.foldl step x).eraseIdx (m + t)) d'.2
            (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
            hv x hx, getD_of_length_le _ _ (by rw [foldl_step_length]; omega)]
      · right
        have hrt : r ≠ m + d'.1 := hrep (t, r) (by simp) (by intro h; rw [← h] at hd't; simp at hd't)
        refine ⟨fun t' ht' hd't' hnot => ?_, ?_, fun d'' hd'' hne => hrep d'' (List.mem_cons_of_mem _ hd'') hne⟩
        · by_cases htt : t' < t
          · rw [del_getElem_lt G t (m + t) r t' htt ht]
            exact hun t' (by omega) hd't' (fun d'' hd'' => by
              simp only [List.mem_cons] at hd''
              rcases hd'' with rfl | hd''
              · simp; omega
              · exact hnot d'' hd'')
          · have htt' : t ≤ t' := by omega
            rw [del_getElem_ge G t (m + t) r t' htt' (by rw [hlen'] at ht'; omega), deps_renG]
            intro hmem
            obtain ⟨i, hi, hreni⟩ := List.mem_map.1 hmem
            have hi' : m + d'.1 ∉ deps (G[t' + 1]'(by rw [hlen'] at ht'; omega)) :=
              hun (t' + 1) (by rw [hlen'] at ht'; omega) (by omega) (fun d'' hd'' => by
                simp only [List.mem_cons] at hd''
                rcases hd'' with rfl | hd''
                · simp; omega
                · have := hgt d'' hd''; omega)
            unfold ren at hreni
            split_ifs at hreni with h1 h2
            · exact hi' (hreni ▸ hi)
            · exact hrt hreni
            · omega
        · unfold ren
          split_ifs with h1 h2
          · exact ho
          · exact hrt
          · omega
    obtain ⟨ih1, ih2, ih3⟩ := ih (del G t (m + t) r) (ren (m + t) r o) hsort' hlt' hval' hjust'
    refine ⟨?_, fun o₀ h => ih2 _ (fanInTwo_del G o₀ t (m + t) r o₀ h), fun x hx => ?_⟩
    · simp only [delMany]
      rw [ih1, hlen']
      simp
      omega
    · simp only [delMany]
      rw [ih3 x hx]
      have := del_eval G o x t r ht (by rw [hx]; exact hr) (by rw [hx]; exact (hhead x hx).1)
        (by rw [hx]; exact (hhead x hx).2)
      rwa [hx] at this

/-- A smaller circuit from a justified list of deletions. -/
theorem smaller (m : ℕ) (G : List Gate) (o : ℕ) (ds : List (ℕ × ℕ))
    (hsort : ds.Pairwise (fun a b => b.1 < a.1)) (hlt : ∀ d ∈ ds, d.1 < G.length)
    (hval : ∀ d ∈ ds, d.2 < m + d.1 ∨ m + G.length ≤ d.2) (hjust : ∀ d ∈ ds, Just m G o ds d)
    (hfan : FanInTwo ⟨G, o⟩) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = G.length - ds.length ∧
      ∀ x : List Bool, x.length = m → D.eval x = Circuit.eval ⟨G, o⟩ x := by
  obtain ⟨h1, h2, h3⟩ := delMany_spec m ds G o hsort hlt hval hjust
  exact ⟨⟨(delMany m G o ds).1, (delMany m G o ds).2⟩, h2 o hfan, h1, h3⟩

theorem just_congr (m : ℕ) (G : List Gate) (o : ℕ) (ds ds' : List (ℕ × ℕ))
    (h : ∀ d, d ∈ ds ↔ d ∈ ds') (d : ℕ × ℕ) (hj : Just m G o ds d) : Just m G o ds' d := by
  unfold Just at hj ⊢
  rcases hj with hj | ⟨h1, h2, h3⟩
  · exact Or.inl hj
  · exact Or.inr ⟨fun t ht hdt hnot => h1 t ht hdt (fun d' hd' => hnot d' ((h d').1 hd')),
      h2, fun d' hd' hne => h3 d' ((h d').2 hd') hne⟩

/-- Three deletions in any order. -/
theorem smaller3 (m : ℕ) (G : List Gate) (o : ℕ) (d₁ d₂ d₃ : ℕ × ℕ)
    (h12 : d₁.1 ≠ d₂.1) (h13 : d₁.1 ≠ d₃.1) (h23 : d₂.1 ≠ d₃.1)
    (hlt : ∀ d ∈ [d₁, d₂, d₃], d.1 < G.length)
    (hval : ∀ d ∈ [d₁, d₂, d₃], d.2 < m + d.1 ∨ m + G.length ≤ d.2)
    (hjust : ∀ d ∈ [d₁, d₂, d₃], Just m G o [d₁, d₂, d₃] d)
    (hfan : FanInTwo ⟨G, o⟩) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = G.length - 3 ∧
      ∀ x : List Bool, x.length = m → D.eval x = Circuit.eval ⟨G, o⟩ x := by
  have key : ∀ L : List (ℕ × ℕ), (∀ d, d ∈ L ↔ d ∈ [d₁, d₂, d₃]) → L.length = 3 →
      L.Pairwise (fun a b => b.1 < a.1) →
      ∃ D : Circuit, FanInTwo D ∧ D.size = G.length - 3 ∧
        ∀ x : List Bool, x.length = m → D.eval x = Circuit.eval ⟨G, o⟩ x := by
    intro L hL hlen hsort
    have := smaller m G o L hsort (fun d hd => hlt d ((hL d).1 hd)) (fun d hd => hval d ((hL d).1 hd))
      (fun d hd => just_congr m G o _ _ (fun d => (hL d).symm) d (hjust d ((hL d).1 hd))) hfan
    rwa [hlen] at this
  rcases lt_trichotomy d₁.1 d₂.1 with a | a | a <;> rcases lt_trichotomy d₁.1 d₃.1 with b | b | b <;>
    rcases lt_trichotomy d₂.1 d₃.1 with c | c | c <;> first
    | exact absurd a h12 | exact absurd b h13 | exact absurd c h23
    | exact key [d₃, d₂, d₁] (fun d => by simp only [List.mem_cons, List.not_mem_nil, or_false]; try tauto) rfl (by simp; omega)
    | exact key [d₂, d₃, d₁] (fun d => by simp only [List.mem_cons, List.not_mem_nil, or_false]; try tauto) rfl (by simp; omega)
    | exact key [d₃, d₁, d₂] (fun d => by simp only [List.mem_cons, List.not_mem_nil, or_false]; try tauto) rfl (by simp; omega)
    | exact key [d₁, d₃, d₂] (fun d => by simp only [List.mem_cons, List.not_mem_nil, or_false]; try tauto) rfl (by simp; omega)
    | exact key [d₂, d₁, d₃] (fun d => by simp only [List.mem_cons, List.not_mem_nil, or_false]; try tauto) rfl (by simp; omega)
    | exact key [d₁, d₂, d₃] (fun d => by simp only [List.mem_cons, List.not_mem_nil, or_false]; try tauto) rfl (by simp; omega)

/-- The wire that can stand in for a gate reading a wire of constant value `b`. -/
def other (l : List ℕ) (c : ℕ) : Option ℕ :=
  match l with
  | [a, d] => if a = c then (if d = c then none else some d) else (if d = c then some a else none)
  | _ => none

def repOf (g : Gate) (c q : ℕ) (b : Bool) (nsrc big : ℕ) : ℕ :=
  match g.op with
  | GateOp.not => if b then big else nsrc
  | GateOp.and =>
    if b then (match other g.inputs c with | some d => if d < q then d else big | none => nsrc) else big
  | GateOp.or =>
    if b then nsrc else (match other g.inputs c with | some d => if d < q then d else big | none => big)
  | _ => big

theorem repOf_valid (g : Gate) (c q : ℕ) (b : Bool) (nsrc big : ℕ) (hn : nsrc < q) :
    repOf g c q b nsrc big < q ∨ repOf g c q b nsrc big = big := by
  obtain ⟨op, l⟩ := g
  simp only [repOf]
  cases op <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    first
    | exact Or.inl hn
    | exact Or.inr trivial
    | exact Or.inr rfl
    | (rcases h : other l c with _ | d
       · first | exact Or.inl hn | exact Or.inr rfl | exact Or.inr trivial
       · by_cases hd : d < q
         · simp [hd]
         · simp [hd])

theorem reader_value (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (c q : ℕ) (b : Bool) (W : List Bool) (nsrc big : ℕ)
    (hc : c ∈ deps g) (hcq : c < q) (hnq : nsrc < q) (hWc : W.getD c false = b)
    (hWn : W.getD nsrc false = true) (hbig : W.getD big false = false)
    (hq : W.getD q false = g.op.eval (g.inputs.map fun i => if i < q then W.getD i false else false)) :
    W.getD q false = W.getD (repOf g c q b nsrc big) false := by
  rw [hq]
  obtain ⟨op, l⟩ := g
  simp only [deps, repOf] at hc ⊢
  simp only [List.getD_eq_getElem?_getD] at hWc hWn hbig ⊢
  rcases hop with rfl | rfl | rfl <;> rcases l with _ | ⟨a, _ | ⟨d, _ | ⟨e, l'⟩⟩⟩
  · simp at hc
  · simp only [List.mem_singleton] at hc
    subst hc
    cases b <;> simp [GateOp.eval, other, hcq, hWc, hWn, hbig]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    by_cases ha : a = c <;> by_cases hd : d = c
    · cases b <;> simp [GateOp.eval, other, ha, hd, hcq, hWc, hWn, hbig]
    · cases b <;> simp [GateOp.eval, other, ha, hd, hcq, hWc, hWn, hbig] <;>
        (try (split_ifs with hdq <;> simp [hdq, hbig]))
    · cases b <;> simp [GateOp.eval, other, ha, hd, hcq, hWc, hWn, hbig] <;>
        (try (split_ifs with hdq <;> simp [hdq, hbig]))
    · rcases hc with hc | hc
      · exact (ha hc.symm).elim
      · exact (hd hc.symm).elim
  · simp at hlen
  · simp at hc
  · simp only [List.mem_singleton] at hc
    subst hc
    cases b <;> simp [GateOp.eval, other, hcq, hWc, hWn, hbig]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    by_cases ha : a = c <;> by_cases hd : d = c
    · cases b <;> simp [GateOp.eval, other, ha, hd, hcq, hWc, hWn, hbig]
    · cases b <;> simp [GateOp.eval, other, ha, hd, hcq, hWc, hWn, hbig] <;>
        (try (split_ifs with hdq <;> simp [hdq, hbig]))
    · cases b <;> simp [GateOp.eval, other, ha, hd, hcq, hWc, hWn, hbig] <;>
        (try (split_ifs with hdq <;> simp [hdq, hbig]))
    · rcases hc with hc | hc
      · exact (ha hc.symm).elim
      · exact (hd hc.symm).elim
  · simp at hlen
  · simp at hc
  · simp only [List.head?_cons, Option.toList_some, List.mem_singleton] at hc
    subst hc
    cases b <;> simp [GateOp.eval, hcq, hWc, hWn, hbig]
  · simp only [List.head?_cons, Option.toList_some, List.mem_singleton] at hc
    subst hc
    cases b <;> simp [GateOp.eval, hcq, hWc, hWn, hbig]
  · simp at hlen

theorem other_ne (l : List ℕ) (c d : ℕ) (h : other l c = some d) : d ≠ c := by
  unfold other at h
  split at h
  · split_ifs at h <;> simp_all
  · simp at h

theorem repOf_ne (g : Gate) (c q : ℕ) (b : Bool) (nsrc big : ℕ) (hn : nsrc ≠ c) (hb : big ≠ c) :
    repOf g c q b nsrc big ≠ c := by
  obtain ⟨op, l⟩ := g
  simp only [repOf]
  cases op <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    first
    | exact hn
    | exact hb
    | (rcases h : other l c with _ | d
       · first | exact hn | exact hb
       · by_cases hd : d < q
         · simpa [hd] using other_ne l c d h
         · simpa [hd] using hb)

theorem plus_eval_eq (C : Circuit) {n : ℕ} (y : Fin n → Bool) :
    ((plus C).gates.foldl step (List.ofFn y)).getD C.output false =
      circuitFun (n + 1) C (Fin.snoc y true) := by
  rw [plus_foldl]
  rfl

theorem plus_getD_src' (C : Circuit) (n : ℕ) (x : List Bool) (hx : x.length = n) :
    ((plus C).gates.foldl step x).getD n false = true := by
  simp only [plus, List.foldl_cons, step, src, GateOp.eval, List.map_nil, List.all_nil]
  rw [foldl_step_getD _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp [hx]

/-- The bad shapes: a reader of the last input whose value under `true` is the constant `bj`. -/
theorem bad_case (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit (n + 1) C)
    (hnc : ∃ y y' : Fin n → Bool,
      circuitFun (n + 1) C (Fin.snoc y true) ≠ circuitFun (n + 1) C (Fin.snoc y' true))
    (hH3 : ∀ s : ℕ, HasCircuitSize n (fun y : Fin n → Bool => circuitFun (n + 1) C (Fin.snoc y true)) s →
      C.size ≤ s + 1)
    (j : ℕ) (hj : j < C.gates.length) (bj : Bool)
    (hWp : ∀ x : List Bool, x.length = n →
      ((plus C).gates.foldl step x).getD (n + 1 + j) false = bj) : False := by
  classical
  set G := (plus C).gates with hG
  have hGlen : G.length = C.gates.length + 1 := by simp [hG, plus]
  set big := n + G.length with hbig
  set p := n + 1 + j with hp
  have hGt : ∀ t (ht : t < C.gates.length), G[t + 1]'(by omega) = C.gates[t] := fun t ht => by
    simp [hG, plus]
  have hsrc : ∀ x : List Bool, x.length = n → (G.foldl step x).getD n false = true :=
    fun x hx => plus_getD_src' C n x hx
  have hbigv : ∀ x : List Bool, x.length = n → (G.foldl step x).getD big false = false :=
    fun x hx => getD_of_length_le _ _ (by rw [foldl_step_length, hx])
  have hgv : ∀ x : List Bool, x.length = n → ∀ t (ht : t < C.gates.length),
      (G.foldl step x).getD (n + 1 + t) false =
        (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
          if i < n + 1 + t then (G.foldl step x).getD i false else false) := by
    intro x hx t ht
    have := gate_value G x (t + 1) (by omega)
    rw [hx, hGt t ht, show n + (t + 1) = n + 1 + t by omega] at this
    exact this
  have hfanC : ∀ t (ht : t < C.gates.length),
      ((C.gates[t]).op = GateOp.and ∨ (C.gates[t]).op = GateOp.or ∨ (C.gates[t]).op = GateOp.not) ∧
        (C.gates[t]).inputs.length ≤ 2 := by
    intro t ht
    have := hmin.1 _ (List.getElem_mem ht)
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hconst : ∀ (w : ℕ) (b : Bool), (∀ x : List Bool, x.length = n → (G.foldl step x).getD w false = b) →
      C.output = w → False := by
    intro w b hw ho
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← plus_eval_eq, ← plus_eval_eq, ho, hw _ (by simp), hw _ (by simp)]
  have hout : C.output ≠ p := fun h => hconst p bj hWp h
  -- a smaller circuit for the restriction contradicts the size hypothesis
  have M2 : ∀ (d₁ d₂ d₃ : ℕ × ℕ), d₁.1 ≠ d₂.1 → d₁.1 ≠ d₃.1 → d₂.1 ≠ d₃.1 →
      (∀ d ∈ [d₁, d₂, d₃], d.1 < G.length) →
      (∀ d ∈ [d₁, d₂, d₃], d.2 < n + d.1 ∨ n + G.length ≤ d.2) →
      (∀ d ∈ [d₁, d₂, d₃], Just n G C.output [d₁, d₂, d₃] d) → False := by
    intro d₁ d₂ d₃ h12 h13 h23 hlt hval hjust
    obtain ⟨D, hDfan, hDsize, hDeval⟩ :=
      smaller3 n G C.output d₁ d₂ d₃ h12 h13 h23 hlt hval hjust (plus_fanInTwo C hmin.1)
    have h1 := hlt d₁ (by simp)
    have h2 := hlt d₂ (by simp)
    have h3 := hlt d₃ (by simp)
    have hhas : HasCircuitSize n (fun y => circuitFun (n + 1) C (Fin.snoc y true)) (C.gates.length - 2) := by
      refine ⟨D, hDfan, by rw [hDsize, hGlen]; omega, fun y => ?_⟩
      rw [hDeval (List.ofFn y) (by simp)]
      show Circuit.eval ⟨G, C.output⟩ (List.ofFn y) = circuitFun (n + 1) C (Fin.snoc y true)
      rw [← plus_eval_eq]
      rfl
    have := hH3 _ hhas
    simp only [Circuit.size] at this
    omega
  -- the single deletion in `C` itself
  have M1 : ∀ r : ℕ, (r < p ∨ n + 1 + C.gates.length ≤ r) →
      Just (n + 1) C.gates C.output [(j, r)] (j, r) → False := by
    intro r hr hjust
    obtain ⟨D, hDfan, hDsize, hDeval⟩ := smaller (n + 1) C.gates C.output [(j, r)] (by simp)
      (by simp [hj]) (by simpa using hr) (by simpa using hjust) hmin.1
    have hfun : circuitFun (n + 1) D = circuitFun (n + 1) C := by
      funext z
      simp only [circuitFun]
      rw [hDeval (List.ofFn z) (by simp)]
    have := hmin.2 D hDfan hfun
    simp only [Circuit.size, List.length_singleton] at this hDsize
    omega
  -- readers of `p` later than `j`
  by_cases hex : ∃ t, ∃ ht : t < C.gates.length, j < t ∧ p ∈ deps C.gates[t]
  swap
  · refine M1 (n + 1 + C.gates.length) (Or.inr le_rfl) (Or.inr ⟨fun t ht hjt _ hmem => hex ⟨t, ht, hjt, hmem⟩, hout, ?_⟩)
    simp
  obtain ⟨t₁, ht₁, hjt₁, hr₁⟩ := hex
  set q₁ := n + 1 + t₁ with hq₁
  set rep₁ := repOf (C.gates[t₁]) p q₁ bj n big with hrep₁
  have hv₁ : ∀ x : List Bool, x.length = n → (G.foldl step x).getD q₁ false = (G.foldl step x).getD rep₁ false :=
    fun x hx => reader_value (C.gates[t₁]) (hfanC t₁ ht₁).1 (hfanC t₁ ht₁).2 p q₁ bj _ n big hr₁ (by omega)
      (by omega) (hWp x hx) (hsrc x hx) (hbigv x hx) (hgv x hx t₁ ht₁)
  have hval₁ : rep₁ < q₁ ∨ rep₁ = big := repOf_valid _ _ _ _ _ _ (by omega)
  have hne₁ : rep₁ ≠ p := repOf_ne _ _ _ _ _ _ (by omega) (by omega)
  -- the value of the bad gate as a replacement wire
  set rep₀ : ℕ := if bj then n else big with hrep₀
  have hv₀ : ∀ x : List Bool, x.length = n → (G.foldl step x).getD p false = (G.foldl step x).getD rep₀ false := by
    intro x hx
    rw [hWp x hx, hrep₀]
    cases bj
    · simp only [Bool.false_eq_true, ite_false]
      exact (hbigv x hx).symm
    · simp only [eq_self_iff_true, ite_true]
      exact (hsrc x hx).symm
  have hval₀ : rep₀ < p ∨ rep₀ = big := by
    rw [hrep₀]
    cases bj
    · exact Or.inr (by simp)
    · exact Or.inl (by simp; omega)
  have hpj : n + (j + 1) = p := by omega
  have hq₁t : n + (t₁ + 1) = q₁ := by omega
  -- S1: another reader of the last input
  by_cases h1 : ∃ t, ∃ ht : t < C.gates.length, t ≠ j ∧ t ≠ t₁ ∧ n ∈ deps C.gates[t]
  · obtain ⟨t, ht, htj, htt₁, hrt⟩ := h1
    set q := n + 1 + t with hq
    set rep := repOf (C.gates[t]) n q true n big with hrep
    have hv : ∀ x : List Bool, x.length = n → (G.foldl step x).getD q false = (G.foldl step x).getD rep false :=
      fun x hx => reader_value (C.gates[t]) (hfanC t ht).1 (hfanC t ht).2 n q true _ n big hrt (by omega)
        (by omega) (hsrc x hx) (hsrc x hx) (hbigv x hx) (hgv x hx t ht)
    have hval : rep < q ∨ rep = big := repOf_valid _ _ _ _ _ _ (by omega)
    refine M2 (j + 1, rep₀) (t₁ + 1, rep₁) (t + 1, rep) (by simp; omega) (by simp; omega) (by simp; omega)
      (by simp; omega) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl)
      · simp only; rcases hval₀ with h | h <;> omega
      · simp only; rcases hval₁ with h | h <;> omega
      · simp only; rcases hval with h | h <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl)
      · exact Or.inl fun x hx => by rw [show n + (j + 1) = p by omega]; exact hv₀ x hx
      · exact Or.inl fun x hx => by rw [show n + (t₁ + 1) = q₁ by omega]; exact hv₁ x hx
      · exact Or.inl fun x hx => by rw [show n + (t + 1) = q by omega]; exact hv x hx
  -- S2: another reader of the bad gate
  by_cases h2 : ∃ t, ∃ ht : t < C.gates.length, j < t ∧ t ≠ t₁ ∧ p ∈ deps C.gates[t]
  · obtain ⟨t, ht, htj, htt₁, hrt⟩ := h2
    set q := n + 1 + t with hq
    set rep := repOf (C.gates[t]) p q bj n big with hrep
    have hv : ∀ x : List Bool, x.length = n → (G.foldl step x).getD q false = (G.foldl step x).getD rep false :=
      fun x hx => reader_value (C.gates[t]) (hfanC t ht).1 (hfanC t ht).2 p q bj _ n big hrt (by omega)
        (by omega) (hWp x hx) (hsrc x hx) (hbigv x hx) (hgv x hx t ht)
    have hval : rep < q ∨ rep = big := repOf_valid _ _ _ _ _ _ (by omega)
    refine M2 (j + 1, rep₀) (t₁ + 1, rep₁) (t + 1, rep) (by simp; omega) (by simp; omega) (by simp; omega)
      (by simp; omega) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl)
      · simp only; rcases hval₀ with h | h <;> omega
      · simp only; rcases hval₁ with h | h <;> omega
      · simp only; rcases hval with h | h <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl)
      · exact Or.inl fun x hx => by rw [show n + (j + 1) = p by omega]; exact hv₀ x hx
      · exact Or.inl fun x hx => by rw [show n + (t₁ + 1) = q₁ by omega]; exact hv₁ x hx
      · exact Or.inl fun x hx => by rw [show n + (t + 1) = q by omega]; exact hv x hx
  -- no other reader of the last input nor of the bad gate: the first reader is constant or a copy
  have hun_n : ∀ t (ht : t < C.gates.length), t ≠ j → t ≠ t₁ → n ∉ deps C.gates[t] :=
    fun t ht htj htt₁ hmem => h1 ⟨t, ht, htj, htt₁, hmem⟩
  have hun_p : ∀ t (ht : t < C.gates.length), j < t → t ≠ t₁ → p ∉ deps C.gates[t] :=
    fun t ht hjt htt₁ hmem => h2 ⟨t, ht, hjt, htt₁, hmem⟩
  have hout_n : C.output ≠ n := fun h => hconst n true hsrc h
  by_cases hc1 : rep₁ = n ∨ rep₁ = big
  · -- constant first reader
    set b₁ : Bool := decide (rep₁ = n) with hb₁
    have hWq₁ : ∀ x : List Bool, x.length = n → (G.foldl step x).getD q₁ false = b₁ := by
      intro x hx
      rw [hv₁ x hx, hb₁]
      rcases hc1 with h | h
      · rw [h, hsrc x hx]; simp
      · rw [h, hbigv x hx]
        have : ¬ (big = n) := by omega
        simp [this]
    have hout₁ : C.output ≠ q₁ := fun h => hconst q₁ b₁ hWq₁ h
    by_cases h3 : ∃ t, ∃ ht : t < C.gates.length, t₁ < t ∧ q₁ ∈ deps C.gates[t]
    · obtain ⟨t, ht, ht₁t, hrt⟩ := h3
      set q := n + 1 + t with hq
      set rep := repOf (C.gates[t]) q₁ q b₁ n big with hrep
      have hv : ∀ x : List Bool, x.length = n → (G.foldl step x).getD q false = (G.foldl step x).getD rep false :=
        fun x hx => reader_value (C.gates[t]) (hfanC t ht).1 (hfanC t ht).2 q₁ q b₁ _ n big hrt (by omega)
          (by omega) (hWq₁ x hx) (hsrc x hx) (hbigv x hx) (hgv x hx t ht)
      have hval : rep < q ∨ rep = big := repOf_valid _ _ _ _ _ _ (by omega)
      refine M2 (j + 1, rep₀) (t₁ + 1, rep₁) (t + 1, rep) (by simp; omega) (by simp; omega) (by simp; omega)
        (by simp; omega) ?_ ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro d (rfl | rfl | rfl)
        · simp only; rcases hval₀ with h | h <;> omega
        · simp only; rcases hval₁ with h | h <;> omega
        · simp only; rcases hval with h | h <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro d (rfl | rfl | rfl)
        · exact Or.inl fun x hx => by rw [show n + (j + 1) = p by omega]; exact hv₀ x hx
        · exact Or.inl fun x hx => by rw [show n + (t₁ + 1) = q₁ by omega]; exact hv₁ x hx
        · exact Or.inl fun x hx => by rw [show n + (t + 1) = q by omega]; exact hv x hx
    · -- delete the bad gate, its reader and the source, all unread
      have hun_q : ∀ t (ht : t < C.gates.length), t₁ < t → q₁ ∉ deps C.gates[t] :=
        fun t ht ht₁t hmem => h3 ⟨t, ht, ht₁t, hmem⟩
      refine M2 (j + 1, big) (t₁ + 1, big) (0, big) (by simp; omega) (by simp) (by simp) (by simp; omega) ?_ ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro d (rfl | rfl | rfl) <;> simp only <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro d (rfl | rfl | rfl)
        · refine Or.inr ⟨fun t' ht' hlt hnot hmem => ?_, fun h => hout (h.trans hpj), ?_⟩
          · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
            rw [hGt t'' (by omega)] at hmem
            exact hun_p t'' (by omega) (by omega) (fun h => hnot (t₁ + 1, big) (by simp) (by rw [h])) (by rw [hpj] at hmem; exact hmem)
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro d (rfl | rfl | rfl) <;> simp <;> omega
        · refine Or.inr ⟨fun t' ht' hlt hnot hmem => ?_, fun h => hout₁ (h.trans hq₁t), ?_⟩
          · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
            rw [hGt t'' (by omega)] at hmem
            exact hun_q t'' (by omega) (by omega) (by rw [hq₁t] at hmem; exact hmem)
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro d (rfl | rfl | rfl) <;> simp <;> omega
        · refine Or.inr ⟨fun t' ht' hlt hnot hmem => ?_, fun h => hout_n (by simpa using h), ?_⟩
          · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
            rw [hGt t'' (by omega)] at hmem
            exact hun_n t'' (by omega) (fun h => hnot (j + 1, big) (by simp) (by rw [h]))
              (fun h => hnot (t₁ + 1, big) (by simp) (by rw [h])) (by simpa using hmem)
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro d (rfl | rfl | rfl) <;> simp <;> omega
  · -- the first reader is a copy of an earlier wire: delete the bad gate, the reader and the source
    have hc1' : rep₁ ≠ n ∧ rep₁ ≠ big := by tauto
    refine M2 (j + 1, big) (t₁ + 1, rep₁) (0, big) (by simp; omega) (by simp) (by simp) (by simp; omega) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl)
      · simp only; omega
      · simp only; rcases hval₁ with h | h <;> omega
      · simp only; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl)
      · refine Or.inr ⟨fun t' ht' hlt hnot hmem => ?_, fun h => hout (h.trans hpj), ?_⟩
        · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
          rw [hGt t'' (by omega)] at hmem
          exact hun_p t'' (by omega) (by omega) (fun h => hnot (t₁ + 1, rep₁) (by simp) (by rw [h])) (by rw [hpj] at hmem; exact hmem)
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro d (rfl | rfl | rfl) <;> simp <;> omega
      · exact Or.inl fun x hx => by rw [show n + (t₁ + 1) = q₁ by omega]; exact hv₁ x hx
      · refine Or.inr ⟨fun t' ht' hlt hnot hmem => ?_, fun h => hout_n (by simpa using h), ?_⟩
        · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
          rw [hGt t'' (by omega)] at hmem
          exact hun_n t'' (by omega) (fun h => hnot (j + 1, big) (by simp) (by rw [h]))
            (fun h => hnot (t₁ + 1, rep₁) (by simp) (by rw [h])) (by simpa using hmem)
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro d (rfl | rfl | rfl) <;> simp <;> omega

theorem one_deletion (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit (n + 1) C) (j : ℕ) (hj : j < C.gates.length)
    (r : ℕ) (hr : r < n + 1 + j ∨ n + 1 + C.gates.length ≤ r)
    (hjust : Just (n + 1) C.gates C.output [(j, r)] (j, r)) : False := by
  obtain ⟨D, hDfan, hDsize, hDeval⟩ := smaller (n + 1) C.gates C.output [(j, r)] (by simp)
    (by simp [hj]) (by simpa using hr) (by simpa using hjust) hmin.1
  have hfun : circuitFun (n + 1) D = circuitFun (n + 1) C := by
    funext z
    simp only [circuitFun]
    rw [hDeval (List.ofFn z) (by simp)]
  have := hmin.2 D hDfan hfun
  simp only [Circuit.size, List.length_singleton] at this hDsize
  omega

theorem main_thm (n : ℕ) (C : Circuit) (hmin : IsMinimalCircuit (n + 1) C)
    (hnc : ∃ y y' : Fin n → Bool,
      circuitFun (n + 1) C (Fin.snoc y true) ≠ circuitFun (n + 1) C (Fin.snoc y' true))
    (hH3 : ∀ s : ℕ, HasCircuitSize n (fun y : Fin n → Bool => circuitFun (n + 1) C (Fin.snoc y true)) s →
      C.size ≤ s + 1)
    (j : ℕ) (hj : j < C.gates.length)
    (hread : (C.gates[j]).op = GateOp.not ∧ (C.gates[j]).inputs.head? = some n ∨
      (C.gates[j]).op ≠ GateOp.not ∧ n ∈ (C.gates[j]).inputs) :
    (C.gates[j]).op = GateOp.and ∧ (C.gates[j]).inputs.length = 2 ∧ n ∈ (C.gates[j]).inputs ∧
      ∃ w ∈ (C.gates[j]).inputs, w ≠ n ∧ w < n + 1 + j := by
  classical
  have hvalC : ∀ x : List Bool, x.length = n + 1 →
      (C.gates.foldl step x).getD (n + 1 + j) false = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < n + 1 + j then (C.gates.foldl step x).getD i false else false) := by
    intro x hx
    have := gate_value C.gates x j hj
    rw [hx] at this
    exact this
  have hvalP : ∀ x : List Bool, x.length = n →
      ((plus C).gates.foldl step x).getD (n + 1 + j) false = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < n + 1 + j then ((plus C).gates.foldl step x).getD i false else false) := by
    intro x hx
    have := gate_value (plus C).gates x (j + 1) (by simp [plus]; omega)
    rw [hx, show n + (j + 1) = n + 1 + j by omega] at this
    simpa [plus] using this
  have hsrc : ∀ x : List Bool, x.length = n → ((plus C).gates.foldl step x).getD n false = true :=
    fun x hx => plus_getD_src' C n x hx
  have hbigC : ∀ x : List Bool, x.length = n + 1 →
      (C.gates.foldl step x).getD (n + 1 + C.gates.length) false = false :=
    fun x hx => getD_of_length_le _ _ (by rw [foldl_step_length, hx])
  have M1 : ∀ r : ℕ, (r < n + 1 + j ∨ n + 1 + C.gates.length ≤ r) →
      (∀ x : List Bool, x.length = n + 1 →
        (C.gates.foldl step x).getD (n + 1 + j) false = (C.gates.foldl step x).getD r false) → False :=
    fun r hr hv => one_deletion n C hmin j hj r hr (Or.inl hv)
  obtain ⟨hop, hlen⟩ := hmin.1 _ (List.getElem_mem hj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hnp : n < n + 1 + j := by omega
  rcases hl : (C.gates[j]).inputs with _ | ⟨a, _ | ⟨d, _ | ⟨e, l'⟩⟩⟩
  · rw [hl] at hread
    simp at hread
  · rw [hl] at hread
    have ha : a = n := by
      rcases hread with ⟨_, h⟩ | ⟨_, h⟩ <;> simpa [eq_comm] using h
    subst a
    rcases hop with hop | hop | hop
    · exact (M1 n (Or.inl hnp) fun x hx => by
        rw [hvalC x hx, hl, hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
          hnp, ite_true]).elim
    · exact (M1 n (Or.inl hnp) fun x hx => by
        rw [hvalC x hx, hl, hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false,
          hnp, ite_true]).elim
    · exact (bad_case n C hmin hnc hH3 j hj false fun x hx => by
        rw [hvalP x hx, hl, hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hnp, ite_true, hsrc x hx,
          Bool.not_true]).elim
  · rw [hl] at hread
    rcases hop with hop | hop | hop
    · have hmem : n = a ∨ n = d := by
        rcases hread with ⟨h, _⟩ | ⟨_, h⟩
        · rw [hop] at h; cases h
        · simpa using h
      by_cases ha : a = n <;> by_cases hd : d = n
      · subst a; subst d
        exact (M1 n (Or.inl hnp) fun x hx => by
          rw [hvalC x hx, hl, hop]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
            hnp, ite_true, Bool.and_self]).elim
      · subst a
        by_cases hdp : d < n + 1 + j
        · exact ⟨hop, rfl, by simp, d, by simp, hd, hdp⟩
        · exact (M1 _ (Or.inr le_rfl) fun x hx => by
            rw [hvalC x hx, hl, hop, hbigC x hx]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
              hdp, ite_false, Bool.and_false]).elim
      · subst d
        by_cases hap : a < n + 1 + j
        · exact ⟨hop, rfl, by simp, a, by simp, ha, hap⟩
        · exact (M1 _ (Or.inr le_rfl) fun x hx => by
            rw [hvalC x hx, hl, hop, hbigC x hx]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
              hap, ite_false, Bool.false_and]).elim
      · rcases hmem with h | h
        · exact absurd h.symm ha
        · exact absurd h.symm hd
    · have hmem : n = a ∨ n = d := by
        rcases hread with ⟨h, _⟩ | ⟨_, h⟩
        · rw [hop] at h; cases h
        · simpa using h
      by_cases ha : a = n <;> by_cases hd : d = n
      · subst a; subst d
        exact (M1 n (Or.inl hnp) fun x hx => by
          rw [hvalC x hx, hl, hop]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false,
            hnp, ite_true, Bool.or_self]).elim
      · subst a
        by_cases hdp : d < n + 1 + j
        · exact (bad_case n C hmin hnc hH3 j hj true fun x hx => by
            rw [hvalP x hx, hl, hop]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false,
              hnp, ite_true, hsrc x hx, Bool.true_or]).elim
        · exact (M1 n (Or.inl hnp) fun x hx => by
            rw [hvalC x hx, hl, hop]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false,
              hnp, ite_true, hdp, ite_false]).elim
      · subst d
        by_cases hap : a < n + 1 + j
        · exact (bad_case n C hmin hnc hH3 j hj true fun x hx => by
            rw [hvalP x hx, hl, hop]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false,
              hnp, ite_true, hsrc x hx, Bool.or_true]).elim
        · exact (M1 n (Or.inl hnp) fun x hx => by
            rw [hvalC x hx, hl, hop]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false,
              hnp, ite_true, hap, ite_false, Bool.false_or]).elim
      · rcases hmem with h | h
        · exact absurd h.symm ha
        · exact absurd h.symm hd
    · have ha : a = n := by
        rcases hread with ⟨_, h⟩ | ⟨h, _⟩
        · simpa using h
        · exact absurd hop h
      subst a
      exact (bad_case n C hmin hnc hH3 j hj false fun x hx => by
        rw [hvalP x hx, hl, hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hnp, ite_true, hsrc x hx,
          Bool.not_true]).elim
  · rw [hl] at hlen
    simp at hlen

end L171

end PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_171 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' true)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) s → C.size ≤ s + 1) → ∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get j).inputs.length = 2 ∧ n ∈ (C.gates.get j).inputs ∧ ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val := by
  intro n C hmin _ hnc hH3 j hread
  simp only [List.get_eq_getElem] at hread ⊢
  exact PEqualNP.Outside.L171.main_thm n C hmin hnc hH3 j.1 j.2 hread
