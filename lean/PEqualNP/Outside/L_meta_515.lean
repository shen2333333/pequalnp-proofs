import Mathlib
import PEqualNP.Defs

namespace Live515

variable {α : Type} [DecidableEq α]

-- The ordinary circuit may consult any earlier result.
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

-- A live set contains just the wires actually read by the remaining computation.
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

-- Any pair of rows which the output separates must stay separated at each cut.
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

end Live515

namespace Live515
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Live515

namespace Check515

abbrev W := BitVec 344
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 172)).setWidth 172
def cuts (ws : List W) : BitVec 172 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 172) ++ (0 : BitVec 172)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

def advance (k : ℕ) (next : List W → Bool) (a b : W) (rest : List W) : Bool :=
  let ds := ops a b
  let base := cuts rest
  let attempt := fun (kept : List W) (covered : BitVec 172) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

def rawInputs : List W :=
  [0x707c07e1007e538c9800ce03e39f21073f193673000002402610026518c880000012089210113191631,
   0x319a591990619909f30fc64b4cc92648624c861f87f318a491890618908630346494c49224862448606846,
   0xc21c9e21e3821e31cc0e187390f1c783838f181cf9cc2149621638216318c0c181290b04583808b1818298,
   0x3e0e03e0003e03e0ff0607c1f01f80c03f01fe0fe000a0000a0000a0000150606c0501b80c037002a0d60,
   0xfc00ffc003fc003ff0007f801ffe000ffc001fff0005400ffc002b4003ff0000a801afe0002b4001d5f000,
   0xffff000003ffffc000007fffe000000fffffe000000abff0000014bfd800000757fe000000d4beec000000,
   0xfffffffffc00000000007ffffffffff000000000000fffffdbfd800000000007fffffedf76000000000000,
   0xffffffffffffffffffff80000000000000000000000ff5ffff5ffff5ffffeaf80000000000000000000000]

def inputs := rawInputs.map canon

end Check515
namespace Check515
variable {α : Type}

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end Check515

namespace Check515
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 172) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (172+i.val)

theorem neg_differs (i : Fin 172) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 344 := by omega
  have hi : 172+i.val < 344 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 172) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 172) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (172+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (172+i.val) := by simpa [differs] using h.2
  have lo : i.val < 344 := by omega
  have hi : 172+i.val < 344 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 172) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬172 + i.val < 172 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 172) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : Live515.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := Live515.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 172)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end Check515

namespace Check515

def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

theorem advance_has {k : ℕ} {next : List W → Bool} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hn : kept.length+1 ≤ k+1) (hc : cuts (z::kept) = -1) (ht : next (z::kept) = true) :
    advance k next a b r = true := by
  have hh : (ops a b).any (fun w => (cuts kept ||| sep w == -1) && next (w :: kept)) := by
    apply List.any_eq_true.mpr
    refine ⟨z, by simpa [basicOps] using hz, ?_⟩
    change sep z ||| cuts kept = -1 at hc
    simp [BitVec.or_comm (cuts kept), hc, ht]
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [advance, hn, ite_true, cuts, List.foldr_cons] at * <;> simp_all

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem search_complete (n : ℕ) (ws : List W) (hn : ws.Nodup)
    (h : Live515.live basicOps goal n ws.toFinset) : search n ws = true := by
  induction n generalizing ws with
  | zero => simp [search, singleton_list hn h]
  | succ k ih =>
    rcases Live515.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [search, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          advance k (search k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live515.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        apply advance_has hop hk _ (cuts_full hl) (ih _ hnd hl)
        have hc := Live515.live_card hl
        rw [List.toFinset_card_of_nodup hnd] at hc
        exact hc
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check515

namespace Check515
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 344) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 344) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩


theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)


def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 344 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 172) ++ (0 : BitVec 172))) :
    Live515.build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 172) ++ (0 : BitVec 172)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 172) ++ (0 : BitVec 172)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 172) ++ (0 : BitVec 172)) := by
      intro k; simpa only [List.foldl_cons,hstep] using he k
    have appendOK (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr h)) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
      · simp_all


def graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
  (x 0 && x 5) || (x 0 && x 6) || (x 3 && x 7)

def assignment (k : Fin 344) (i : Fin 8) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live515.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 172) := [1, 0, 2, 7, 17, 25, 48, 96]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (172+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live515.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 344) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 344) : graph (assignment k) =
    bit k ((-1 : BitVec 172) ++ (0 : BitVec 172)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
      (x 4 &&& x 5) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 7) =
      ((-1 : BitVec 172) ++ (0 : BitVec 172)) := by decide
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 344) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 172) ++ (0 : BitVec 172)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    Live515.build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : Live515.build basicOps goal k inputs.toFinset) :
    Live515.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := Live515.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : Live515.live basicOps goal m inputs.toFinset) :
    Live515.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem lower_of_check (check : search 10 inputs = false) (s : ℕ)
    (h : HasCircuitSize 8 graph s) : 11 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 10 := by change C.gates.length ≤ s at hsize; omega
  have searched := search_complete 10 inputs (by decide) (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check515
namespace Check515

def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩

end Check515

namespace Check515

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live515.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases Live515.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live515.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := Live515.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem lower_of_optimized (check : optimized 10 3 inputs = false) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize 8 graph s) : 11 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 10 := by change C.gates.length ≤ s at hsize; omega
  have searched := optimized_complete 10 inputs 3 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check515

namespace Live515
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]

theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]

theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]

theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le

theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩

def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

theorem zeros_step {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r)+1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := by intro h; exact fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega

theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

theorem project_live {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    induction n with
    | zero => exact mem
    | succ n ih => exact Or.inl (ih (by omega))
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha|hb|⟨u,w,hA,hB,hw,hop⟩
        · apply free
          simp [kept_insert, hZ, ha]
        · apply free
          simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert,hZ,hA,hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert,hA], w, by simp [kept_insert,hB],
                hw, v, hop, build_mono covers next⟩

end Live515

namespace Check515

abbrev Half := BitVec 172
def fill (m : Half) (r : Fin 172) (x : Half) : Half :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)

def crop (m : Half) (r : Fin 172) (x : W) : W :=
  (fill m r ((x >>> 172).setWidth 172)) ++ (fill m r (x.setWidth 172))

theorem fill_bit (m x : Half) (r : Fin 172) {i : ℕ} (hi : i < 172) :
    (fill m r x)[i] = if m[i] then x[i] else x[r.val] := by
  unfold fill
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr, hm]

def pos (m : Half) (r : Fin 172) (i : Nat) :=
  if i < 172 then (if m.getLsbD i then i else r.val)
  else (if m.getLsbD (i-172) then i else 172+r.val)

theorem pos_lt (m : Half) (r : Fin 172) {i : Nat} (hi : i < 344) : pos m r i < 344 := by
  unfold pos; split <;> split <;> omega

theorem fill_lsb (m x : Half) (r : Fin 172) {i : Nat} (hi : i < 172) :
    (fill m r x).getLsbD i = if m.getLsbD i then x.getLsbD i else x.getLsbD r.val := by
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem r.isLt] using fill_bit m x r hi

theorem crop_bit (m : Half) (r : Fin 172) (x : W) (i : ℕ) (hi : i < 344) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_append]
  by_cases h : i < 172
  · rw [if_pos h, if_pos h, fill_lsb _ _ _ h]
    cases e : m.getLsbD i <;> simp only [BitVec.getLsbD_setWidth, h, r.isLt, decide_true,
      Bool.true_and, Bool.false_eq_true, if_false, if_true]
  · have hr : i-172 < 172 := by omega
    rw [if_neg h, if_neg h, fill_lsb _ _ _ hr]
    cases e : m.getLsbD (i-172) <;> simp only [BitVec.getLsbD_setWidth, hr, r.isLt,
      decide_true, Bool.true_and, Bool.false_eq_true, if_false, if_true, BitVec.getLsbD_ushiftRight,
      show 172+(i-172)=i by omega]

theorem crop_and (m : Half) (r : Fin 172) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

theorem crop_neg (m : Half) (r : Fin 172) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

def cropOpt (m : Half) (r : Fin 172) (x : W) := wrap (crop m r x)

theorem crop_canon (m : Half) (r : Fin 172) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

set_option maxRecDepth 2500 in
theorem crop_goal (m : Half) (r : Fin 172) : cropOpt m r goal = some goal := by
  have g : goal = (BitVec.allOnes 172 ++ (0 : Half)) := by decide
  have eq : crop m r goal = goal := by
    change (fill m r (BitVec.allOnes 172) ++ fill m r 0) = (BitVec.allOnes 172 ++ (0 : Half))
    congr 1
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp only [BitVec.getElem_allOnes, ite_self]
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp

  rw [cropOpt, eq]
  decide

set_option maxRecDepth 2500 in
theorem binary_project {x y v : W} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps u w := by
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 344 := by
    rcases sign t with h'|h' <;> rw [ht] at h'
    · exact .inl h'
    · exact .inr h'
  by_cases hx : canon x = 0
  · rcases trivial _ hx with rfl|rfl
    · rw [show (0 : W) &&& y = 0 from BitVec.zero_and] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.allOnes_and] at h; exact .inr (.inl h)
  by_cases hy : canon y = 0
  · rcases trivial _ hy with rfl|rfl
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.and_allOnes] at h; exact .inl h
  have hn : canon (x &&& y) ≠ 0 := by intro hn; simp [wrap, hn] at h
  have hval : canon (x &&& y) = v := by simpa only [wrap, if_neg hn, Option.some.injEq] using h
  by_cases eq : canon x = canon y
  · rcases same_both eq with same|bad
    · exact .inl (by simp only [wrap, if_neg hx, ← hval, same])
    · exact False.elim (hn bad)
  · exact .inr (.inr ⟨canon x,canon y,by simp only [wrap,if_neg hx],by simp only [wrap,if_neg hy],eq,
        hval ▸ signed_both (sign x) (sign y)⟩)

theorem mask_projects (m : Half) (r : Fin 172) : Live515.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

end Check515

namespace Check515

def maybeBuild (n : Nat) (av : List W) : Bool :=
  av.sublists.any (fun ws => ws.length ≤ n+1 && cuts ws == -1 &&
    optimized n (n+1-ws.length) ws)

theorem maybeBuild_complete {n : ℕ} {av : List W} (hn : av.Nodup)
    (h : Live515.build basicOps goal n av.toFinset) : maybeBuild n av = true := by
  obtain ⟨s,hs,hr⟩ := Live515.compress h
  let xs := av.filter (fun a => decide (a ∈ s))
  have hsub : xs.Sublist av := List.filter_sublist
  have hnd : xs.Nodup := hn.sublist hsub
  have heq : xs.toFinset = s := by
    ext a
    simp only [List.mem_toFinset, xs, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hs ha),ha⟩⟩
  rw [←heq] at hr
  have bound := Live515.live_card hr
  rw [List.toFinset_card_of_nodup hnd] at bound
  apply List.any_eq_true.mpr
  refine ⟨xs,List.mem_sublists.mpr hsub,?_⟩
  have ok := optimized_complete n xs (n+1-xs.length) hnd (by omega) hr
  simp [bound, cuts_full hr, ok]

def projectedBudget (m : Half) (r : Fin 172) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length

def available (m : Half) (r : Fin 172) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup

theorem available_spec (m : Half) (r : Fin 172) (ws : List W) :
    (available m r ws).toFinset = Live515.kept (cropOpt m r) ws.toFinset := by
  ext y; simp [available, Live515.kept, List.mem_filterMap]

theorem projected_bound (m : Half) (r : Fin 172) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + Live515.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega

theorem projection_survives (m : Half) (r : Fin 172) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (h : Live515.live basicOps goal k ws.toFinset) :
    maybeBuild (projectedBudget m r k ws) (available m r ws) = true := by
  have hbuild := Live515.project_live (crop_goal m r) (mask_projects m r) h _ (projected_bound m r k hn)
  rw [← available_spec] at hbuild
  exact maybeBuild_complete (List.nodup_dedup _) hbuild

end Check515

namespace Check515

abbrev Claim := Nat × List W
abbrev Hint := Half × Fin 172 × Nat

def goodClaim (c : Claim) : Bool := decide c.2.Nodup && !(maybeBuild c.1 c.2)

def usable (c : Claim) (m : Half) (r : Fin 172) (n : Nat) (ws : List W) : Bool :=
  projectedBudget m r n ws ≤ c.1 &&
  ws.all (fun w => match cropOpt m r w with | none => true | some y => c.2.contains y)

theorem unusable (c : Claim) (m : Half) (r : Fin 172) {n : Nat} {ws : List W}
    (hn : ws.Nodup) (live : Live515.live basicOps goal n ws.toFinset) (hc : goodClaim c) :
    usable c m r n ws = false := by
  apply Bool.eq_false_iff.mpr
  intro u
  simp only [goodClaim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  simp only [usable, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at u
  have budget := projected_bound m r n hn
  have bound : n ≤ c.1 + Live515.zeros (cropOpt m r) ws.toFinset := by omega
  have build := Live515.project_live (crop_goal m r) (mask_projects m r) live _ bound
  have sub : Live515.kept (cropOpt m r) ws.toFinset ⊆ c.2.toFinset := by
    intro y hy
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hy
    have hy' : cropOpt m r w = some y := by simpa using hv
    have hu := u.2 w (List.mem_toFinset.mp hw)
    simpa [hy'] using hu
  have ok := maybeBuild_complete hc.1 (Live515.build_mono sub build)
  exact Bool.noConfusion (hc.2.symm.trans ok)

def key (n : Nat) (ws : List W) : Nat := ws.foldl (fun h w => (65599*h+w.toNat)%1000000007) n

def matched (table : List Claim) (hint : Nat → Option Hint) (n : Nat) (ws : List W) : Bool :=
  match hint (key n ws) with
  | none => false
  | some (m,r,j) => (table[j]?).any (fun c => usable c m r n ws)

theorem matched_false {table : List Claim} (ht : table.all goodClaim = true)
    (hint : Nat → Option Hint) {n : Nat} {ws : List W} (hn : ws.Nodup)
    (h : Live515.live basicOps goal n ws.toFinset) : matched table hint n ws = false := by
  unfold matched
  cases hh : hint (key n ws) with
  | none => rfl
  | some data =>
    obtain ⟨m,r,j⟩ := data
    change (table[j]?).any (fun c => usable c m r n ws) = false
    cases he : table[j]? with
    | none => rfl
    | some c =>
      exact unusable c m r hn h (List.all_eq_true.mp ht c (List.mem_of_getElem? he))

def front (table : List Claim) (hint : Nat → Option Hint) : Nat → Nat → Nat → List W → Bool
  | 0, n, _, ws => !(matched table hint n ws)
  | depth+1, n, extra, ws =>
    !(matched table hint n ws) && (ws == [goal] ||
      (pairs ws).any (fun (a,b,r) => dispatch extra (front table hint depth (n-1)) a b r))

theorem front_complete {table : List Claim} (ht : table.all goodClaim = true) (hint : Nat → Option Hint)
    (depth n : Nat) (ws : List W) (extra : Nat) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live515.live basicOps goal n ws.toFinset) :
    front table hint depth n extra ws = true := by
  induction depth generalizing n ws extra with
  | zero => simp [front, matched_false ht hint hn h]
  | succ depth ih =>
    simp only [front, matched_false ht hint hn h, Bool.not_false, Bool.true_and]
    cases n with
    | zero => simp [singleton_list hn h]
    | succ k =>
      simp only [Nat.add_one_sub_one]
      rcases Live515.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
      · simp [singleton_list hn done]
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go {a b : W} (perm : ws.Perm (a::b::r))
            (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
            dispatch extra (front table hint depth k) a b r = true := by
          obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
          have hl : Live515.live basicOps goal k (z::kept).toFinset := by
            simpa [hfin] using tail
          have hc := Live515.live_card hl
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
          have len := perm.length_eq
          simp only [List.length_cons] at len
          apply dispatch_complete (k := k) (extra := extra) (front table hint depth k) hop hk (by omega) (by omega) (cuts_full hl)
          apply ih _ _ _ hnd _ hl
          simp; omega
        simp only [Bool.or_eq_true, List.any_eq_true]
        right
        rcases hm with direct | swap
        · exact ⟨(a,b,r), direct, go hp hs hz⟩
        · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem lower_of_front (table : List Claim) (hint : Nat → Option Hint) (depth : Nat)
    (ht : table.all goodClaim = true) (check : front table hint depth 10 3 inputs = false)
    (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 8 graph s) : 11 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 10 := by change C.gates.length ≤ s at hsize; omega
  have searched := front_complete ht hint depth 10 inputs 3 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check515

namespace Check515
def checkedSet0 : Claim := (6, [0x100c00c1000c400c000042006183010306180000000000400410004400c000000002081010102180000, 0xc0100c00c1c00c000000180200600301c0060000000c4120c40c1c40c600a00180220600301c006140000, 0xc610000001c60c000002184200000041c3060000000861000000086080000021042000000408204000000, 0xc6120c60c0000000000218423061830000000000000c61208608000000000021842304102000000000000, 0xc6120c60c1c60c600f0000000000000000000000000c4120c40c1c40c600a000000000000000000000000, 0xff9efff9f3ff9f3fff0ffffbdfffe7cfffcf9ffffff040020c000140006000000800206000014000140000])

def checkedSet1 : Claim := (6, [0x1800c03c0000000000008005007800600000000000008000014000000000000800500280060, 0x6180080300000000000008600006000000000000000618108230100000000000860408602042, 0x70000c300000000000000870000783000000000000030000c300000000000000030000503000, 0x71814000000000000000087050a0000000000000000418100000000000000000840408000000, 0x71814c33c180000000000000000000000000000000071014c328180000000000000000000000, 0xffffffffffefffbbff3fffffffffffffefefde7ffff0000000000618108230100000000000860408602042])

def checkedSet2 : Claim := (6, [0x3e01a073000000000000c03800e60980000000000000a000011000000000000c03000220900, 0x18e601204300000000000058d80086018000000000018e701284340000000000058d880868188, 0x1ec001ac00000000000000dec000e6c0000000000000a4001ac000000000000000a4000c4c000, 0x1eff800000000000000000def8c000000000000000014bf800000000000000000d4b8c0000000, 0x1eff81ac736000000000000000000000000000000001ef581ac62600000000000000000000000, 0xffffffffff921ff5fccffffffffffff393fff99ffff0000000001821010840400000000000180880808088])

def checkedSet3 : Claim := (6, [0x20810101021800000000000000000000000000000002081010102180400, 0x80320992101331806000000000000000000000000000012089210113180600, 0x180010320003900019800000000000000000000000008001032000290001900000, 0x181080000003909320000000000000000000000000010108000000100820000000, 0x181090324990000000000000000000000000000000018109020410000000000000, 0xffffffffffffffffffffe7ff7fcdfe6c6ffcdffffff0000000000000000000000000000080000100080400])

def checkedSet4 : Claim := (6, [0x180380f00783800f001c01c00000000000000000000180280b00583800b0018018, 0x1f8000fe0003fc00001f000000000000000000000000a8000fe0002b400001f000, 0x1f8300c00601ec0c000c00c000000000000000000001f83e0ec0761ec0ec00e00e, 0x1f83e0000003fc0fe000000000000000000000000001503e0000001480ec000000, 0x1f83e0fe07f000000000000000000000000000000001f83e0ec076000000000000, 0xffffffffffffffffffffe67f5fc9fe4c63fc9ffffff0000000000000000000006014048024060048006006])

def checkedSet5 : Claim := (7, [0x1ec0c000c00c00000000000000000000000000000001ec8ecc4e08e, 0x3838f181cf9c00000000000000000000000000000003808b1818298, 0xc03f01fe0fe00000000000000000000000000000000c037002a0d60, 0xdef8c0e6c98c0000000000000000000000000000000defeece6e9ce, 0xffc001fff00000000000000000000000000000000002b4001d5f000, 0xfffffe0000000000000000000000000000000000000d4beec000000, 0xfffffffffffffffffffffffffffffff8624c861f87f0000000000000000000000000000000862448606846])

def checkedSet6 : Claim := (6, [0x21e00000000c0e00000001c78000000000f9c00000021600000000c0c00000000458000000000298, 0x3e000000000ff000000001f80000000000fe00000000a00000000015000000001b80000000000d60, 0x3f80000000073600000001c6000000000098c0000003fd8000000073700000001f760000000009ce, 0x3ffc000000000000000001fff0000000000000000003fd8000000000000000001f76000000000000, 0x3ffc0000000fff8000000000000000000000000000035fc0000000eaf80000000000000000000000, 0xffffffd993fffffff30fffffffff264fffffffff87f0000001890000000030300000001224000000000846])

def checkedSet7 : Claim := (6, [0x10f000800000181c61000000000000000000000000010b0008000001818210, 0x1a00080000001dc06200000000000000000000000000000080000000080420, 0x1ac0000000000c4c0000000000000000000000000001aec000000000c4e000, 0x1afe000000001ddf0000000000000000000000000001afe000000001d5f000, 0x1afe0890000000000000000000000000000000000001aec000000000000000, 0xffffffffffffffffffffffffedc9f76fffffe63f9ff0000000000000000000000000848000000000406000])

def checkedSet8 : Claim := (6, [0x21e000808000000000000038f000061000000000000216000808000000000000008b0000210, 0x3e00008c000000000000003f00000620000000000000a000004000000000000003700000420, 0x3f8000000000000000000038c0000000000000000003fd80000000000000000003eec000000, 0x3ffc0000000000000000003ffe000000000000000003fd80000000000000000003eec000000, 0x3ffc008c8800000000000000000000000000000000035fc0088880000000000000000000000, 0xfffffffffffd993ff73ffffffffffffffe4c9fff9ff0000000000018900000000000000000002448000000])

def checkedSet9 : Claim := (7, [0x187310c1c603838f181cf9c00000000000000000000181210804403808b1818298, 0x60701f01c00c03f01fe0fe00000000000000000000060600501800c037002a0d60, 0x7f801fc0000ffc001fff000000000000000000000000a801ac00002b4001d5f000, 0x7ff30000000fffffe0000000000000000000000000075730000000d4beec000000, 0x7ff31fc1c60def8c0e6c98c000000000000000000007ff31fc1c60defeece6e9ce, 0xffffffffffffffffffffc64fecff3ff8624c861f87f0000000000000000000046410c41020862448606846])

def checkedSet10 : Claim := (8, [0x187390f1c783838f181cf9c00000000000000000000181290b04583808b1818298, 0x607c1f01f80c03f01fe0fe000000000000000000000606c0501b80c037002a0d60, 0x7f801ffe000ffc001fff000000000000000000000000a801afe0002b4001d5f000, 0x7ff31fc1c60def8c0e6c98c000000000000000000007fffffedf76defeece6e9ce, 0x7fffe000000fffffe00000000000000000000000000757fe000000d4beec000000, 0x7ffffffffffdef8c0e6c98c000000000000000000007fffffedf76defeece6e9ce, 0xffffffffffffffffffffc64b4cc92648624c861f87f0000000000000000000046494c49224862448606846])

def checkedSet11 : Claim := (6, [0x4a03619b2103371806000000000000000000000000000012089210113180600, 0x2184230618341c3061e00000000000000000000000021a4230698341d3061e0500, 0x3980133600079c0019e00000000000000000000000008801236000294001940000, 0x39b4a00000079db36000000000000000000000000003134a000000509a24000000, 0x39b4b336d9b0000000000000000000000000000000039b4b324d12000000000000, 0xffffffffffffffffffffe67f5fc9fe4c63fc9ffffff00000000000000000000202401009804013000a0500])

def checkedSet12 : Claim := (6, [0x33faf93f9063f93ffffffffffffffffffffffffffff300a090090600900600300000000000000000000000, 0xc01c1e01e3801e01c00e00000000000000000000000c014160163801601800c00000000000000000000000, 0xfc001fc003fc0001f0000000000000000000000000054001fc002b40001f00000000000000000000000000, 0xfc18180181ec1800c00600000000000000000000000fc1f1d81d9ec1d80e00700000000000000000000000, 0xfc1f000003fc1fc0000000000000000000000000000a81f000001481d80000000000000000000000000000, 0xfc1f1fc1fc000000000000000000000000000000000fc1f1d81d8000000000000000000000000000000000])

def checkedSet13 : Claim := (6, [0x20000050000000000004003000a000000000000000020000050000000000004003000a0020, 0x1a008035000000000000c007006a0060000000000000a000015000000000000c007002a0060, 0x600008200000000000000c600006a20000000000000200008200000000000000020000402000, 0x61a100000000000000000c60708000000000000000041a100000000000000000c40608000000, 0x61a1082351000000000000000000000000000000000610108220100000000000000000000000, 0xffffffffff9e5ff7fceffffffffffff39ffff9dffff0000000000000000004000000000000000100080020])

def checkedSet14 : Claim := (7, [0x3838f181cf9c00000000000000000000000000000003808b1818298, 0xc03f01fe0fe00000000000000000000000000000000c037002a0d60, 0xdef8c0e6c98c0000000000000000000000000000000defeece6e9ce, 0xffc001fff00000000000000000000000000000000002b4001d5f000, 0xfffffe0000000000000000000000000000000000000d4beec000000, 0xfffffffffffffffffffffffffffffff8624c861f87f0000000000000000000000000000000862448606846, 0xfffffffffffffffffffffffffffffffffe4c9fff87f0000000000000000000000000000000af6449f5f846])

def checkedSet15 : Claim := (6, [0x3e008030000000000000c03800600800000000000000a000010000000000000c03000200800, 0x10a600000000000000000050980000000000000000010a7000000000000000000509880000000, 0x1680008400000000000000d680006040000000000000200008400000000000000020000404000, 0x16bf800000000000000000d6b8c000000000000000014bf800000000000000000d4b8c0000000, 0x16bf80843020000000000000000000000000000000016b5808420200000000000000000000000, 0xffffffffff961ff7fcfffffffffffff397fff9fffff0000000001021000000000000000000100880000000])

def checkedSet16 : Claim := (6, [0x3e0e03e00000000000060701f01c0000000000000000a0000a00000000000060600501800000000000000, 0xc21f9fe1ffffffffffff987ff0fffffffffffffffffc210902100000000000018121080440000000000000, 0xce60a02600000000000039b01300c00000000000000ce70b02700000000000039b21380c40000000000000, 0xfc00f8000000000000007f801fc00000000000000005400f8000000000000000a801ac0000000000000000, 0xfff800000000000000007ff30000000000000000000abf8000000000000000075730000000000000000000, 0xfff8f83f80000000000000000000000000000000000ff58f83580000000000000000000000000000000000])

def checkedSet17 : Claim := (7, [0x4100410203838f181cf9c00000000000000000000000000000003808b1818298, 0x40480c01200c03f01fe0fe00000000000000000000040480401200c037002a0d60, 0x46000c48000ffc001fff00000000000000000000000020008480002b4001d5f000, 0x46410c41020def8c0e6c98c0000000000000000000046494c49224defeece6e9ce, 0x46494000000fffffe0000000000000000000000000044494000000d4beec000000, 0xfffffffffffffffffffffffffffffff8624c861f87f0000000000000000000046494c49224862448606846])

def checkedSet18 : Claim := (6, [0x3e0e03e00018008030060701f01c0080200060080000a0000a00008000010060600501800802000200800, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffffc210902100000000000018121080440000000000000, 0xce60a02600000000000039b01300c00000000000000ce70b02700000000000039b21380c40000000000000, 0xfc00f8000060000840007f801fc00008600006040005400f8000020000840000a801ac0000020000404000, 0xfff800000061880000007ff30000000862040000000abf8000000418800000075730000000842040000000, 0xfff8f83f80618808430200000000000000000000000ff58f83580610808420200000000000000000000000])

def checkedSet19 : Claim := (5, [0x80800800008004002004100410200020400048040000000000000000000000000000000000000000000, 0x180401800018008030040480c012008024006008400080000800008000010040480401200802400200840, 0x3000490000600008600046000c480008600006060001000490000200008600002000848000020000406000, 0x318a000000618900000046494000000862448000000218a000000418900000044494000000842448000000, 0x318a491890618908630300000000000000000000000310a491090610908620300000000000000000000000, 0xce77b7e77f9e77f7bcfdb9bef3befdf79dfbf9fb7fb0000000000000000000000000000000000000000000])

def checkedSet20 : Claim := (6, [0x18040180001e00e03f040080c00200c007007e0060008000080000a000015040080400200c007002a0060, 0x30004100007c000e300046000c08000c7c0007e3000100041000034000e300002000808000034000543000, 0x31804018006de00a033046000c00000c6c00066000031824118106de18a233146084c08204c6c60c662042, 0x31820000007de1c0000046084000000c7c70e000000218200000049e180000044084000000c4860c000000, 0x31824118107de1ce33f18000000000000000000000031024110107d41ce32a180000000000000000000000, 0xffffffffffe39f39ff0ffffffffffffbe3cf9e1ffff3182411810618108230146084c08204860408602042])

def checkedSet21 : Claim := (5, [0x3e0e03e00018008030060701f01c0080200060080000a0000a00008000010060600501800802000200800, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffffc210902100000000000018121080440000000000000, 0xce60a02600000000000039b01300c00000000000000ce70b02700000000000039b21380c40000000000000, 0xfc00f8000060000840007f801fc00008600006040005400f8000020000840000a801ac0000020000404000, 0xfff800000061880000007ff30000000862040000000abf8000000418800000075730000000842040000000, 0xfff8f83f80618808430200000000000000000000000ff58f83580610808420200000000000000000000000])

def checkedSet22 : Claim := (6, [0x3e0e03e0003e01a073060701f01c00c03800e6098000a0000a0000a000011060600501800c03000220900, 0xc21f9fe1ff921ff5fccf987ff0fffff393fff99ffffc210902101821010840418121080440180880808088, 0xce60a026018e6012043039b01300c0058d800860180ce70b027018e7012843439b21380c4058d880868188, 0xfc00f80001ec001ac0007f801fc0000dec000e6c0005400f80000a4001ac0000a801ac00000a4000c4c000, 0xfff8000001eff80000007ff30000000def8c0000000abf80000014bf800000075730000000d4b8c0000000, 0xfff8f83f81eff81ac73600000000000000000000000ff58f83581ef581ac62600000000000000000000000])

def checkedSet23 : Claim := (5, [0x100c00c1000c400c000042006183010306180000000000400410004400c000000002081010102180000, 0xc0100c00c1c00c000000180200600301c0060000000c4120c40c1c40c600a00180220600301c006140000, 0xc610000001c60c000002184200000041c3060000000861000000086080000021042000000408204000000, 0xc6120c60c0000000000218423061830000000000000c61208608000000000021842304102000000000000, 0xc6120c60c1c60c600f0000000000000000000000000c4120c40c1c40c600a000000000000000000000000, 0xff9efff9f3ff9f3fff0ffffbdfffe7cfffcf9ffffff040020c000140006000000800206000014000140000])

def checkedSet24 : Claim := (5, [0x1c60c600f00000000000041c3061e000000000000001c60c600f00000000000041d3061e0500, 0x21006e408c000000000000210337180600000000000210026408c000000000000210113180600, 0x39c003600000000000000079c0019e00000000000002940036000000000000000294001940000, 0x39e66c000000000000000079db3600000000000000010a6480000000000000000509a24000000, 0x39e66f60cf00000000000000000000000000000000039e46f60ca000000000000000000000000, 0xfffffffffc63f93ffffffffffffffffc63fc9ffffff00000000000020000050000000000004013000a0500])

def checkedSet25 : Claim := (5, [0x180380f00783800f001c01c00000000000000000000180280b00583800b0018018, 0x1f8000fe0003fc00001f000000000000000000000000a8000fe0002b400001f000, 0x1f8300c00601ec0c000c00c000000000000000000001f83e0ec0761ec0ec00e00e, 0x1f83e0000003fc0fe000000000000000000000000001503e0000001480ec000000, 0xffffffffffffffffffffe67f5fc9fe4c63fc9ffffff0000000000000000000006014048024060048006006, 0xfffffffffffffffffffffffffffffffc63fc9ffffff000000000000000000001f83e0ec076060048006006])

def checkedSet26 : Claim := (5, [0x21e00000000c0e00000001c78000000000f9c00000021600000000c0c00000000458000000000298, 0x3e000000000ff000000001f80000000000fe00000000a00000000015000000001b80000000000d60, 0x3f80000000073600000001c6000000000098c0000003fd8000000073700000001f760000000009ce, 0x3ffc0000000fff8000000000000000000000000000035fc0000000eaf80000000000000000000000, 0xffffffd993fffffff30fffffffff264fffffffff87f0000001890000000030300000001224000000000846, 0xfffffffffffffffff30fffffffffffffffffffff87f0000003fd8000000030300000001f76000000000846])

def checkedSet27 : Claim := (5, [0x9c21c00000004002000010e1c7000000000480400009421400000000000000010a0450000000000000, 0xa4a648000000000000001324d120000000000000000b4a7480000000000000013a4d52000000000000, 0xe03e00000008030000001f01f000000006008400000000a00000000010000000501b00000000200840, 0xfd8000000008600000001fec0000000006060000000fd8000000008600000001aec000000000406000, 0xfdbfd80000086303000000000000000000000000000fdb5d8000008620300000000000000000000000, 0xffff07c07ffffff7bcfdffffe03e39fffffff9fb7fb0000000000000000000000000000000000000000000])

def checkedSet28 : Claim := (6, [0x21980000004198000000444300000008420c00000002188000000418800000044410000000842040000000, 0x29e00000004de002003065000000000c4c00006000029e80000004de802003065610000000c4f040060100, 0x57e7fffffe33e7ffffffeafcfffffffe33f3fffffff00a000000000a000001060600000000c03000020100, 0xa800000001cc0012000075000000000dcc0008600000000000000840012000000000000000084000840000, 0xabf8000001cff800000075730000000dcf8c0000000abf80000014bf800000075730000000d4b8c0000000, 0xabf8000001cff812043000000000000000000000000ab58000001cf5812042000000000000000000000000])

def checkedSet29 : Claim := (6, [0x3e0e03e0003e008030060701f01c00c0380060080000a0000a0000a000010060600501800c03000200800, 0xc21f9fe1ff961ff7fcff987ff0fffff397fff9fffffc210902101021000000018121080440100880000000, 0xce60a026010a6000000039b01300c00509800000000ce70b027010a7000000039b21380c40509880000000, 0xfc00f8000168000840007f801fc0000d680006040005400f8000020000840000a801ac0000020000404000, 0xfff80000016bf80000007ff30000000d6b8c0000000abf80000014bf800000075730000000d4b8c0000000, 0xfff8f83f816bf808430200000000000000000000000ff58f835816b5808420200000000000000000000000])

def checkedSet30 : Claim := (5, [0x187390e1c7000204000480400000000000000000000181290a0450000000000000, 0x39b4b324d120000000000000000000000000000000039b6b3a4d52000000000000, 0x607c1f01f0080240060084000000000000000000000606c0501b00802400200840, 0x7f801fec000860000606000000000000000000000000a801aec000020000406000, 0x7fffe00000086244800000000000000000000000000757fe000000842448000000, 0xffffffffffffffffffff800ce03e39f79dfbf9fb7fb0000000000000000000000000000000000000000000])

def checkedSet31 : Claim := (6, [0x1e0601e0001e00e03f0600c0f00380c007007e006000a0000a0000a0000150600c0500380c007002a0060, 0x3c0061c0007c000e300067800f0e000c7c0007e3000140061c00034000e300002800a0e000034000543000, 0x3de0601e006de00a033067800f00000c6c0006600003de3619e186de18a2331678c6f0c306c6c60c662042, 0x3de30000007de1c00000678c6000000c7c70e00000029e300000049e1800000650c6000000c4860c000000, 0x3de361de1c7de1ce33f1800000000000000000000003d4361d41c7d41ce32a180000000000000000000000, 0xffffffffffe39f39ff0ffffffffffffbe3cf9e1ffff3de3619e186181082301678c6f0c306860408602042])

def checkedSet32 : Claim := (6, [0x3e0e03e00018008030060701f01c0080200060080000a0000a00008000010060600501800802000200800, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffffc210902100000000000018121080440000000000000, 0xcfe0e03e00018008030079f01f01c00802000600800cef0b02f00008000010079f21781c40802000200800, 0xfc00f8000060000840007f801fc00008600006040005400f8000020000840000a801ac0000020000404000, 0xfff800000061880000007ff30000000862040000000abf8000000418800000075730000000842040000000, 0xfff8f83f80618808430200000000000000000000000ff58f83580610808420200000000000000000000000])

def checkedSet33 : Claim := (6, [0x20000050000000000004003000a000000000000000020000050000000000804003000a0020, 0x1a0401a0001a0080350600c0d00380c007006a006000a0000a0000a0000150600c0500380c007002a0060, 0x3000410000600008200066000d08000c600006a20001000410000200008200002000808000020000402000, 0x31a200000061a1000000660c4000000c6070800000021a200000041a1000000640c4000000c40608000000, 0x31a2411a1061a1082351000000000000000000000003102411010610108220100000000000000000000000, 0xce5fbfe5ff9e5ff7fcef99fff2fffff39ffff9dffff0000000000000000004000000000080000100080020])

def checkedSet34 : Claim := (5, [0x4a03619b2103371806000000000000000000000000000012089210113180600, 0x2184230618341c3061e00000000000000000000000021a4230698341d3061e0500, 0x3980133600079c0019e00000000000000000000000008801236000294001940000, 0x39b4a00000079db36000000000000000000000000003134a000000509a24000000, 0x39b4b336d9b0000000000000000000000000000000039b4b324d12000000000000, 0xffffffffffffffffffffe67f5fc9fe4c63fc9ffffff00000000000000000000202401009804013000a0500])

def checkedSet35 : Claim := (5, [0x10004400c000000000000010102180000000000000010004400c000000000000010102180400, 0x210066408c000000000000210133180600000000000210026408c000000000000210113180600, 0x39000340000000000000003900019800000000000002900034000000000000000290001900000, 0x39206400000000000000003909320000000000000001020400000000000000000100820000000, 0x39206740cc00000000000000000000000000000000039206740c8000000000000000000000000, 0xfffffffffc6ff9bffffffffffffffffc6ffcdffffff0000000000000000004000000000000000100080400])

def checkedSet36 : Claim := (5, [0x10f000800000181c61000000000000000000000000010b0008000001818210, 0x1a00080000001dc06200000000000000000000000000000080000000080420, 0x1ac0000000000c4c0000000000000000000000000001aec000000000c4e000, 0x1afe000000001ddf0000000000000000000000000001afe000000001d5f000, 0xffffffffffffffffffffffffedc9f76fffffe63f9ff0000000000000000000000000848000000000406000, 0xffffffffffffffffffffffffffffffffffffe63f9ff0000000000000000000000001aec000000000406000])

def checkedSet37 : Claim := (5, [0x3e00000000180000000607c000000080240000000000a00000000080000000606c0000000802400000000, 0x5407ffffffbe77ffffff8a8cfffffff7bdfbfffffff0000000000000000000000000000000000000000000, 0x821c0000000008000000107380000000020400000008214000000000000000010128000000000000000000, 0x8a6500000000000000003134a0000000000000000008a7500000000000000003136a000000000000000000, 0xa8000000004000000000750000000008400000000000000000000000000000000000000000000000000000, 0xabff000000418900000000000000000000000000000ab5f000000410900000000000000000000000000000])

def checkedSet38 : Claim := (5, [0x33faf93f9063f93ffffffffffffffffffffffffffff300a090090600900600300000000000000000000000, 0xc01c1e01e3801e01c00e00000000000000000000000c014160163801601800c00000000000000000000000, 0xfc001fc003fc0001f0000000000000000000000000054001fc002b40001f00000000000000000000000000, 0xfc18180181ec1800c00600000000000000000000000fc1f1d81d9ec1d80e00700000000000000000000000, 0xfc1f000003fc1fc0000000000000000000000000000a81f000001481d80000000000000000000000000000, 0xfffffffffc63f93fffffffffffffffffffffffffffffc1f1d81d8600900600300000000000000000000000])

def checkedSet39 : Claim := (5, [0x1e0601e00018008030060000f0000080000060000000a0000a00008000010060000500000800000200000, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffffc010100100000000000018020080040000000000000, 0xcc60200600000000000039800300000000000000000cc70300700000000000039820380040000000000000, 0xfc0078000060000840007f800fc0000860000604000540078000020000840000a800ac0000020000404000, 0xfdf800000061880000007f830000000860040000000a9f8000000418800000075030000000840040000000, 0xfdf8781f80618808430200000000000000000000000fd58781580610808420200000000000000000000000])

def checkedSet40 : Claim := (5, [0x480301982003310806000000000000000000000000000010088200111080600, 0x200401001804003000a000000000000000000000000202401009804013000a0500, 0x380011300007800018a00000000000000000000000008001030000280001800000, 0x38348000000781b300000000000000000000000000030348000000501a20000000, 0x38349130d980000000000000000000000000000000038349120d10000000000000, 0xffffffffffffffffffffe7ff7fcffe7c7ffcfffffff00000000000000000000202401009804013000a0500])

def checkedSet41 : Claim := (5, [0x3e0603e00018008030060700f01c0080200060080000a0000a00008000010060600501800802000200800, 0xe60202600000000000021b00300c000000000000000e70202700000000000021b20300c40000000000000, 0x3c00600000600008000067800f000008600006000001400600000200008000002800a00000020000400000, 0x3ff8000000618800000067f300000008620400000002bf8000000418800000065730000000842040000000, 0x3ff8603f806188080302000000000000000000000003f58603580610808020200000000000000000000000, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffff0210002100000000000000120000440000000000000])

def checkedSet42 : Claim := (5, [0x803e0182100300130100000000000000000000000000012008210010011010, 0x280000e000034000003000000000000000000000000280004e000034000007000, 0x1a8000fe0003b400001f000000000000000000000000a8000fe0002b400001f000, 0x1a8280000003b40b000000000000000000000000000100280000001000a0000000, 0xffffffffffffffffffffe77f7fc9fe7c6bfcfffffff0000000000000000000002000048000020000006000, 0xfffffffffffffffffffffffffffffffc6bfcfffffff000000000000000000001a8280ec050020000006000])

def checkedSet43 : Claim := (5, [0x1e0e03e00018008030060001f01c0080000060080000a0000a00008000010060000501800800000200800, 0xc60a02600000000000021801300c000000000000000c60b02700000000000021801380c40000000000000, 0x3c00f80000600008400067801fc00008600006040001400f80000200008400002801ac0000020000404000, 0x3de000000061800000006780000000086000000000029e0000000418000000065000000000840000000000, 0x3de0f83f806180084302000000000000000000000003d40f83580610008420200000000000000000000000, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffff0000902100000000000000001080440000000000000])

def checkedSet44 : Claim := (5, [0x1e0601e00018008030060701f01c0080200060080000a0000a00008000010060600501800802000200800, 0xc60200600000000000039b01300c000000000000000c60200600000000000039b21380c40000000000000, 0x3c0060000060000800007f801fc0000860000604000140060000020000800000a801ac0000020000404000, 0x3de000000061800000007ff3000000086204000000029e0000000418000000075730000000842040000000, 0x3de0601e006180080300000000000000000000000003d40601400610008020000000000000000000000000, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffff0000000000000000000018121080440000000000000])

def checkedSet45 : Claim := (6, [0x2184230618341c3061e00000000000000000000000021a4230698341d3061e0500, 0x406006200062008000004a03619b2103371806000000020022000220080000000012089210113180600, 0x3ffbf9ff9c7ff9ffffffe67f5fc9fe4c63fc9ffffff00000000000000000000202401009804013000a0500, 0xc00086000380003000003980133600079c0019e00004000860002800030000008801236000294001940000, 0xc204000003820600000039b4a00000079db36000000820400000102040000003134a000000509a24000000, 0xc204862060000000000039b4b336d9b000000000000c204842040000000000039b4b324d12000000000000])

def checkedSet46 : Claim := (5, [0x3e0003e00018000030000700001c0000200000080000a0000a00008000010000600001800002000000800, 0xc21fffe1ff9e7ffffcfff87fffffffff9ffffffffffc210102100000000000018120080440000000000000, 0xce60002600000000000019b00000c00000000000000ce70102700000000000019b20080c40000000000000, 0xfc0018000060000040001f8000c0000060000004000540018000020000040000a8000c0000020000004000, 0xfff800000061880000001ff30000000062040000000abf8000000418800000015730000000042040000000, 0xfff8183f80618800430200000000000000000000000ff58183580610800420200000000000000000000000])

def checkedSet47 : Claim := (5, [0x4420a00200000000000028a013008000000000000004420b00200000000000028a01380800000000000000, 0x540018000020000040000a8000c00000200000040005400f8000020000840000a801ac0000020000404000, 0x5400f8000020000840006a801fc00008200006040005400f8000020000840000a801ac0000020000404000, 0x54a000000020800000006ae0000000082200000000000a0000000008000000060600000000802000000000, 0x54a0f80a002080084100000000000000000000000005400f80000200008400000000000000000000000000, 0xeb5f9ff5ffdf7ff7feff9d7ff0fffff7dffff9fffff4000900000000000000008001080000000000000000])

def checkedSet48 : Claim := (5, [0xe03e00000008030000001f01c000000006008000000000a00000000010000000501800000000200800, 0xc3ff9fe1ff9ffff7fcfff87ff0ffffff9ffff9fffffc010902100000000000018021080440000000000000, 0xcc00a02600000000000019801300c00000000000000cc10b02700000000000019821380c40000000000000, 0xfc00f8000060000840001f801fc00000600006040005400f8000020000840000a801ac0000020000404000, 0xfc1800000060080000001f830000000060040000000a818000000400800000015030000000040040000000, 0xfc18f83f80600808430200000000000000000000000fc18f83580600808420200000000000000000000000])

def checkedSet49 : Claim := (6, [0x506c06e1006c000000004a03619b2103371806000000024026100240000000000012089210113180600, 0xc0100c00c1c00c000002184230618341c3061e00000c0100c00c1c00c0000021a4230698341d3061e0500, 0x33faf93f9063f93fffffe67f5fc9fe4c63fc9ffffff00000000000000000000202401009804013000a0500, 0xcc0006c0039c000000003980133600079c0019e0000440006c002940000000008801236000294001940000, 0xcc050000039c06c0000039b4a00000079db36000000880500000108048000003134a000000509a24000000, 0xcc0506c06c000000000039b4b336d9b000000000000cc05048048000000000039b4b324d12000000000000])

def checkedSet50 : Claim := (6, [0x60701f01c0080200060080000a0000a00008000010060600501800802000200800, 0x3e0e03e00018008030060701f01c0080200060080000a0000a00008000010060600501800802000200800, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffffc210902100000000000018121080440000000000000, 0xce60a02600000000000039b01300c00000000000000ce70b02700000000000039b21380c40000000000000, 0xfc00f8000060000840007f801fc00008600006040005400f8000020000840000a801ac0000020000404000, 0xfff800000061880000007ff30000000862040000000abf8000000418800000075730000000842040000000])

def checkedSet51 : Claim := (5, [0x7f801fc0000860000604000000000000000000000000a801ac0000020000404000, 0x260002600000000000039b01300c000000000000000270002700000000000039b21380c40000000000000, 0x3e0003e00018000030060701f01c0080200060080000a0000a00008000010060600501800802000200800, 0x3f800000001880000007ff3000000086204000000003f8000000018800000075730000000842040000000, 0x3f8003f800188000302000000000000000000000000358003580010800020200000000000000000000000, 0xfe1fffe1fffe7ffffcff987ff0fffff79ffff9fffff0210002100000000000018121080440000000000000])

def checkedSet52 : Claim := (6, [0x3e0e03e00018008030060701f01c0080200060080000a0000a00008000010060600501800802000200800, 0x3f8003f80018800030200000000000000000000000ab58003580410800020200000000000000000000000, 0xc21f9fe1ff9e7ff7fcff987ff0fffff79ffff9fffffc210902100000000000018121080440000000000000, 0xce60a02600000000000039b01300c00000000000000ce70b02700000000000039b21380c40000000000000, 0xfc00f8000060000840007f801fc00008600006040005400f8000020000840000a801ac0000020000404000, 0xfff800000061880000007ff30000000862040000000abf8000000418800000075730000000842040000000])

def checkedSet53 : Claim := (4, [0x21c0000000000200000001c700000000008040000002140000000000000000000450000000000000, 0x2648000000000000000000d120000000000000000002748000000000000000000d52000000000000, 0x3e00000000030000000001f000000000008400000000a00000000010000000001b00000000000840, 0x3fd800000003030000000000000000000000000000035d8000000020300000000000000000000000, 0xffffffc07ffffffffcfdfffffffe39ffffffffff7fb0000000000000000000000000000000000000000000])

def checkedSet54 : Claim := (4, [0xe00000000008000060701f01c008020006008000000000000000000000060600501800802000200800, 0x4400a00000000000000039b01300c000000000000004400b00000000000000039b21380c40000000000000, 0x540000000020000000007ff300000008620400000000000000000000000000075730000000842040000000, 0x5400f8000020000840007f801fc00008600006040005400f8000020000840000a801ac0000020000404000, 0xebff9fffffdffff7ffff987ff0fffff79ffff9fffff4000900000000000000018121080440000000000000])

def checkedSet55 : Claim := (4, [0x40600620006200800000080300182000310002000000020022000220080000000010008200011000200, 0x3ffbf9ff9c7ff9ffffffe7ff7fcffe7c7ffcfffffff0000000000000000000000000000000000000000000, 0xc0008600038000300000180010300003800018000004000860002800030000008001030000280001800000, 0xc2040000038206000000181080000003808300000008204000001020400000010108000000100820000000, 0xc204862060000000000018109030418000000000000c204842040000000000018109020410000000000000])

def checkedSet56 : Claim := (4, [0x40600620006010008000080300182000300100100000020022000201000800000010008200010010010, 0x3ffbf9ff9c7ff9ffffffe7ff7fcffe7c7ffcfffffff0000000000000000000000000000000000000000000, 0xc0001600038000018000180000b000038000001800040001600028000018000080000b0000280000018000, 0xc0140000038016000000180280000003800b000000080140000010014000000100280000001000a0000000, 0xfffffffffc7ff9fffffffffffffffffc7ffcfffffffc0141401400000000000180280a0050000000000000])

def checkedSet57 : Claim := (4, [0x3e000000001800000006070000000080200000000000a0000000008000000060600000000802000000000, 0x8a600000000000000000313000000000000000000008a70000000000000000031320000000000000000000, 0xa8000000004000000000750000000008400000000000000000000000000000000000000000000000000000, 0xabf8000000418800000075000000000840000000000ab58000000410800000000000000000000000000000, 0xd61fffffffbe7fffffff9afffffffff7bffffffffff8210000000000000000010120000000000000000000])

def checkedSet58 : Claim := (4, [0x21c0000000000200000001c700000000008040000002140000000000000000000450000000000000, 0x2648000000000000000100d120000000000000000002748000000000000000100d52000000000000, 0x3e00000000030000000501f000000002008400000000a00000000010000000501b00000000200840, 0x3fd800000003030000050000000000020000000000035d8000000020300000000000000000000000, 0xffffffc07ffffffffcfdfffffafe39fffffffdff7fb0000000000000000000000000000000000000000000])

def checkedSet59 : Claim := (4, [0x4420a00200000000000028a013008000000000000004420b00200000000000028a01380800000000000000, 0x540018000020000040000a8000c00000200000040005400f8000020000840000a801ac0000020000404000, 0x54a000000020800000006ae0000000082200000000000a0000000008000000060600000000802000000000, 0x54a0f80a0020800841006a801fc00008200006040005400f8000020000840000a801ac0000020000404000, 0xeb5f9ff5ffdf7ff7feff9d7ff0fffff7dffff9fffff4000900000000000000008001080000000000000000])

def checkedSet60 : Claim := (4, [0x9c21c00000004002000010e1c7000000000480400009421400000000000000010a0450000000000000, 0xa4a648000000000000001324d120000000000000000b4a7480000000000000013a4d52000000000000, 0xe03e00000008030000001f01f000000006008400000000a00000000010000000501b00000000200840, 0xfdbfd8000008630300001fec0000000006060000000fdb5d8000008620300001aec000000000406000, 0xffff07c07ffffff7bcfdffffe03e39fffffff9fb7fb0000000000000000000000000000000000000000000])

def checkedSet61 : Claim := (4, [0x100c00c1000c40080000000060000100001000000000004004100044008000000002000010000100000, 0x4100040c0040c000a000000000000000000000000084100040c0840c000a000000000000000000000000, 0xc410000001c40c00000008000000000140000000000841000000084080000000000000000000000000000, 0xc4120c40c0000000000008002060000000000000000c41208408000000000000800204000000000000000, 0xf3feff3ff3e3ff3fffffff7ffff9ffffebfffffffff0000000000000000000000000000000000000000000])

def checkedSet62 : Claim := (4, [0x8080083801e01c00e0000004000028000001c0000000000003801601800c00000000000280000018000, 0xa000090001fc0000f80000000000000000000000200a000091481fc0000f80000000000000000000000, 0x3008080081ec1800c006020000400000a400000c000300a090091ec1d80e007020000480000a400000e000, 0x300a000003fc1fc00000020000000002b4000000000200a000001481d80000000000000000000000000000, 0xfffffffffc63f93ffffffffffffffffd6bfffffffff300a090090600900600302000048000020000006000])

def checkedSet63 : Claim := (4, [0x3e000000003e000000060700000000c0380000000000a000000000a000000060600000000c03000000000, 0x8a600000010a60000000313000000005098000000008a700000010a7000000031320000000509880000000, 0xa800000001480000000075000000000d480000000000000000000000000000000000000000000000000000, 0xabf80000014bf800000075000000000d48000000000ab580000014b5800000000000000000000000000000, 0xd61fffffffb61fffffff9afffffffff3b7fffffffff8210000001021000000010120000000100880000000])

def checkedSet64 : Claim := (4, [0x19a0000000199000000004b40000000024c8000000018a000000018900000000494000000002448000000, 0x21c000000021c000000007380000000038e000000002140000000214000000001280000000008a0000000, 0x3e000000003e0000000007c0000000003e0000000000a000000000a0000000006c0000000003600000000, 0x3ff00000003fd80000000000000000000000000000035f000000035d80000000000000000000000000000, 0xfc07fffffffc07ffffffff8cfffffffffc73fffffff0000000000000000000000000000000000000000000])

def checkedSet65 : Claim := (4, [0x4020040000400600a0000002000000000001400000000000000000000000000000000000000000000000, 0x4100040c0040c000a080000000000000000000000084100040c0840c000a080000000000000000000000, 0xc402004000c40020020008002000000040000400000c412084080c4082002000800204000004000040000, 0xc410000001c40c00000008000000000140000000000841000000084080000000000000000000000000000, 0xffffffffffe3bf39ff5fffffffffffffebfffebffff0c41208408000000000000800204000000000000000])

def checkedSet66 : Claim := (4, [0x80a00a2000a01400a000000500002000000140000000020022000201000800000010000200000010000, 0xa0000b4000b40000b80000000000000000000000200a0000b4400b40000b80000000000000000000000, 0x3008080080600800400202000040000020000004000300a090090600900600302000048000020000006000, 0x300a000002700b40000002000000000230000000000200a000000400900000000000000000000000000000, 0xfffffffffdeffdbffffffffffffffffdeffffffffff300a090090600900600302000048000020000006000])

def checkedSet67 : Claim := (4, [0x14060140001400e02a000000a000000000005400000000000000000000000000000000000000000000000, 0x14300141c0141c002a180000000000000000000000294300141c4941c002a180000000000000000000000, 0x3d406014006d400a022002800a000000240004400003d436194186d418a222102800a0c000024000442000, 0x3d430000007d41c00000028000000000340000000002943000000494180000000000000000000000000000, 0xffffffffffe3bf39ff5fffffffffffffebfffebffff3d43619418610108220102800a0c000020000402000])

def checkedSet68 : Claim := (4, [0x21c0000000000200000001c700000000008040000002140000000000000000000450000000000000, 0x3e00000000030000000001f000000000008400000000a00000000010000000001b00000000000840, 0x3e48000000030000000001f120000000008400000002f48000000010000000001f52000000000840, 0x3fd800000003030000000000000000000000000000035d8000000020300000000000000000000000, 0xffffffc07ffffffffcfdfffffffe39ffffffffff7fb0000000000000000000000000000000000000000000])

def checkedSet69 : Claim := (4, [0x40600620006010008000000300002000000100000000020022000201000800000010000200000010000, 0x14000160001600000c000000000000000000000008014000161001600000c00000000000000000000000, 0x3ffbf9ff9c7ff9fffffff7ffffcffffd7ffffffffff0000000000000000000000000000000000000000000, 0xc0140000038016000000080000000002800000000008014000001001400000000000000000000000000000, 0xfffffffffc7ff9fffffffffffffffffd7ffffffffffc0141401400000000000080000a0000000000000000])

def checkedSet70 : Claim := (5, [0x10f1c7800000181cf9c00000000000000000000000010b0458000001818298, 0x1f01f80000001fe0fe00000000000000000000000000501b800000002a0d60, 0x1fc1c60000000e6c98c0000000000000000000000001fedf76000000e6e9ce, 0x1ffe000000001fff0000000000000000000000000001afe000000001d5f000, 0xffffffffffffffffffffffffecc9264fffffe61f87f0000000000000000000000000c49224000000606846, 0xffffffffffffffffffffffffffffffffffffe61f87f0000000000000000000000001fedf76000000606846])

def checkedSet71 : Claim := (6, [0x480301982003310806000000000000000000000000000010088200111080600, 0x200401001804003000a000000000000000000000000202401009804013000a0500, 0x380011300007800018a00000000000000000000000008001030000280001800000, 0x38348000000781b300000000000000000000000000030348000000501a20000000, 0x38349130d980000000000000000000000000000000038349120d10000000000000, 0xffffffffffffffffffffe7ff7fcffe7c7ffcfffffff00000000000000000000202401009804013000a0500])

def checkedSet72 : Claim := (6, [0x803e0182100300130100000000000000000000000000012008210010011010, 0x280000e000034000003000000000000000000000000280004e000034000007000, 0x1a8000fe0003b400001f000000000000000000000000a8000fe0002b400001f000, 0x1a8280000003b40b000000000000000000000000000100280000001000a0000000, 0x1a8280fe058000000000000000000000000000000001a8280ec050000000000000, 0xffffffffffffffffffffe77f7fc9fe7c6bfcfffffff0000000000000000000002000048000020000006000])

def checkedSet73 : Claim := (7, [0x3838f181cf9c00000000000000000000000000000003808b1818298, 0xc03f01fe0fe00000000000000000000000000000000c037002a0d60, 0xdef8c0e6c98c0000000000000000000000000000000defeece6e9ce, 0xffc001fff00000000000000000000000000000000002b4001d5f000, 0xfffffe0000000000000000000000000000000000000d4beec000000, 0xffffff81cf9c0000000000000000000000000000000fcbefd818298, 0xfffffffffffffffffffffffffffffff8624c861f87f0000000000000000000000000000000862448606846])

def checkedSet74 : Claim := (6, [0x1e00e03f000000000000c007007e0060000000000000a000015000000000000c007002a0060, 0x6de00a033000000000000c6c00066000000000000006de18a233100000000000c6c60c662042, 0x7c000e300000000000000c7c0007e3000000000000034000e300000000000000034000543000, 0x7de1c0000000000000000c7c70e000000000000000049e180000000000000000c4860c000000, 0x7de1ce33f18000000000000000000000000000000007d41ce32a180000000000000000000000, 0xffffffffffe39f39ff0ffffffffffffbe3cf9e1ffff0000000000618108230100000000000860408602042])

def checkedSet75 : Claim := (7, [0x200300c0000000000000c03f01fe0fe00000000000000000000000000000000c037002a0d60, 0x1821010840400000000000def8c0e6c98c0000000001821410840400000000000defeece6e9ce, 0x3800031800000000000000ffc001fff00000000000028000318000000000000002b4001d5f000, 0x3821600000000000000000fffffe0000000000000001021400000000000000000d4beec000000, 0x38216318c0c000000000003838f181cf9c00000000038216318c0c000000000003808b1818298, 0xfffffffffc7df9cff3fffffffffffff8624c861f87f0000000000000000000000000000000862448606846])

def checkedSet76 : Claim := (6, [0x707c07e1007c13009800080300182000300100100000024026100241100880000010008200010010010, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff300a090090600900600300000000000000000000000, 0x3c0301c01c7c01c03001800000000000000000000003c0b09c09c7c09c0700380000000000000000000000, 0xfc001fc003fc0001f000180000b000038000001800054001fc002b40001f000080000b0000280000018000, 0xfc1f000003fc1fc00000180280000003800b0000000a81f000001481d800000100280000001000a0000000, 0xfc1f1fc1fc0000000000180280b0058000000000000fc1f1d81d80000000000180280a0050000000000000])

def checkedSet77 : Claim := (5, [0x40600620006210808000080300182000310102100000020022000221080800000010008200011010210, 0x2008020000200300c00001010004000008018002800000000000000000000000000000000000000000000, 0x3dfb79df9c7df9cff3ffe7ef6fcfbe7c7f7ce7ffd7f0000000000000000000000000000000000000000000, 0xc0009600038000318000180010b000038000181800040009600028000318000080010b0000280001818000, 0xc2140000038216000000181280000003808b000000082140000010214000000101280000001008a0000000, 0xc2149621600000000000181290b0458000000000000c2149421400000000000181290a0450000000000000])

def checkedSet78 : Claim := (5, [0x707c07e1007c13009800080300182000300100100000024026100241100880000010008200010010010, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff300a090090600900600300000000000000000000000, 0x3c0301c01c7c01c03001800000000000000000000003c0b09c09c7c09c0700380000000000000000000000, 0xfc001fc003fc0001f000180000b000038000001800054001fc002b40001f000080000b0000280000018000, 0xfc1f000003fc1fc00000180280000003800b0000000a81f000001481d800000100280000001000a0000000, 0xfc1f1fc1fc0000000000180280b0058000000000000fc1f1d81d80000000000180280a0050000000000000])

def checkedSet79 : Claim := (5, [0x600c0f00380c007007e006000000000000000000000600c0500380c007002a0060, 0x67800f00000c6c00066000000000000000000000000678c6f0c306c6c60c662042, 0x67800f0e000c7c0007e30000000000000000000000002800a0e000034000543000, 0x678c6000000c7c70e00000000000000000000000000650c6000000c4860c000000, 0x678c6f0e38700000000000000000000000000000000678c6f0c306000000000000, 0xffffffffffffffffffffde7bdcf9e7cbe3cf9e1ffff0000000000000000000046084c08204860408602042])

def checkedSet80 : Claim := (5, [0x3e01a073000000000000c03800e60980000000000000a000011000000000000c03000220900, 0x18e601204300000000000058d80086018000000000018e701284340000000000058d880868188, 0x1ec001ac00000000000000dec000e6c0000000000000a4001ac000000000000000a4000c4c000, 0x1eff800000000000000000def8c000000000000000014bf800000000000000000d4b8c0000000, 0xffffffffff921ff5fccffffffffffff393fff99ffff0000000001821010840400000000000180880808088, 0xfffffffffffffffffffffffffffffff393fff99ffff0000000001ef581ac62600000000000180880808088])

def checkedSet81 : Claim := (6, [0x33faf93f9063f93fffffe67f5fc9fe4c63fc9ffffff300a090090600900600306014048024060048006006, 0xc01c1e01e3801e01c00e180380f00783800f001c01cc014160163801601800c180280b00583800b0018018, 0xfc001fc003fc0001f0001f8000fe0003fc00001f00054001fc002b40001f0000a8000fe0002b400001f000, 0xfc18180181ec1800c0061f8300c00601ec0c000c00cfc1f1d81d9ec1d80e0071f83e0ec0761ec0ec00e00e, 0xfc1f000003fc1fc000001f83e0000003fc0fe000000a81f000001481d8000001503e0000001480ec000000, 0xfc1f1fc1fc00000000001f83e0fe07f000000000000fc1f1d81d800000000001f83e0ec076000000000000])

def checkedSet82 : Claim := (5, [0x700007c0007c00889800080000180000300002100000000024000240088880000000008000010000210, 0x14300141c0141c002a180000000000000000000000014b00149c0149c002a380000000000000000000000, 0x3400034000340000ea0001000004000008000002800000000000000000000000000000000000000000000, 0x35f000000035fc00000001280000000008b0000000035f000000035d800000001280000000008a0000000, 0x35f0035fc000000000000128000458000000000000035f0035d8000000000000128000450000000000000, 0xfdbaffdb93fdb93ff35fffef7fffbe7fff7cffffd7f010a001090010900020300000000000000000000000])

def checkedSet83 : Claim := (6, [0x40001e0002800001c000080000f000028000001c00040001600028000018000080000b0000280000018000, 0x5400000002b4000000000f8060000002fc00e000000000000000000000000000500600000004800c000000, 0x5400180000a40000c0000f8000c00000ec00000c00054001d8000a40000e0000f8060ec0060ec00c00e002, 0x54001fc00000000000000f8060fe00700000000000054001d800000000000000f8060ec006000000000000, 0x54001fc002b40001f0000f8000fe0002fc00001f00054001fc002b40001f0000a8000fe0002b400001f000, 0xbbfff93ffd6bfffffffff67fdfc9ffcd63ff9ffffff1000090000200000600006004048004060008006002])

def checkedSet84 : Claim := (6, [0x707c07e1007c130098000803e0182100300130100000024026100241100880000012008210010011010, 0x33faf93f9063f93fffffe77f7fc9fe7c6bfcfffffff300a090090600900600302000048000020000006000, 0x3c0301c01c7c01c030018280000e0000340000030003c0b09c09c7c09c070038280004e000034000007000, 0xfc001fc003fc0001f0001a8000fe0003b400001f00054001fc002b40001f0000a8000fe0002b400001f000, 0xfc1f000003fc1fc000001a8280000003b40b0000000a81f000001481d800000100280000001000a0000000, 0xfc1f1fc1fc00000000001a8280fe058000000000000fc1f1d81d800000000001a8280ec050000000000000])

def checkedSet85 : Claim := (5, [0x21e00000000c0e00000001c78000000000f9c00000021600000000c0c00000000458000000000298, 0x3e000000000ff000000001f80000000000fe00000000a00000000015000000001b80000000000d60, 0x3f80000000073600000001c6000000000098c0000003fd8000000073700000001f760000000009ce, 0x3ffc000000000000000001fff0000000000000000003fd8000000000000000001f76000000000000, 0x3ffc0000000fff80000001c78000000000f9c00000035fc0000000eaf80000000458000000000298, 0xffffffd993fffffff30fffffffff264fffffffff87f0000001890000000030300000001224000000000846])

def checkedSet86 : Claim := (5, [0x3403e0ea0000000000000008018002800000000000000000000000000000000000000000000, 0x7d41ce32a18000000000000000000000000000000007d49ce72a380000000000000000000000, 0x21007e53889800000000002000310102100000000002100265188880000000000200011010210, 0x3fc003ff000000000000003800018180000000000002b4003ff00000000000000280001818000, 0x3ff5fc00000000000000003808b000000000000000014b5d800000000000000001008a0000000, 0xfffffffffc61b909f35ffffffffffffc7f7ce7ffd7f0000000000610908620300000000000000000000000])

def checkedSet87 : Claim := (6, [0x707c07e1007c13009800080300182000300100100000024026100241100880000010008200010010010, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff300a090090600900600300000000000000000000000, 0x3c0707c07e7c07c13009800080300182000300100103c0b0bc0be7c0bc1700b80000010008200010010010, 0xfc001fc003fc0001f000180000b000038000001800054001fc002b40001f000080000b0000280000018000, 0xfc1f000003fc1fc00000180280000003800b0000000a81f000001481d800000100280000001000a0000000, 0xfc1f1fc1fc0000000000180280b0058000000000000fc1f1d81d80000000000180280a0050000000000000])

def checkedSet88 : Claim := (6, [0x20810101021800000000000000000000004000000002081010102180400, 0x406406610066408c000008032099210133180600000002402610026408c000000012089210113180600, 0x3ffbf9bf986ff9bfffffe7ff7fcdfe6c6ffcdffffff0000000000000000004000000000080000100080400, 0xc0008640039000340000180010320003900019800004000864002900034000008001032000290001900000, 0xc2040000039206400000181080000003909320000008204000001020400000010108000000100820000000, 0xc204866064000000000018109032499000000000000c204842040000000000018109020410000000000000])

def checkedSet89 : Claim := (6, [0x2184230618341c3061e00000020000200002000005021a4230698341d3061e0500, 0x506c06e1006e408c00004a03619b210337180600000002402610026408c000000012089210113180600, 0x33faf93f9063f93fffffe67f5fc9fe4c63fc9ffffff00200002000020000050202401009804013000a0500, 0xcc00a6c0039c003600003980133600079c0019e00004400a6c002940036000008801236000294001940000, 0xce650000039e66c0000039b4a00000079db360000008a650000010a648000003134a000000509a24000000, 0xce65a6e66c000000000039b4b336d9b000000000000ce65a4a648000000000039b4b324d12000000000000])

def checkedSet90 : Claim := (5, [0x1e00e03f000000000000c007007e0060000000000000a000015000000000000c007002a0060, 0x6de00a033000000000000c6c00066000000000000006de18a233100000000000c6c60c662042, 0x7c000e300000000000000c7c0007e3000000000000034000e300000000000000034000543000, 0x7de1c0000000000000000c7c70e000000000000000049e180000000000000000c4860c000000, 0x7de1ce33f18000000000000000000000000000000007d41ce32a180000000000000000000000, 0xffffffffffe39f39ff0ffffffffffffbe3cf9e1ffff0000000000618108230100000000000860408602042])

def checkedSet91 : Claim := (5, [0x1800c03c0000000000008005007800600000000000008000014000000000000800500280060, 0x6180080300000000000008600006000000000000000618108230100000000000860408602042, 0x70000c300000000000000870000783000000000000030000c300000000000000030000503000, 0x71814000000000000000087050a0000000000000000418100000000000000000840408000000, 0x71814c33c180000000000000000000000000000000071014c328180000000000000000000000, 0xffffffffffefffbbff3fffffffffffffefefde7ffff0000000000618108230100000000000860408602042])

def checkedSet92 : Claim := (5, [0x506c06e1006c00000000080300182000300000000000024026100240000000000010008200010000000, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff3008080080600800400200000000000000000000000, 0x3c0100c00c7c00c00000000000000000000000000003c0908c08c7c08c0400200000000000000000000000, 0xfc001ec003fc0000c000180000b000038000000800054001ec002b40000c000080000b0000280000008000, 0xfc1d000003fc1ec00000180280000003800b0000000a81d000001481c800000100280000001000a0000000, 0xfc1d1ec1ec0000000000180280b0058000000000000fc1d1c81c80000000000180280a0050000000000000])

def checkedSet93 : Claim := (5, [0x7c0021000253000000000300002000010100000000024002100025100000000010000200001010000, 0xe0000000003e0000000010000000000018000000000000000000000000000000000000000000000000, 0x140061c00034000e300000000000000000000000000140069c00034000e700000000000000000000000000, 0x5400000002b400000000080000000002800000000000000000000000000000000000000000000000000000, 0x5400ffc0000000000000080010b00000000000000005400fd80000000000000080010a0000000000000000, 0xbbff593ffd6bffc9fffff7ffefcffffd7fffe7fffff1000490000200008600000000000000000000000000])

def checkedSet94 : Claim := (5, [0x700007c0007c00009800080000180000300000100000000024000240000880000000008000010000010, 0x33faffff9273f93fffffe7ff7ffffe7e7ffcfffffff300a080090600900400300000000000000000000000, 0x3c0300001c6c01c00001800000000000000000000003c0b08009c6c09c0400380000000000000000000000, 0xfc00180001ec0000c000180000800001800000080005400180000a40000c00008000080000080000008000, 0xfc1f000001ec1fc00000180280000001800b0000000a81f000001481d800000100280000001000a0000000, 0xfc1f1801fc000000000018028080058000000000000fc1f1801d8000000000018028080050000000000000])

def checkedSet95 : Claim := (5, [0x28030040045801c0100080000000000000000000000280b0040045809c0100080000000000000000000000, 0x77fafdbfd8e7f93fffffefff7fefff7cfffcfffffff200a000000400900000000000000000000000000000, 0xa8000240035800011000100000100003000000100000000024002100001100000000010000200000010000, 0xa818000001481800000010020000000100080000000a81f000001481d800000100280000001000a0000000, 0xa81f000003581fc00000100280000003000b0000000a81f000001481d800000100280000001000a0000000, 0xa81f024024000000000010028010008000000000000a81f000000000000000010028000000000000000000])

def checkedSet96 : Claim := (5, [0x7c07c0000013009800000300180000000100100000024024000001100880000010008000000010010, 0x33fff93f9273ffffffffe7ffffcffe7e7ffffffffff3008090090600800600300000000000000000000000, 0x3c0001c01c6c00003001800000000000000000000003c0809c09c6c0800700380000000000000000000000, 0xfc001fc001ec0001f000180000b000018000001800054001fc000a40001f000080000b0000080000018000, 0xfc18000001ec1800000018020000000180080000000a818000001481800000010020000000100080000000, 0xfc181fc1fc0000000000180200b0058000000000000fc181d81d80000000000180200a0050000000000000])

def checkedSet97 : Claim := (6, [0x1e0601e0001e00e03f060000f00000c007007e006000a0000a0000a000015060000500000c007002a0060, 0x3c006000007c000e300067800f00000c7c0007e3000140060000034000e300002800a00000034000543000, 0x3de00000007de1c0000067800000000c7c70e00000029e000000049e180000065000000000c4860c000000, 0x3de0601e006de00a033067800f00000c6c0006600003de0601e006de18a233167800f00000c6c60c662042, 0x3de0601e007de1ce33f1800000000000000000000003d406014007d41ce32a180000000000000000000000, 0xf39fdff9ffe39f39ff0fde7ffcfffffbe3cf9e1ffff3180401800618108230146000c00000860408602042])

def checkedSet98 : Claim := (6, [0x21007c13009800000000002000300100100000024026100241100880000010008200010010010, 0x707c07e1007c13009800080300182000300100100000024026100241100880000010008200010010010, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff300a090090600900600300000000000000000000000, 0x3c0301c01c7c01c03001800000000000000000000003c0b09c09c7c09c0700380000000000000000000000, 0xfc001fc003fc0001f000180000b000038000001800054001fc002b40001f000080000b0000280000018000, 0xfc1f000003fc1fc00000180280000003800b0000000a81f000001481d800000100280000001000a0000000])

def checkedSet99 : Claim := (5, [0x200401001804003000a000000000000000000000000200401001804003000a0020, 0x600c0d00380c007006a006000000000000000000000600c0500380c007002a0060, 0x66000d08000c600006a20000000000000000000000002000808000020000402000, 0x660c4000000c6070800000000000000000000000000640c4000000c40608000000, 0x660c4d0838400000000000000000000000000000000660c4d08304000000000000, 0xffffffffffffffffffff99fff2fffff39ffff9dffff0000000000000000000000000000080000100080020])

def checkedSet100 : Claim := (5, [0x706c07e1007c00009800080300182000300000100000024026100240000880000010008200010000010, 0xc0300c01c1c01c00001800000000000000000000000c0b00c09c1c09c0000380000000000000000000000, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff000a000090000900000300000000000000000000000, 0xcc0006c0039c0000000018000030000380000000000440006c002940000000008000030000280000000000, 0xcc1f0000039c1fc00000180280000003800b0000000881f000001081d800000100280000001000a0000000, 0xcc1f06c1fc000000000018028030058000000000000cc1f0481d8000000000018028020050000000000000])

def checkedSet101 : Claim := (5, [0x507c07e1006c13009800080300182000300100100000024026100241100880000010008200010010010, 0xc0101c01c1c00c03001800000000000000000000000c0109c09c1c00c0700380000000000000000000000, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff0000090090000000600300000000000000000000000, 0xcc001fc0039c0001f000180000b000038000001800044001fc002940001f000080000b0000280000018000, 0xcc050000039c06c00000180080000003800300000008805000001080480000010008000000100020000000, 0xcc051fc1fc0000000000180080b0058000000000000cc051d81d80000000000180080a0050000000000000])

def checkedSet102 : Claim := (5, [0x3e008030000000000000c03800600800000000000000a000010000000000000c03000200800, 0x10a600000000000000000050980000000000000000010a7000000000000000000509880000000, 0x1680008400000000000000d680006040000000000000200008400000000000000020000404000, 0x16bf800000000000000000d6b8c000000000000000014bf800000000000000000d4b8c0000000, 0xffffffffff961ff7fcfffffffffffff397fff9fffff0000000001021000000000000000000100880000000, 0xfffffffffffffffffffffffffffffff397fff9fffff00000000016b5808420200000000000100880000000])

def checkedSet103 : Claim := (5, [0x506c06e1007c13009800080300182000300100100000024026100241100880000010008200010010010, 0xc0100c00c7c01c03001800000000000000000000000c0100c00c7c09c0700380000000000000000000000, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff0000000000600900600300000000000000000000000, 0xcc0006c003fc0001f00018000030000380000018000440006c002b40001f00008000030000280000018000, 0xcc05000003fc1fc00000180080000003800b00000008805000001481d800000100080000001000a0000000, 0xcc0506c06c000000000018008030018000000000000cc05048048000000000018008020010000000000000])

def checkedSet104 : Claim := (5, [0x3e0e03e00000000000060701f01c0000000000000000a0000a00000000000060600501800000000000000, 0xc21f9fe1ffffffffffff987ff0fffffffffffffffffc210902100000000000018121080440000000000000, 0xce60a02600000000000039b01300c00000000000000ce70b02700000000000039b21380c40000000000000, 0xfc00f8000000000000007f801fc00000000000000005400f8000000000000000a801ac0000000000000000, 0xfff800000000000000007ff30000000000000000000abf8000000000000000075730000000000000000000, 0xffffffffffffffffffff987ff0fffffffffffffffffff58f83580000000000018121080440000000000000])

def checkedSet105 : Claim := (5, [0x1d800000000000000000000ec0000000000000000035d800000000000000000008ec000000, 0x21c000000000000000000038e0000d0000000000000214000000000000000000008a0000000, 0x3f8000110000000000000038c0000900000000000003fd80011000000000000003eec000940, 0x3fd80000000000000000003fec000000000000000003fd80000000000000000003eec000000, 0x3fd800150000000000000038e0000d000000000000035d800000000000000000008a0000000, 0xfffffffffffd9b7fffaffffffffffffffe4dbfffaff0000000000018900010000000000000002448000840])

def checkedSet106 : Claim := (5, [0x21e000c0e000000000000038f0000f9c00000000000216000c0c000000000000008b0000298, 0x3e0000ff000000000000003f00000fe0000000000000a000015000000000000003700000d60, 0x3f8000736000000000000038c000098c000000000003fd80073700000000000003eec0009ce, 0x3ffc0000000000000000003ffe000000000000000003fd80000000000000000003eec000000, 0x3ffc00fff800000000000038f0000f9c0000000000035fc00eaf800000000000008b0000298, 0xfffffffffffd993ff30ffffffffffffffe4c9fff87f0000000000018900030300000000000002448000846])

def checkedSet107 : Claim := (5, [0x3fc1fc00000000000000003800b00000000000000001481d800000000000000001000a0000000, 0x1c01c7c01c0300180000000000000000000000000009c09c7c09c0700380000000000000000000000, 0x7c07e1007c13009800000300182000300100100000024026100241100880000010008200010010010, 0x1fc003fc0001f000000000b000038000001800000001fc002b40001f000000000b0000280000018000, 0x1fc1fc0000000000000000b005800000000000000001d81d80000000000000000a0050000000000000, 0xfffff93f9063f93fffffffffffcffe7c7ffcfffffff0000090090600900600300000000000000000000000])

def checkedSet108 : Claim := (6, [0x1fc1fc0000000000000000b005800000000000054001d81d80000000000080000a0050000000000000, 0x707c07e1007c13009800080300182000300100100000024026100241100880000010008200010010010, 0x33faf93f9063f93fffffe7ff7fcffe7c7ffcfffffff300a090090600900600300000000000000000000000, 0x3c0301c01c7c01c03001800000000000000000000003c0b09c09c7c09c0700380000000000000000000000, 0xfc001fc003fc0001f000180000b000038000001800054001fc002b40001f000080000b0000280000018000, 0xfc1f000003fc1fc00000180280000003800b0000000a81f000001481d800000100280000001000a0000000])

def checkedSet109 : Claim := (4, [0x2086080000000000000003041020000000000000400208608000000000000800304102000000000000, 0x602006000060000000200403001004002000000000020000200002000000020040100100400200000000, 0xc002080000800000000218003040004080000000000400208000000000000000800204000000000000000, 0xc612086080860800000000000000000000000000000c41208408084080000000000000000000000000000, 0xf39fdff9fff79fffffffde7ffcfffffbf7fffffffff0000000000000000000000000000000000000000000])

def checkedSet110 : Claim := (4, [0x70000021007c13009800080000002000300100100000000002100241100880000000000200010010010, 0x28030000007c01c0300180000000000000000000000280b0000007c09c0700380000000000000000000000, 0x77fafffffc63f93fffffefff7ffffffc7ffcfffffff200a000000600900600300000000000000000000000, 0xa800000003fc0001f000100000000003800000180000000000002b40001f00000000000000280000018000, 0xa81f000003fc1fc00000100280000003800b0000000a81f000001481d800000100280000001000a0000000])

def checkedSet111 : Claim := (4, [0x180401800018008030040400c010008020006008000080000800008000010040400401000802000200800, 0x3000480000600008400046000c400008600006040001000480000200008400002000840000020000404000, 0x31880000006188000000464100000008620400000002188000000418800000044410000000842040000000, 0xce7fbfe7ff9e7ff7fcffb9fff3fffff79ffff9fffff0000000000000000000000000000000000000000000, 0xffffffffffffffffffffb9fff3fffff79ffff9fffff3108481080610808420200000000000000000000000])

def checkedSet112 : Claim := (4, [0x180401800018008030040080c002008004006000400080000800008000010040080400200800400200040, 0x3000410000600008200046000c080008600006020001000410000200008200002000808000020000402000, 0x31820000006181000000460840000008604080000002182000000418100000044084000000840408000000, 0x31824118106181082301000000000000000000000003102411010610108220100000000000000000000000, 0xce7fbfe7ff9e7ff7fcffb9fff3fffff79ffff9fffff0000000000000000000000000000000000000000000])

def checkedSet113 : Claim := (4, [0x7c0002400889800000000180000100002100000000024000240088880000000008000010000210, 0x141c00004002a180000000000000000000000000000149c00004002a380000000000000000000000, 0x34000000000ea0000000004000000000002800000000000000000000000000000000000000000000, 0x35fc00024000000000000045800001000000000000035d8000000000000000000450000000000000, 0xffffffdb93fffdbff35fffffffffbe7ffffeffffd7f0000001090000000020300000000000000000000000])

def checkedSet114 : Claim := (4, [0x28030040045801c0100080000000000000000000000280b0040045809c0100080000000000000000000000, 0x77fafdbfd8e7f93fffffefff7fefff7cfffcfffffff200a000000400900000000000000000000000000000, 0xa8000240035800011000100000100003000000100000000024002100001100000000010000200000010000, 0xa818000001481800000010020000000100080000000a81f000001481d800000100280000001000a0000000, 0xa81f024027581fc00000100280100083000b0000000a81f000001481d800000100280000001000a0000000])

def checkedSet115 : Claim := (4, [0x602006000060000000200403001004002000000000020000200002000000020040100100400200000000, 0x602086080060000000200403041024002000000000420208608002000000020840304102400200000000, 0xc002080000800000000218003040004080000000000400208000000000000000800204000000000000000, 0xc612086080860800000000000000000000000000000c41208408084080000000000000000000000000000, 0xf39fdff9fff79fffffffde7ffcfffffbf7fffffffff0000000000000000000000000000000000000000000])

def checkedSet116 : Claim := (4, [0x7c0021000013000000000300002000000100000000024002100001100000000010000200000010000, 0x140001c000340000300000000000000000000000000140009c000340000700000000000000000000000000, 0x5400000002b400000000080000000002800000000000000000000000000000000000000000000000000000, 0x54001fc002b400000000080000b000028000000000054001d80000000000000080000a0000000000000000, 0xbbfff93ffd6bfffffffff7ffffcffffd7ffffffffff1000090000200000600000000000000000000000000])

def checkedSet117 : Claim := (4, [0x700007c0007c00889800080000180000300002100000000024000240088880000000008000010000210, 0x14300141c0141c002a180000000000000000000000014b00149c0149c002a380000000000000000000000, 0x3400034000340000ea0001000004000008000002800000000000000000000000000000000000000000000, 0x35f0035fc035fc00000001280004580008b0000000035f0035d8035d800000001280004500008a0000000, 0xfdbaffdb93fdb93ff35fffef7fffbe7fff7cffffd7f010a001090010900020300000000000000000000000])

def checkedSet118 : Claim := (4, [0x902100000000000000001fc1c60000000000000400090210000000000000a801fc1c60000000000000, 0x200802000020000000060701f01c00c038000000000000000000000000000060600501800c03000000000, 0xc00090000100000000007f801fc0000d48000000000400090000000000000000a801ac0000000000000000, 0xc200802001020000000039b01300c00509800000000c210902101021000000039b21380c40509880000000, 0xffffffffffffffffffff987ff0fffff3b7fffffffffc210902101021000000018121080440100880000000])

def checkedSet119 : Claim := (4, [0x40001e0002800001c000080000f000028000001c00040001600028000018000080000b0000280000018000, 0x5400000002b4000000000a8000000002b40000000000000000000000000000000000000000000000000000, 0x5400180000a40000c0000a8000c00000a400000c00054001d8000a40000e0000a8000ec0000a400000e000, 0x54001fc002b4000000000a8000fe0002b400000000054001d800000000000000a8000ec000000000000000, 0xbbfff93ffd6bfffffffff77fffc9fffd6bfffffffff1000090000200000600002000048000020000006000])

def checkedSet120 : Claim := (4, [0x481880000000000000000c410200000000000001000481880000000000002000c41020000000000000, 0x180401800018000000040400c010008020000000000080000800008000000040400401000802000000000, 0x3000480000400000000046000c400008400000000001000480000000000000002000840000000000000000, 0xce7fbfe7ffbe7fffffffb9fff3fffff7bffffffffff0000000000000000000000000000000000000000000, 0xffffffffffffffffffffb9fff3fffff7bffffffffff3108481080410800000000000000000000000000000])

def checkedSet121 : Claim := (4, [0xa4a648000000000000001324d120000000000004400a4a648000000000008801324d12000000000000, 0x260a02600026000000020341300d00401a000000000020000200002000000020240100900401200000000, 0x319f5fd9fef59fffffffc64fecff3ffaf67ffffffff0000000000000000000000000000000000000000000, 0xcc00a480010800000000398013240005080000000004400a48000000000000008801224000000000000000, 0xce65a4a6490a6480000018309020c10101820000000ce45a4a4490a4480000018109020410100820000000])

def checkedSet122 : Claim := (4, [0x2086080000000000000003049020000000000000400208608000000000000800304902000000000000, 0x602006000060000000202403009004012000000000020000200002000000020240100900401200000000, 0xc002080000800000000218003040004080000000000400208000000000000000800204000000000000000, 0xc612086080860800000002000008000010000000000c41208408084080000000000000000000000000000, 0xf39fdff9fff79fffffffde5ffcff7ffbf6fffffffff0000000000000000000000000000000000000000000])

def checkedSet123 : Claim := (4, [0x60000500000c0000000000000a0000a0000a000000060600501800c03000000000, 0x902b00000000000000001581c400000000000004000902b00000000000008001581c40000000000000, 0x2a0802a0002a000000060701501c00c0380000000000a0000a0000a000000060600501800c03000000000, 0x3ddf7fddfefddfffffffc7cfeeff3ffafe7ffffffff0080000800008000000040400401000802000000000, 0xc000900001000000000078001580000d000000000004000900000000000000008001080000000000000000])

def checkedSet124 : Claim := (6, [0xfe00000000001f0000000000000000000000000001afe000000001d5f000, 0x10f180000000181cd0000000000000000000000000010b0000000001818000, 0x1fc1800000000e6c9000000000000000000000000001fedb00000000e6e940, 0x1ffe000000001fff0000000000000000000000000001afe000000001d5f000, 0x1fffb800000000000000000000000000000000000001fedb00000000000000, 0xffffffffffffffffffffffffecc967ffffffe61faff0000000000000000000000000c49200000000606840])

def checkedSet125 : Claim := (6, [0x1d800000000000000000000ec0000000000000000035d800000000000000000008ec000000, 0x21c000000000000000000038e0000d0000000000000214000000000000000000008a0000000, 0x3f8000110000000000000038c0000900000000000003fd80011000000000000003eec000940, 0x3fd80000000000000000003fec000000000000000003fd80000000000000000003eec000000, 0x3fd800150000000000000000000000000000000000035d80000000000000000000000000000, 0xfffffffffffd9b7fffaffffffffffffffe4dbfffaff0000000000018900010000000000000002448000840])

def checkedSet126 : Claim := (7, [0xc03f01fe0fe00000000000000000000000000000000c037002a0d60, 0x1ec1800c00600000000000def8c0e6c98c0000000001ec1d80e00700000000000defeece6e9ce, 0x3801e01c00e000000000003838f181cf9c0000000003801601800c000000000003808b1818298, 0x3fc0001f00000000000000ffc001fff0000000000002b40001f000000000000002b4001d5f000, 0x3fc1fc0000000000000000fffffe0000000000000001481d80000000000000000d4beec000000, 0xfffffffffc63f93ffffffffffffffff8624c861f87f0000000000600900600300000000000862448606846])

def checkedSet127 : Claim := (8, [0xc03f01fe0fe0000000000000a000015000000000000c037002a0d60, 0x3e03e0ff000000000000c03f01fe0fe0000000000000a000015000000000000c037002a0d60, 0x1eff81ac73600000000000def8c0e6c98c0000000001effd9ae73700000000000defeece6e9ce, 0x3821e31cc0e000000000003838f181cf9c00000000038216318c0c000000000003808b1818298, 0x3fc003ff00000000000000ffc001fff0000000000002b4003ff000000000000002b4001d5f000, 0x3ffffc0000000000000000fffffe00000000000000014bfd80000000000000000d4beec000000, 0xfffffffffc619909f30ffffffffffff8624c861f87f0000000000618908630300000000000862448606846])

def checkedSet128 : Claim := (6, [0x21e000c0e000000000000038f0000f9c00000000000216000c0c000000000000008b0000298, 0x3e0000ff000000000000003f00000fe0000000000000a000015000000000000003700000d60, 0x3f8000736000000000000038c000098c000000000003fd80073700000000000003eec0009ce, 0x3ffc0000000000000000003ffe000000000000000003fd80000000000000000003eec000000, 0x3ffc00fff800000000000000000000000000000000035fc00eaf80000000000000000000000, 0xfffffffffffd993ff30ffffffffffffffe4c9fff87f0000000000018900030300000000000002448000846])

def checkedSet129 : Claim := (7, [0x3e000000000000000c03f01fe0fe00000000000000000000000000000000c037002a0d60, 0xa4001ac00000000000000def8c0e6c98c0000000000a4001ae00000000000000defeece6e9ce, 0x2800031c000000000000003838f181cf9c00000000028000318000000000000003808b1818298, 0x2b40000000000000000000fffffe0000000000000000000000000000000000000d4beec000000, 0x2b4003ff00000000000000ffc001fff0000000000002b4003ff000000000000002b4001d5f000, 0xfffffffffd6bffc9fffffffffffffff8624c861f87f0000000000200008600000000000000862448606846])

def checkedSet130 : Claim := (6, [0x1f0001fc001fc0000f80000000000000000000000a81f0001fd481fc0000f80000000000000000000000, 0x33faf93f9063f93ffffff77fffc9fffd6bfffffffff300a090090600900600302000048000020000006000, 0xc01c1e01e3801e01c00e080000f000028000001c000c014160163801601800c080000b0000280000018000, 0xfc18180181ec1800c0060a8000c00000a400000c000fc1f1d81d9ec1d80e0070a8000ec0000a400000e000, 0xfc1f000003fc1fc000000a8000000002b4000000000a81f000001481d80000000000000000000000000000, 0xfc1f1fc1fc00000000000a8000fe000000000000000fc1f1d81d800000000000a8000ec000000000000000])

def checkedSet131 : Claim := (5, [0xe0000000003e000000001a00000000001d400000000000000000000000000000000000000000000000, 0x40009e0002800031c000080010f000028000181c00040009600028000318000080010b0000280001818000, 0x5400000002b4000000000a8000000002b40000000000000000000000000000000000000000000000000000, 0x5400f80000a4001ac0000a801ac00000a4000c4c0005400fd8000a4001ae0000a801aec0000a4000c4e000, 0x5400ffc00000000000000a801afe0000000000000005400fd800000000000000a801aec000000000000000, 0xbbff593ffd6bffc9fffff77fedc9fffd6bffe6bffff1000490000200008600002000848000020000406000])

def checkedSet132 : Claim := (6, [0x9e0000000031c000000010f1c7800000181cf9c00009600000000318000000010b0458000001818298, 0xe0000000003e000000001f01f80000001fe0fe00000000000000000000000000501b800000002a0d60, 0xf8000000001ac00000001fc1c60000000e6c98c0000fd800000001ae00000001fedf76000000e6e9ce, 0xffc000000000000000001ffffff0000000000000000fd8000000000000000001fedf76000000000000, 0xffc00000003ff00000001ffe000000001fff0000000ffc00000003ff00000001afe000000001d5f000, 0xffff593fffffffc9ffffffffecc9264fffffe61f87f0000490000000008600000000c49224000000606846])

def checkedSet133 : Claim := (5, [0x1f0001fc001fc0000f80000000000000000000000a81f0001fd481fc0000f80000000000000000000000, 0x33faf93f9063f93ffffff77fffc9fffd6bfffffffff300a090090600900600302000048000020000006000, 0xc01c1e01e3801e01c00e080000f000028000001c000c014160163801601800c080000b0000280000018000, 0xfc18180181ec1800c0060a8000c00000a400000c000fc1f1d81d9ec1d80e0070a8000ec0000a400000e000, 0xfc1f000003fc1fc000000a8000000002b4000000000a81f000001481d80000000000000000000000000000, 0xfc1f1fc1fc00000000000a8000fe000000000000000fc1f1d81d800000000000a8000ec000000000000000])

def checkedSet134 : Claim := (5, [0x730001c600038c000098c00000000000000000000007fe001f76003eec0009ce, 0x738001c780038f0000f9c00000000000000000000001280004580008b0000298, 0x7c0001f80003f00000fe000000000000000000000006c0001b80003700000d60, 0x7fe000000003ffe00000000000000000000000000007fe000000003eec000000, 0x7fe001fff00000000000000000000000000000000007fe001f76000000000000, 0xffffffffffffffffffffffcb5fff264ffe4c9fff87f0000000000000000000000494001224002448000846])

def checkedSet135 : Claim := (5, [0x3e01a073000000000000c03800e60980000000000000a000011000000000000c03000220900, 0x18e601204300000000000058d80086018000000000018e701284340000000000058d880868188, 0x1ec001ac00000000000000dec000e6c0000000000000a4001ac000000000000000a4000c4c000, 0x1eff800000000000000000def8c000000000000000014bf800000000000000000d4b8c0000000, 0x1eff81ac73600000000000dec000e6c0000000000001ef581ac626000000000000a4000c4c000, 0xffffffffff921ff5fccffffffffffff393fff99ffff0000000001821010840400000000000180880808088])

def checkedSet136 : Claim := (5, [0x100c00c1000c400c000042006183010306180000000000400410004400c000000002081010102180000, 0xc0100c00c1c00c000000180200600301c0060000000c4120c40c1c40c600a00180220600301c006140000, 0xc610000001c60c000002184200000041c3060000000861000000086080000021042000000408204000000, 0xc6120c60c0000000000218423061830000000000000c61208608000000000021842304102000000000000, 0xff9efff9f3ff9f3fff0ffffbdfffe7cfffcf9ffffff040020c000140006000000800206000014000140000, 0xfffffffffffffffffffffffbdfffe7cfffcf9ffffff0c4120c40c1c40c600a000800206000014000140000])

def checkedSet137 : Claim := (5, [0x14060140001400e02a000000a000000000005400000000000000000000000000000000000000000000000, 0x14300141c0141c002a180000000000000000000000294300141c4941c002a180000000000000000000000, 0x3d406014006d400a022002800a000000240004400003d436194186d418a222102800a0c000024000442000, 0x3d430000007d41c00000028000000000340000000002943000000494180000000000000000000000000000, 0x3d4361d41c000000000002800a0e0000000000000003d43619418000000000002800a0c000000000000000, 0xf3bedf3bf3e3bf39ff5fff7ffdf9ffffebfffebffff3102411010610108220102000808000020000402000])

def checkedSet138 : Claim := (6, [0x3ffbf9ff9c7ff9ffffffe7ff5fcffe4c7ffc9ffffff0000000000000000000000014000024000048000006, 0xc0001600038000018000180000b000038000001800040001600028000018000080000b0000280000018000, 0xc0101001018010008004180300800601800c000800cc01414014180140080041803e0a00761800ec00800e, 0xc01400000380160000001803e0000003800fe000000801400000100140000001003e0000001000ec000000, 0xc01416016000000000001803e0b007f000000000000c01414014000000000001803e0a0076000000000000, 0xc014160163801601800c180380b00783800f001801cc014160163801601800c180280b00583800b0018018])

def checkedSet139 : Claim := (5, [0x21e00000000c0e00000001c78000000000f9c00000021600000000c0c00000000458000000000298, 0x3e000000000ff000000001f80000000000fe00000000a00000000015000000001b80000000000d60, 0x3f80000000073600000001c6000000000098c0000003fd8000000073700000001f760000000009ce, 0x3ffc000000000000000001fff0000000000000000003fd8000000000000000001f76000000000000, 0x3ffc0000000fff8000000000000000000000000000035fc0000000eaf80000000000000000000000, 0xffffffd993fffffff30fffffffff264fffffffff87f0000001890000000030300000001224000000000846])

def checkedSet140 : Claim := (5, [0x3403e0ea000000000000000001d400000000000000000000000000000000000000000000000, 0x35fc00eaf8000000000000000000000000000000014b5fc00eaf80000000000000000000000, 0x1ef581ac626000000000000a4000c4c0000000000001ef5d9ae627000000000000a4000c4e000, 0x3821e31cc0e0000000000028000181c00000000000038216318c0c00000000000280001818000, 0x3ff5fc00000000000000002b400000000000000000014b5d80000000000000000000000000000, 0xfffffffffc61b909f35ffffffffffffd6bffe6bffff0000000000610908620300000000000020000406000])

def checkedSet141 : Claim := (6, [0x33faf93f9063f93ffffff77fffc9fffd6bfffffffff300a090090600900600302000048000020000006000, 0xc01c1e01e3801e01c00e080000f000028000001c000c014160163801601800c080000b0000280000018000, 0xfc00180001ec0000c0000a8000c00000a400000c00054001d8000a40000e0000a8000ec0000a400000e000, 0xfc18180181ec1800c0060a8000c00000a400000c000fc1f1d81d9ec1d80e0070a8000ec0000a400000e000, 0xfc1f000003fc1fc000000a8000000002b4000000000a81f000001481d80000000000000000000000000000, 0xfc1f1fc1fc00000000000a8000fe000000000000000fc1f1d81d800000000000a8000ec000000000000000])

def checkedSet142 : Claim := (6, [0x9e0020000031c808000010f000800000181c61000009600200000318808000010b0008000001818210, 0xe0000000003e08c000001a00080000001dc06200000000000000000004000000000080000000080420, 0xf8000000001ac00000001ac0000000000c4c0000000fd800000001ae00000001aec000000000c4e000, 0xffc024000000000000001afe0890000000000000000fd8000000000000000001aec000000000000000, 0xffc02400003ff8c880001afe000000001ddf0000000ffc02400003ff88880001afe000000001d5f000, 0xffff593fdbffffc9f73fffffedc9f76fffffe63f9ff0000490000000008600000000848000000000406000])

def checkedSet143 : Claim := (6, [0x9e21e0000031cc0e000010f1c7800000181cf9c00009621600000318c0c000010b0458000001818298, 0xe03e0000003e0ff000001f01f80000001fe0fe00000000a00000000015000000501b800000002a0d60, 0xf83f8000001ac73600001fc1c60000000e6c98c0000fdbfd800001ae73700001fedf76000000e6e9ce, 0xfffffc000000000000001ffffff0000000000000000fdbfd8000000000000001fedf76000000000000, 0xfffffc00003fffff80001ffe000000001fff0000000fff5fc00003ffeaf80001afe000000001d5f000, 0xffff591993ffffc9f30fffffecc9264fffffe61f87f0000491890000008630300000c49224000000606846])

def checkedSet144 : Claim := (5, [0x21e000c0e000000000000038f0000f9c00000000000216000c0c000000000000008b0000298, 0x3e0000ff000000000000003f00000fe0000000000000a000015000000000000003700000d60, 0x3f8000736000000000000038c000098c000000000003fd80073700000000000003eec0009ce, 0x3ffc0000000000000000003ffe000000000000000003fd80000000000000000003eec000000, 0x3ffc00fff800000000000000000000000000000000035fc00eaf80000000000000000000000, 0xfffffffffffd993ff30ffffffffffffffe4c9fff87f0000000000018900030300000000000002448000846])

def checkedSet145 : Claim := (5, [0x80a00a2000a01400a000000500002000000140000000020022000201000800000010000200000010000, 0xa0000b4000b40000b80000000000000000000000200a0000b4400b40000b80000000000000000000000, 0x3008080080600800400202000040000020000004000300a090090600900600302000048000020000006000, 0x300a000002700b40000002000000000230000000000200a000000400900000000000000000000000000000, 0x300a0b40b400000000000200005a000000000000000300a090090000000000002000048000000000000000, 0xfffffdbfd9effdbfffffffffffedfffdeffffffffff300a090090600900600302000048000020000006000])

def checkedSet146 : Claim := (5, [0x506c06e1006c00000000000360002100000000000000024026100240000000000012000210000000000, 0x1d0001ec001ec0000600000000000000000000000a81d0001ed481ec0000600000000000000000000000, 0xc3feff3ff383ff3ffffffd7ffff9ffffcbfffffffffc0141601638016008004080000b0000280000008000, 0xcc0506c06f9c06c0000008800036000294000000000cc1516c16f9c16c08004088000b6000294000008000, 0xfc1d000003fc1ec000000a8000000002b4000000000a81d000001481c80000000000000000000000000000, 0xfc1d1ec1ec00000000000a8000f6000000000000000fc1d1c81c800000000000a8000e4000000000000000])

def checkedSet147 : Claim := (5, [0x40600620006210808000000300002000010100000000020022000221080800000010000200001010000, 0x2008020000200300c00000010000000000018000000000000000000000000000000000000000000000000, 0x2140021600216000c0c0000000000000000000000082140021610216000c0c00000000000000000000000, 0x3dfb79df9c7df9cff3fff7ffefcffffd7fffe7fffff0000000000000000000000000000000000000000000, 0xc2140000038216000000080000000002800000000008214000001021400000000000000000000000000000, 0xc2149621600000000000080010b0000000000000000c2149421400000000000080010a0000000000000000])

def checkedSet148 : Claim := (5, [0x1b00019c0019c0000780000000000000000000000a81b00019d4819c0000780000000000000000000000, 0x33feff3ff263ff3ffffff77ffff9ffff6bfffffffff300a090090600900600302000048000020000006000, 0xc018180181801800c006080000c000008000000c000c010100101801000800408000080000080000008000, 0xfc18180181ec1800c0060a8000c00000a400000c000fc1b198199ec1980e0070a8000cc0000a400000e000, 0xfc1b000001fc19c000000a8000000000b4000000000a81b000001481980000000000000000000000000000, 0xfc1b19c19c00000000000a8000ce000000000000000fc1b19819800000000000a8000cc000000000000000])

def checkedSet149 : Claim := (5, [0x21e000808000000000000038f000061000000000000216000808000000000000008b0000210, 0x3e00008c000000000000003f00000620000000000000a000004000000000000003700000420, 0x3f8000000000000000000038c0000000000000000003fd80000000000000000003eec000000, 0x3ffc0000000000000000003ffe000000000000000003fd80000000000000000003eec000000, 0x3ffc008c8800000000000000000000000000000000035fc0088880000000000000000000000, 0xfffffffffffd993ff73ffffffffffffffe4c9fff9ff0000000000018900000000000000000002448000000])

def checkedSet150 : Claim := (5, [0x180001fc001800000f80000000000000000000000a8180001fd481800000f80000000000000000000000, 0x33fff93f9273fffffffff77fffc9ffff7bfffffffff3008090090600800600302000048000020000006000, 0xc0181e01e1801801c00e080000f000008000001c000c010160161801001800c080000b0000080000018000, 0xfc18000001ec180000000a8000000000a4000000000a818000001481800000000000000000000000000000, 0xfc18180181ec1800c0060a8000c00000a400000c000fc181d81d9ec1800e0070a8000ec0000a400000e000, 0xfc181fc1fc00000000000a8000fe000000000000000fc181d81d800000000000a8000ec000000000000000])

def checkedSet151 : Claim := (6, [0x218002180021e000c0e00730001c600038f0000f9c02100021000216000c0c001200004400008b0000298, 0x3e0003e0003e0000ff000700001c00003f00000fe000a0000a0000a000015000600001800003700000d60, 0x3f800000003ffc0000000730000000003ffe00000003f800000003fd80000000730000000003eec000000, 0x3f8003f8003f800073600730001c600038c000098c03f8003f8003fd80073700730001c60003eec0009ce, 0x3f8003f8003ffc00fff800000000000000000000000358003580035fc00eaf80000000000000000000000, 0xfd9fffd9fffd993ff30fffcfffff3ffffe4c9fff87f0188001880018900030300410001020002448000846])

def checkedSet152 : Claim := (6, [0x1f0001fc001fc0000f80000000000000000000000a81f0001fd481fc0000f80000000000000000000000, 0x33faf93f9063f93ffffff77fffc9fffd6bfffffffff300a090090600900600302000048000020000006000, 0xc01c1e01e3801e01c00e080000f000028000001c000c014160163801601800c080000b0000280000018000, 0xfc18180181ec1800c0060a8000c00000a400000c000fc1f1d81d9ec1d80e0070a8000ec0000a400000e000, 0xfc1f000003fc1fc000000a8000000002b4000000000a81f000001481d80000000000000000000000000000, 0xfc1f1fc1fdec1800c0060a8000fe0000a400000c000fc1f1d81d9ec1d80e0070a8000ec0000a400000e000])

def checkedSet153 : Claim := (5, [0x20000050000000000004003000a000000000000000020000050000000000004003000a0020, 0x1a008035000000000000c007006a0060000000000000a000015000000000000c007002a0060, 0x600008200000000000000c600006a20000000000000200008200000000000000020000402000, 0x61a100000000000000000c60708000000000000000041a100000000000000000c40608000000, 0x61a108235100000000000c600006a20000000000000610108220100000000000020000402000, 0xffffffffff9e5ff7fceffffffffffff39ffff9dffff0000000000000000004000000000000000100080020])

def checkedSet154 : Claim := (5, [0x50001fc0006c0000f8000000000000000000000088050001fd0806c0000f80000000000000000000000, 0x33faf93f9063f93ffffff77fffc9fffd6bfffffffff0000090090000000600300000048000000000006000, 0xc0041e01e3800601c00e080000f000028000001c000c004160163800601800c080000b0000280000018000, 0xcc001801818c0000c006088000c000008400000c000cc051d81d98c0480e007088000ec00008400000e000, 0xcc050000039c06c00000088000000002940000000008805000001080480000000000000000000000000000, 0xcc051fc1fc0000000000088000fe000000000000000cc051d81d80000000000088000ec000000000000000])

def checkedSet155 : Claim := (5, [0x3e008030000000000000c03800600800000000000000a000010000000000000c03000200800, 0x10a600000000000000000050980000000000000000010a7000000000000000000509880000000, 0x1680008400000000000000d680006040000000000000200008400000000000000020000404000, 0x16bf800000000000000000d6b8c000000000000000014bf800000000000000000d4b8c0000000, 0x16bf808430200000000000d6800060400000000000016b5808420200000000000020000404000, 0xffffffffff961ff7fcfffffffffffff397fff9fffff0000000001021000000000000000000100880000000])

def checkedSet156 : Claim := (5, [0x500006c001fc0000f80000000000000000000000880500006d481fc0000f80000000000000000000000, 0x33faf93f9063f93ffffff77fffc9fffd6bfffffffff0000000000600900600300000000000020000006000, 0xc004060063801e01c00e0800003000028000001c000c004060063801601800c08000030000280000018000, 0xcc00000001ec1800c006088000000000a400000c000cc05048049ec1d80e007088000240000a400000e000, 0xcc05000003fc1fc00000088000000002b40000000008805000001481d80000000000000000000000000000, 0xcc0506c06c000000000008800036000000000000000cc05048048000000000008800024000000000000000])

def checkedSet157 : Claim := (5, [0x3e0e03e00000000000060701f01c0000000000000000a0000a00000000000060600501800000000000000, 0xc21f9fe1ffffffffffff987ff0fffffffffffffffffc210902100000000000018121080440000000000000, 0xce60a02600000000000039b01300c00000000000000ce70b02700000000000039b21380c40000000000000, 0xfc00f8000000000000007f801fc00000000000000005400f8000000000000000a801ac0000000000000000, 0xfff800000000000000007ff30000000000000000000abf8000000000000000075730000000000000000000, 0xfff8f83f8000000000007f801fc0000000000000000ff58f8358000000000000a801ac0000000000000000])

def checkedSet158 : Claim := (6, [0x1f0001fc001fc0000f80000000000000000000000a81f0001fd481fc0000f80000000000000000000000, 0x33faf93f9063f93ffffff77fffc9fffd6bfffffffff300a090090600900600302000048000020000006000, 0xc01c1e01e3801e01c00e080000f000028000001c000c014160163801601800c080000b0000280000018000, 0xcc0506c06c000000000008800036000000000000000cc151481480000000000088000a4000000000000000, 0xfc18180181ec1800c0060a8000c00000a400000c000fc1f1d81d9ec1d80e0070a8000ec0000a400000e000, 0xfc1f000003fc1fc000000a8000000002b4000000000a81f000001481d80000000000000000000000000000])

def checkedSet159 : Claim := (4, [0x100c00c1000c40080000000060000100001000000000004004100044008000000002000010000100000, 0x4100c40c1040c400a000000006000010000100000084100440c1840c400a000000002000010000100000, 0xc410000001c40c00000008000000000140000000000841000000084080000000000000000000000000000, 0xc4120c40c0000000000008002060000000000000000c41208408000000000000800204000000000000000, 0xf3feff3ff3e3ff3fffffff7ffff9ffffebfffffffff0000000000000000000000000000000000000000000])

def checkedSet160 : Claim := (5, [0x1e01e0000001c00e000000f000000000001c0000000160160000001800c000000b0000000000018000, 0x30001fc0001c0000f8000000000000000000000028030001fc4801c0000f80000000000000000000000, 0x3c001801806c0000c006028000c000002400000c0003c031d81d86c0180e007028000ec00002400000e000, 0x3c030000007c01c00000028000000000340000000002803000000480180000000000000000000000000000, 0x3c031fc1fc0000000000028000fe0000000000000003c031d81d80000000000028000ec000000000000000, 0xf3fef93f93e3ff3fffffff7fffc9ffffebfffffffff3002090090600100600302000048000020000006000])

def checkedSet161 : Claim := (5, [0x1e00e03f000000000000c007007e0060000000000000a000015000000000000c007002a0060, 0x6de00a033000000000000c6c00066000000000000006de18a233100000000000c6c60c662042, 0x7c000e300000000000000c7c0007e3000000000000034000e300000000000000034000543000, 0x7de1c0000000000000000c7c70e000000000000000049e180000000000000000c4860c000000, 0x7de1ce33f180000000000c7c0007e300000000000007d41ce32a180000000000034000543000, 0xffffffffffe39f39ff0ffffffffffffbe3cf9e1ffff0000000000618108230100000000000860408602042])

def checkedSet162 : Claim := (5, [0x3e0000000000ec000000000000000000000000000013e0000000008ec000000, 0x7300018000038c000090000000000000000000000007fe001b00003eec000940, 0x7380018000038e0000d0000000000000000000000001280000000008a0000000, 0x7fe000000003fec00000000000000000000000000007fe000000003eec000000, 0x7fe001b8000000000000000000000000000000000007fe001b00000000000000, 0xffffffffffffffffffffffcb5fff67fffe4dbfffaff0000000000000000000000494001200002448000840])

def checkedSet163 : Claim := (5, [0x3fc1fc00000000000000002b40000000000000000001481d80000000000000000000000000000, 0x1fc001fc0000f8000000000000000000000000000001fd481fc0000f80000000000000000000000, 0x180181ec1800c006000000c00000a400000c00000001d81d9ec1d80e007000000ec0000a400000e000, 0x1e01e3801e01c00e000000f000028000001c0000000160163801601800c000000b0000280000018000, 0x1fc1fc0000000000000000fe00000000000000000001d81d80000000000000000ec000000000000000, 0xfffff93f9063f93fffffffffffc9fffd6bfffffffff0000090090600900600300000048000020000006000])

def checkedSet164 : Claim := (6, [0x21c000000021e000c0e007380000000038f0000f9c02140000000216000c0c001280000000008b0000298, 0x3e000000003e0000ff0007c0000000003f00000fe000a000000000a0000150006c0000000003700000d60, 0x3f800000003f8000736007300000000038c000098c03ff00000003fd800737007fe000000003eec0009ce, 0x3ff00000003ffc00000007fe000000003ffe00000003ff00000003fd800000007fe000000003eec000000, 0x3ff00000003ffc00fff80000000000000000000000035f000000035fc00eaf80000000000000000000000, 0xfd9afffffffd993ff30fffcb5ffffffffe4c9fff87f018a000000018900030300494000000002448000846])

def checkedSet165 : Claim := (7, [0x107380000003838f181cf9c00000000000000000000101280000003808b1818298, 0x607c0000000c03f01fe0fe000000000000000000000606c0000000c037002a0d60, 0x75000000000ffc001fff00000000000000000000000000000000002b4001d5f000, 0x75730000000def8c0e6c98c00000000000000000000757fe000000defeece6e9ce, 0x757fe000000fffffe00000000000000000000000000757fe000000d4beec000000, 0xffffffffffffffffffffcecb5ffffff8624c861f87f0000000000000000000044494000000862448606846])

def checkedSet166 : Claim := (6, [0xf83f80000000000000001fc1c600000000000005400f83f8000000000000a801fc1c60000000000000, 0x3e0e03e0003e000000060701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffffc210902101021000000018121080440100880000000, 0xce60a026010a6000000039b01300c00509800000000ce70b027010a7000000039b21380c40509880000000, 0xfc00f8000148000000007f801fc0000d480000000005400f8000000000000000a801ac0000000000000000, 0xfff8f83f814bf800000000000000000000000000000ff58f835814b5800000000000000000000000000000])

def checkedSet167 : Claim := (5, [0x3e000000003e0000000607c0000000c03e0000000000a000000000a0000000606c0000000c03600000000, 0x219a0000004199000000444b40000008424c8000000218a000000418900000044494000000842448000000, 0x5407fffffeb407ffffff8a8cfffffff2b473fffffff0000000000000000000000000000000000000000000, 0x821c000001021c000000107380000001038e000000082140000010214000000101280000001008a0000000, 0xa800000001480000000075000000000d480000000000000000000000000000000000000000000000000000, 0xabff0000014bfd80000000000000000000000000000ab5f0000014b5d80000000000000000000000000000])

def checkedSet168 : Claim := (6, [0x3e000000003e01a073060700000000c03800e6098000a000000000a000011060600000000c03000220900, 0x8a600000018e601204303130000000058d8008601808a700000018e701284343132000000058d880868188, 0xa800000001ec001ac00075000000000dec000e6c0000000000000a4001ac000000000000000a4000c4c000, 0xabf8000001eff800000075730000000def8c0000000abf80000014bf800000075730000000d4b8c0000000, 0xabf8000001eff81ac73600000000000000000000000ab58000001ef581ac62600000000000000000000000, 0xd61fffffff921ff5fccf9afffffffff393fff99ffff8210000001821010840410120000000180880808088])

def checkedSet169 : Claim := (5, [0xf83f80000000000000001fc1c600000000000005400f83f8000000000000a801fc1c60000000000000, 0x3e0e03e0003e000000060701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffffc210902101021000000018121080440100880000000, 0xce60a026010a6000000039b01300c00509800000000ce70b027010a7000000039b21380c40509880000000, 0xfc00f8000148000000007f801fc0000d480000000005400f8000000000000000a801ac0000000000000000, 0xfff8f83f814bf800000000000000000000000000000ff58f835814b5800000000000000000000000000000])

def checkedSet170 : Claim := (5, [0xa4a648000000000000001324d120000000000004400a4a648000000000008801324d12000000000000, 0x260a02600026000000020341300d00401a000000000020000200002000000020240100900401200000000, 0x319f5fd9fef59fffffffc64fecff3ffaf67ffffffff0000000000000000000000000000000000000000000, 0xc204842041020400000018309020c10101820000000c204842041020400000018109020410100820000000, 0xcc00a480010800000000398013240005080000000004400a48000000000000008801224000000000000000, 0xce65a4a6490a6480000000000000000000000000000ce45a4a4490a4480000000000000000000000000000])

def checkedSet171 : Claim := (6, [0x120430000000000000000008601800000000000000012843400000000000000000868188, 0x18040180001801a073040400c01000802000e609800080000800008000011040400401000802000220900, 0x300048000060001ac00046000c40000860000e6c000100048000020001ac00002000840000020000c4c000, 0x31880000006188000000464100000008620400000002188000000418800000044410000000842040000000, 0x318848188061881ac73600000000000000000000000310848108061081ac62600000000000000000000000, 0xce7fbfe7ff9e7ff5fccfb9fff3fffff79ffff99ffff0000000000000010840400000000000000000808088])

def checkedSet172 : Claim := (5, [0x100c00c1000c400c000042006183010306180000000000400410004400c000000002081010102180000, 0xc0100c00c1c00c000000180200600301c0060000000c4120c40c1c40c600a00180220600301c006140000, 0xc610000001c60c000002184200000041c3060000000861000000086080000021042000000408204000000, 0xc6120c60c1c60c000002184230618341c3060000000c61208608086080000021842304102408204000000, 0xc6120c60c1c60c600f0000000000000000000000000c4120c40c1c40c600a000000000000000000000000, 0xff9efff9f3ff9f3fff0ffffbdfffe7cfffcf9ffffff040020c000140006000000800206000014000140000])

def checkedSet173 : Claim := (5, [0x1ac73600000000000000000e6c98c000000000000001ae73700000000000000000e6e9ce, 0x31cc0e0000000000000000181cf9c00000000000000318c0c00000000000000001818298, 0x3e0ff000000000000000001fe0fe000000000000000000150000000000000000002a0d60, 0x3ff00000000000000000001fff000000000000000003ff00000000000000000001d5f000, 0x3fffff80000000000000000000000000000000000003ffeaf80000000000000000000000, 0xffffffffffffffc9f30fffffffffffffffffe61f87f0000000000000008630300000000000000000606846])

def checkedSet174 : Claim := (5, [0x180380f00783800f001c01c00000000000000000000180280b00583800b0018018, 0x1f8000fe0003fc00001f000000000000000000000000a8000fe0002b400001f000, 0x1f8300c00601ec0c000c00c000000000000000000001f83e0ec0761ec0ec00e00e, 0x1f83e0000003fc0fe000000000000000000000000001503e0000001480ec000000, 0x1f83e0fe07f3fc0fe000000000000000000000000001f83e0ec0761480ec000000, 0xffffffffffffffffffffe67f5fc9fe4c63fc9ffffff0000000000000000000006014048024060048006006])

def checkedSet175 : Claim := (5, [0x1fedf76000000000000000000000000000000000a801fedf76000000000000, 0x187390e1c701038e000000000000000000000000000181290a04501008a0000000, 0x464b4cc92648424c80000000000000000000000000046494c49224842448000000, 0x607c1f01f00c03e0000000000000000000000000000606c0501b00c03600000000, 0x7f801fec000d48000000000000000000000000000000a801aec000000000000000, 0xffffffffffffffffffff800ce03e39f2b473fffffff0000000000000000000000000000000000000000000])

def checkedSet176 : Claim := (6, [0x3e0e03e0003e000000060701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0x3e0f83f8003e000000060701fc1c60c0380000000054a0f83f8000a00000006ae01fc1c60c03000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffffc210902101021000000018121080440100880000000, 0xce60a026010a6000000039b01300c00509800000000ce70b027010a7000000039b21380c40509880000000, 0xfc00f8000148000000007f801fc0000d480000000005400f8000000000000000a801ac0000000000000000, 0xfff8f83f814bf800000000000000000000000000000ff58f835814b5800000000000000000000000000000])

def checkedSet177 : Claim := (6, [0x1f000000001d8000000003e0000000000ec000000035f000000035d8000000013e0000000008ec000000, 0x21c000000021c000000007380018000038e0000d0002140000000214000000001280000000008a0000000, 0x3f8000a0003f8000110007300018000038c000090003ff000a0003fd800110007fe001b00003eec000940, 0x3ff000a0003fd800000007fe001b80003fec00000003ff000a0003fd800000007fe001b00003eec000000, 0x3ff000a0003fd80015000000000000000000000000035f000000035d80000000000000000000000000000, 0xfd9afffdfffd9b7fffafffcb5fff67fffe4dbfffaff018a000800018900010000494001200002448000840])

def checkedSet178 : Claim := (6, [0x21c0021e0021e000c0e00738001c780038f0000f9c02140021600216000c0c001280004580008b0000298, 0x3e0003e0003e0000ff0007c0001f80003f00000fe000a0000a0000a0000150006c0001b80003700000d60, 0x3f8003f8003f800073600730001c600038c000098c03ff003fd803fd800737007fe001f76003eec0009ce, 0x3ff003ffc03ffc00000007fe001fff003ffe00000003ff003fd803fd800000007fe001f76003eec000000, 0x3ff003ffc03ffc00fff80000000000000000000000035f0035fc035fc00eaf80000000000000000000000, 0xfd9affd993fd993ff30fffcb5fff264ffe4c9fff87f018a001890018900030300494001224002448000846])

def checkedSet179 : Claim := (5, [0x10f1c7800000181cf9c00000000000000000000000010b0458000001818298, 0x1f01f80000001fe0fe00000000000000000000000000501b800000002a0d60, 0x1fc1c60000000e6c98c0000000000000000000000001fedf76000000e6e9ce, 0x1ffe000000001fff0000000000000000000000000001afe000000001d5f000, 0x1ffffff0000000000000000000000000000000000001fedf76000000000000, 0xffffffffffffffffffffffffecc9264fffffe61f87f0000000000000000000000000c49224000000606846])

def checkedSet180 : Claim := (5, [0x491890000000000000000c492240000000000001000491890000000000002000c49224000000000000, 0x80800800008000000004100410200020400000000000000000000000000000000000000000000000000, 0x180401800018000000040480c012008024000000000080000800008000000040480401200802400000000, 0x3000490000400000000046000c480008400000000001000490000000000000002000848000000000000000, 0x318a491890418900000000000000000000000000000310a491090410900000000000000000000000000000, 0xce77b7e77fbe77ffffffb9bef3befdf7bdfbfffffff0000000000000000000000000000000000000000000])

def checkedSet181 : Claim := (5, [0x20810101021800000000000000000000000000000002081010102180400, 0x80320992101331806000000000000000000000000000012089210113180600, 0x180010320003900019800000000000000000000000008001032000290001900000, 0x181080000003909320000000000000000000000000010108000000100820000000, 0x181090324993909320000000000000000000000000018109020410100820000000, 0xffffffffffffffffffffe7ff7fcdfe6c6ffcdffffff0000000000000000000000000000080000100080400])

def checkedSet182 : Claim := (5, [0x1ac00000000000000000000c4c000000000000000001ae00000000000000000000c4e000, 0x31c8080000000000000000181c6100000000000000031880800000000000000001818210, 0x3e08c000000000000000001dc06200000000000000000004000000000000000000080420, 0x3ff00000000000000000001ddf000000000000000003ff00000000000000000001d5f000, 0x3ff8c880000000000000000000000000000000000003ff88880000000000000000000000, 0xffffffffffffffc9f73fffffffffffffffffe63f9ff0000000000000008600000000000000000000406000])

def checkedSet183 : Claim := (5, [0x33faf93f9063f93ffffffffffffffffffffffffffff300a090090600900600300000000000000000000000, 0xc01c1e01e3801e01c00e00000000000000000000000c014160163801601800c00000000000000000000000, 0xfc001fc003fc0001f0000000000000000000000000054001fc002b40001f00000000000000000000000000, 0xfc18180181ec1800c00600000000000000000000000fc1f1d81d9ec1d80e00700000000000000000000000, 0xfc1f000003fc1fc0000000000000000000000000000a81f000001481d80000000000000000000000000000, 0xfc1f1fc1fffc1fc0000000000000000000000000000fc1f1d81d9481d80000000000000000000000000000])

def checkedSet184 : Claim := (5, [0xb827800000000000000013c0c600000000000005400b8278000000000000a8013c0c60000000000000, 0x260a02600026000000020301300c004018000000000020000200002000000020200100800401000000000, 0xc39fdff9ffb79fffffffd87ffcfffffbb7fffffffffc210902101021000000018121080440100880000000, 0xce60a026010a6000000039b01300c00509800000000ce70b027010a7000000039b21380c40509880000000, 0xfc00b8000148000000003f8013c00005480000000005400b8000000000000000a8012c0000000000000000, 0xfe78b827814a7800000000000000000000000000000fe58b825814a5800000000000000000000000000000])

def checkedSet185 : Claim := (5, [0xa03f80000000000000001301c600000000000004400a03f80000000000008801301c60000000000000, 0x3e0a03e0003e000000020701301c0040380000000000a0000a0000a000000020600101800403000000000, 0xcc00a000010800000000398013000005080000000004400a00000000000000008801200000000000000000, 0xce60a026010a6000000039b01300c00509800000000ce70a027010a7000000039b21300c40509880000000, 0xcff8a03f810bf800000000000000000000000000000cf58a035810b5800000000000000000000000000000, 0xf21fdfe1fff61fffffffde7ffcfffffbf7fffffffffc210802101021000000018121000440100880000000])

def checkedSet186 : Claim := (5, [0x4a03619b2103371806000000000000000000000000000012089210113180600, 0x2184230618341c3061e00000000000000000000000021a4230698341d3061e0500, 0x3980133600079c0019e00000000000000000000000008801236000294001940000, 0x39b4a00000079db36000000000000000000000000003134a000000509a24000000, 0x39b4b336d9b79db360000000000000000000000000039b4b324d12509a24000000, 0xffffffffffffffffffffe67f5fc9fe4c63fc9ffffff00000000000000000000202401009804013000a0500])

def checkedSet187 : Claim := (5, [0x781f80000000000000000fc00600000000000005400781f8000000000000a800fc0060000000000000, 0x1e0601e0001e000000060000f00000c0000000000000a0000a0000a000000060000500000c00000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffffc010100101001000000018020080040100080000000, 0xcc60200601086000000039800300000508000000000cc70300701087000000039820380040508080000000, 0xfc0078000148000000007f800fc0000d48000000000540078000000000000000a800ac0000000000000000, 0xfdf8781f8149f800000000000000000000000000000fd58781581495800000000000000000000000000000])

def checkedSet188 : Claim := (5, [0x902b00000000000000001581c400000000000004000902b00000000000008001581c40000000000000, 0xa0000a0000a000000060000500000c0000000000000a0000a0000a000000060600501800c03000000000, 0x2a0802a0002a000000060701501c00c0380000000000a0000a0000a000000060600501800c03000000000, 0x3ddf7fddfefddfffffffc7cfeeff3ffafe7ffffffff0080000800008000000040400401000802000000000, 0xc000900001000000000078001580000d000000000004000900000000000000008001080000000000000000, 0xc2b0902b0102b000000000000000000000000000000c210902101021000000000000000000000000000000])

def checkedSet189 : Claim := (5, [0x603f80000000000000000f01c600000000000001400603f80000000000002800f01c60000000000000, 0x3e0603e0003e000000060700f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0xe602026000a6000000021b00300c004098000000000e702027000a7000000021b20300c40409880000000, 0x3c00600000480000000067800f00000c480000000001400600000000000000002800a00000000000000000, 0x3ff8603f804bf8000000000000000000000000000003f586035804b5800000000000000000000000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffff0210002100021000000000120000440000880000000])

def checkedSet190 : Claim := (5, [0x803e0182100300130100000000000000000000000000012008210010011010, 0x280000e000034000003000000000000000000000000280004e000034000007000, 0x1a8000fe0003b400001f000000000000000000000000a8000fe0002b400001f000, 0x1a8280000003b40b000000000000000000000000000100280000001000a0000000, 0x1a8280fe0583b40b0000000000000000000000000001a8280ec0501000a0000000, 0xffffffffffffffffffffe77f7fc9fe7c6bfcfffffff0000000000000000000002000048000020000006000])

def checkedSet191 : Claim := (5, [0x601e00000000000000001fc1c600000000000001400601e0000000000000a801fc1c60000000000000, 0x1e0601e0001e000000060701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0xc60200600086000000039b01300c005098000000000c60200600086000000039b21380c40509880000000, 0x3c0060000048000000007f801fc0000d48000000000140060000000000000000a801ac0000000000000000, 0x3de0601e0049e0000000000000000000000000000003d40601400494000000000000000000000000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffff0000000000000000000018121080440100880000000])

def checkedSet192 : Claim := (6, [0xf83f80000000000000001fc1c600000000000005400f83f8000000000000a801fc1c60000000000000, 0x3e0e03e0003e000000060701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0x3de0601e0049e0000000000000000000000000000003d48681480494800000000000000000000000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffffc210902101021000000018121080440100880000000, 0xce60a026010a6000000039b01300c00509800000000ce70b027010a7000000039b21380c40509880000000, 0xfc00f8000148000000007f801fc0000d480000000005400f8000000000000000a801ac0000000000000000])

def checkedSet193 : Claim := (4, [0x7c0021000013000000000300002000000100000000024002100001100000000010000200000010000, 0x140007c00234000130000000003000020000001000014000bc002340001700000000010000200000010000, 0x5400000002b400000000080000000002800000000000000000000000000000000000000000000000000000, 0x54001fc002b400000000080000b000028000000000054001d80000000000000080000a0000000000000000, 0xbbfff93ffd6bfffffffff7ffffcffffd7ffffffffff1000090000200000600000000000000000000000000])

def checkedSet194 : Claim := (5, [0x183f800000000000000000c1c600000000000005400183f8000000000000a8000c1c60000000000000, 0x3e0003e0003e000000000700001c0000380000000000a0000a0000a000000000600001800003000000000, 0xc21fffe1ffb61ffffffff87fffffffffb7fffffffffc210102101021000000018120080440100880000000, 0xce600026010a6000000019b00000c00109800000000ce701027010a7000000019b20080c40109880000000, 0xfc0018000148000000001f8000c0000148000000000540018000000000000000a8000c0000000000000000, 0xfff8183f814bf800000000000000000000000000000ff581835814b5800000000000000000000000000000])

def checkedSet195 : Claim := (5, [0xfe00000000001f0000000000000000000000000001afe000000001d5f000, 0x10f180000000181cd0000000000000000000000000010b0000000001818000, 0x1fc1800000000e6c9000000000000000000000000001fedb00000000e6e940, 0x1ffe000000001fff0000000000000000000000000001afe000000001d5f000, 0x1fffb800000000000000000000000000000000000001fedb00000000000000, 0xffffffffffffffffffffffffecc967ffffffe61faff0000000000000000000000000c49200000000606840])

def checkedSet196 : Claim := (6, [0x1f01f80000001fe0fe00000000000000000000000000501b800000002a0d60, 0x180180000000c00600001fc1c60000000e6c98c00001d81d8000000e00700001fedf76000000e6e9ce, 0x1e01e0000001c00e000010f1c7800000181cf9c0000160160000001800c000010b0458000001818298, 0x1fc000000001f00000001ffe000000001fff00000001fc000000001f00000001afe000000001d5f000, 0x1fc1fc000000000000001ffffff00000000000000001d81d8000000000000001fedf76000000000000, 0xfffff93f93ffffffffffffffecc9264fffffe61f87f0000090090000000600300000c49224000000606846])

def checkedSet197 : Claim := (6, [0x60701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0xf83f80000000000000001fc1c600000000000005400f83f8000000000000a801fc1c60000000000000, 0x3e0e03e0003e000000060701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0xc21f9fe1ffb61fffffff987ff0fffff3b7fffffffffc210902101021000000018121080440100880000000, 0xce60a026010a6000000039b01300c00509800000000ce70b027010a7000000039b21380c40509880000000, 0xfc00f8000148000000007f801fc0000d480000000005400f8000000000000000a801ac0000000000000000])

def checkedSet198 : Claim := (5, [0x7f801fc0000d48000000000000000000000000000000a801ac0000000000000000, 0x3f80000000000000001fc1c600000000000000000003f8000000000000a801fc1c60000000000000, 0x260002600026000000039b01300c005098000000000270002700027000000039b21380c40509880000000, 0x3e0003e0003e000000060701f01c00c0380000000000a0000a0000a000000060600501800c03000000000, 0x3f8003f8003f8000000000000000000000000000000358003580035800000000000000000000000000000, 0xfe1fffe1fffe1fffffff987ff0fffff3b7fffffffff0210002100021000000018121080440100880000000])

def checkedSet199 : Claim := (6, [0x10f1c7800000181cf9c00000000000000000000000010b0458000001818298, 0x1f01f80000001fe0fe00000000000000000000000000501b800000002a0d60, 0x1fc1c60000000e6c98c0000000000000000000000001fedf76000000e6e9ce, 0x1ffe000000001fff0000000000000000000000000001afe000000001d5f000, 0x1ffffff0000000000000000000000000000000000001fedf76000000000000, 0xffffffffffffffffffffffffecc9264fffffe61f87f0000000000000000000000000c49224000000606846])

end Check515

namespace Check515
def claims : List Claim := [checkedSet0, checkedSet1, checkedSet2, checkedSet3, checkedSet4, checkedSet5, checkedSet6, checkedSet7, checkedSet8, checkedSet9, checkedSet10, checkedSet11, checkedSet12, checkedSet13, checkedSet14, checkedSet15, checkedSet16, checkedSet17, checkedSet18, checkedSet19, checkedSet20, checkedSet21, checkedSet22, checkedSet23, checkedSet24, checkedSet25, checkedSet26, checkedSet27, checkedSet28, checkedSet29, checkedSet30, checkedSet31, checkedSet32, checkedSet33, checkedSet34, checkedSet35, checkedSet36, checkedSet37, checkedSet38, checkedSet39, checkedSet40, checkedSet41, checkedSet42, checkedSet43, checkedSet44, checkedSet45, checkedSet46, checkedSet47, checkedSet48, checkedSet49, checkedSet50, checkedSet51, checkedSet52, checkedSet53, checkedSet54, checkedSet55, checkedSet56, checkedSet57, checkedSet58, checkedSet59, checkedSet60, checkedSet61, checkedSet62, checkedSet63, checkedSet64, checkedSet65, checkedSet66, checkedSet67, checkedSet68, checkedSet69, checkedSet70, checkedSet71, checkedSet72, checkedSet73, checkedSet74, checkedSet75, checkedSet76, checkedSet77, checkedSet78, checkedSet79, checkedSet80, checkedSet81, checkedSet82, checkedSet83, checkedSet84, checkedSet85, checkedSet86, checkedSet87, checkedSet88, checkedSet89, checkedSet90, checkedSet91, checkedSet92, checkedSet93, checkedSet94, checkedSet95, checkedSet96, checkedSet97, checkedSet98, checkedSet99, checkedSet100, checkedSet101, checkedSet102, checkedSet103, checkedSet104, checkedSet105, checkedSet106, checkedSet107, checkedSet108, checkedSet109, checkedSet110, checkedSet111, checkedSet112, checkedSet113, checkedSet114, checkedSet115, checkedSet116, checkedSet117, checkedSet118, checkedSet119, checkedSet120, checkedSet121, checkedSet122, checkedSet123, checkedSet124, checkedSet125, checkedSet126, checkedSet127, checkedSet128, checkedSet129, checkedSet130, checkedSet131, checkedSet132, checkedSet133, checkedSet134, checkedSet135, checkedSet136, checkedSet137, checkedSet138, checkedSet139, checkedSet140, checkedSet141, checkedSet142, checkedSet143, checkedSet144, checkedSet145, checkedSet146, checkedSet147, checkedSet148, checkedSet149, checkedSet150, checkedSet151, checkedSet152, checkedSet153, checkedSet154, checkedSet155, checkedSet156, checkedSet157, checkedSet158, checkedSet159, checkedSet160, checkedSet161, checkedSet162, checkedSet163, checkedSet164, checkedSet165, checkedSet166, checkedSet167, checkedSet168, checkedSet169, checkedSet170, checkedSet171, checkedSet172, checkedSet173, checkedSet174, checkedSet175, checkedSet176, checkedSet177, checkedSet178, checkedSet179, checkedSet180, checkedSet181, checkedSet182, checkedSet183, checkedSet184, checkedSet185, checkedSet186, checkedSet187, checkedSet188, checkedSet189, checkedSet190, checkedSet191, checkedSet192, checkedSet193, checkedSet194, checkedSet195, checkedSet196, checkedSet197, checkedSet198, checkedSet199]

def bucket0 (k : Nat) : Option Hint :=
  if k ≤ 395581120 then (if k ≤ 227833472 then (if k ≤ 120613696 then (if k ≤ 43182240 then (if k = 43182240 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k = 120613696 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none)) else (if k ≤ 196366112 then (if k = 196366112 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 26) else none) else (if k ≤ 204072512 then (if k = 204072512 then some (0x3c031fc1fc7c01c1f00f828000fe00003400001f000, 12, 160) else none) else (if k = 227833472 then some (0xabf8000000418800000075730000000842040000000, 30, 57) else none)))) else (if k ≤ 357000512 then (if k ≤ 264251360 then (if k = 264251360 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k ≤ 328995808 then (if k = 328995808 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 357000512 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none))) else (if k ≤ 364526688 then (if k = 364526688 then some (0x1fc1fffc1fc1f00f800000b00583800b0018018, 3, 107) else none) else (if k ≤ 373841792 then (if k = 373841792 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 395581120 then some (0x3fd8000000030300000501f76000000200846, 1, 58) else none))))) else (if k ≤ 663261024 then (if k ≤ 538801472 then (if k ≤ 513136832 then (if k = 513136832 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k ≤ 533645120 then (if k = 533645120 then some (0x54001fc002b40001f000080000b0000280000018000, 15, 116) else none) else (if k = 538801472 then some (0xfc1b19c19dfc19c0f0078a8000ce0000b400000f000, 12, 148) else none))) else (if k ≤ 553823872 then (if k = 553823872 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none) else (if k ≤ 633623360 then (if k = 633623360 then some (0xfc1f1fc1fffc1fc1f00f9f83e0fe07f3fc0fe01f01f, 0, 81) else none) else (if k = 663261024 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)))) else (if k ≤ 822834400 then (if k ≤ 794282240 then (if k = 794282240 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k ≤ 818191424 then (if k = 818191424 then some (0x7ff31fc1c60ffffffffffff, 0, 9) else none) else (if k = 822834400 then some (0xabff0000004189000000757fe000000842448000000, 27, 37) else none))) else (if k ≤ 850111936 then (if k = 850111936 then some (0xc61208608086080000021842304102408204000000, 26, 109) else none) else (if k ≤ 915318464 then (if k = 915318464 then some (0x3188481880418800000046410c41020842040000000, 30, 120) else none) else (if k = 939109664 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 25) else none)))))

def bucket1 (k : Nat) : Option Hint :=
  if k ≤ 592095969 then (if k ≤ 103051297 then (if k ≤ 62065089 then (if k ≤ 29398945 then (if k = 29398945 then some (0x38349130d98781b318a0780, 7, 40) else none) else (if k = 62065089 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none)) else (if k ≤ 83264993 then (if k = 83264993 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none) else (if k ≤ 88227233 then (if k = 88227233 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none) else (if k = 103051297 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none)))) else (if k ≤ 293782977 then (if k ≤ 179815777 then (if k = 179815777 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k ≤ 226773089 then (if k = 226773089 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 157) else none) else (if k = 293782977 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none))) else (if k ≤ 325679681 then (if k = 325679681 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 18) else none) else (if k ≤ 526187073 then (if k = 526187073 then some (0x7fffffedf76862448606846, 1, 30) else none) else (if k = 592095969 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none))))) else (if k ≤ 897762593 then (if k ≤ 633353793 then (if k ≤ 597684321 then (if k = 597684321 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k ≤ 602400673 then (if k = 602400673 then some (0x3fd8000000030300000001f76000000000846, 1, 68) else none) else (if k = 633353793 then some (0x3182411810618108230146084c08204860408602042, 1, 112) else none))) else (if k ≤ 665136609 then (if k = 665136609 then some (0xfc1d1ec1effc1ec0c0060a8000f60002b400000c000, 14, 146) else none) else (if k ≤ 739733025 then (if k = 739733025 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 897762593 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none)))) else (if k ≤ 935671169 then (if k ≤ 922323297 then (if k = 922323297 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k ≤ 928291969 then (if k = 928291969 then some (0xc61208608086080000021a42304902409204000000, 26, 122) else none) else (if k = 935671169 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))) else (if k ≤ 940353409 then (if k = 940353409 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k ≤ 946219265 then (if k = 946219265 then some (0x3fffff80000000000000001ffffff, 0, 173) else none) else (if k = 969721825 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none)))))

def bucket2 (k : Nat) : Option Hint :=
  if k ≤ 633973570 then (if k ≤ 189427650 then (if k ≤ 86040866 then (if k ≤ 10085986 then (if k = 10085986 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 108) else none) else (if k = 86040866 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 166) else none)) else (if k ≤ 134703170 then (if k = 134703170 then some (0xc61208608086080000021842304102408204000000, 26, 115) else none) else (if k ≤ 167315202 then (if k = 167315202 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 189427650 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none)))) else (if k ≤ 373320802 then (if k ≤ 201082530 then (if k = 201082530 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 373320802 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 85) else none)) else (if k ≤ 444589090 then (if k = 444589090 then some (0x39b4b336d9b79db379e0780, 7, 11) else none) else (if k ≤ 582937250 then (if k = 582937250 then some (0x7fffffedf76862448606846, 1, 30) else none) else (if k = 633973570 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 12) else none))))) else (if k ≤ 738018818 then (if k ≤ 659612770 then (if k ≤ 642975970 then (if k = 642975970 then some (0x3ffc00fff80000000000003ffe000fff, 0, 128) else none) else (if k = 659612770 then some (0x3182411810618108230146084c08204860408602042, 1, 112) else none)) else (if k ≤ 709823074 then (if k = 709823074 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k ≤ 728258018 then (if k = 728258018 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none) else (if k = 738018818 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none)))) else (if k ≤ 893672002 then (if k ≤ 744887970 then (if k = 744887970 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 38) else none) else (if k ≤ 842234594 then (if k = 842234594 then some (0x7de1ce33f180000000000c7c70e7e3063, 0, 161) else none) else (if k = 893672002 then some (0xc014160163801601800c180280b00583800b0018018, 3, 56) else none))) else (if k ≤ 974255970 then (if k = 974255970 then some (0xc2149621638216318c0c080010b0000280001818000, 15, 147) else none) else (if k ≤ 974619970 then (if k = 974619970 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 12) else none) else (if k = 987718210 then some (0x3ff000a0003fd800150007fe001b80003fec000d60, 5, 177) else none)))))

def bucket3 (k : Nat) : Option Hint :=
  if k ≤ 450486211 then (if k ≤ 129517219 then (if k ≤ 44923619 then (if k ≤ 35987747 then (if k = 35987747 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 44923619 then some (0xfff8f83f81eff81ac7367ff31fc1c60def8c0e6c98c, 2, 22) else none)) else (if k ≤ 71530339 then (if k = 71530339 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 26) else none) else (if k ≤ 81904003 then (if k = 81904003 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 129517219 then some (0xc4120c40c1c40c610a080800206000014000141000, 12, 65) else none)))) else (if k ≤ 350902659 then (if k ≤ 164274179 then (if k = 164274179 then some (0x39e66f60cf00000000000079db379e0780, 7, 24) else none) else (if k ≤ 345086691 then (if k = 345086691 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 130) else none) else (if k = 350902659 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none))) else (if k ≤ 367802179 then (if k = 367802179 then some (0x3fd8000000030300000001f76000000000846, 1, 53) else none) else (if k ≤ 404228963 then (if k = 404228963 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 450486211 then some (0x39b4b336d9b79db379e0780, 7, 11) else none))))) else (if k ≤ 645577379 then (if k ≤ 550814595 then (if k ≤ 495220707 then (if k = 495220707 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k ≤ 518634659 then (if k = 518634659 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 136) else none) else (if k = 550814595 then some (0xcc1f06c1ff9c1fc0000f980280300583800b0000018, 3, 100) else none))) else (if k ≤ 563883107 then (if k = 563883107 then some (0x7fffffedf76d4beec000000, 26, 175) else none) else (if k ≤ 622373923 then (if k = 622373923 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 135) else none) else (if k = 645577379 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)))) else (if k ≤ 841956003 then (if k ≤ 654330819 then (if k = 654330819 then some (0x3fffff80000000000000001ffffff, 0, 173) else none) else (if k ≤ 798222243 then (if k = 798222243 then some (0xcff8a03f810bf800000039f31301c6050b8c0000000, 30, 185) else none) else (if k = 841956003 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 85) else none))) else (if k ≤ 877318851 then (if k = 877318851 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none) else (if k ≤ 909619395 then (if k = 909619395 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 136) else none) else (if k = 925167843 then some (0x7fffffedf76d4beec000000, 26, 175) else none)))))

def bucket4 (k : Nat) : Option Hint :=
  if k ≤ 444339204 then (if k ≤ 144560804 then (if k ≤ 54791876 then (if k ≤ 6497028 then (if k = 6497028 then some (0xfff8f83f816bf80843027ff31fc1c60d6b8c0604804, 2, 29) else none) else (if k ≤ 6725092 then (if k = 6725092 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 54791876 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none))) else (if k ≤ 72738820 then (if k ≤ 59117060 then (if k = 59117060 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none) else (if k = 72738820 then some (0x39e66f60cf00000000000079db379e0780, 7, 24) else none)) else (if k ≤ 93606916 then (if k = 93606916 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k = 144560804 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none)))) else (if k ≤ 320047428 then (if k ≤ 211396868 then (if k ≤ 196083972 then (if k = 196083972 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k = 211396868 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)) else (if k ≤ 303593060 then (if k = 303593060 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 320047428 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none))) else (if k ≤ 358087300 then (if k ≤ 333224260 then (if k = 333224260 then some (0x3fd80015000000000000003fec000d60, 5, 105) else none) else (if k = 358087300 then some (0x1a8280fe0583b40b001f018, 3, 72) else none)) else (if k ≤ 385868068 then (if k = 385868068 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 444339204 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none))))) else (if k ≤ 616621220 then (if k ≤ 534650692 then (if k ≤ 476830276 then (if k = 476830276 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k ≤ 510703684 then (if k = 510703684 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 534650692 then some (0x1fffb80000001fffd60, 5, 195) else none))) else (if k ≤ 571795396 then (if k ≤ 545207300 then (if k = 545207300 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none) else (if k = 571795396 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none)) else (if k ≤ 572081348 then (if k = 572081348 then some (0x5400ffc002b4003ff000080010b0000280001818000, 15, 93) else none) else (if k = 616621220 then some (0x7fffffedf76d4beec000000, 26, 175) else none)))) else (if k ≤ 747658212 then (if k ≤ 681129188 then (if k ≤ 668295332 then (if k = 668295332 then some (0xfc181fc1fdec1801f00f8a8000fe0000a400001f000, 12, 150) else none) else (if k = 681129188 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none)) else (if k ≤ 718748388 then (if k = 718748388 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 85) else none) else (if k = 747658212 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none))) else (if k ≤ 822504740 then (if k ≤ 819488996 then (if k = 819488996 then some (0x318a491890418900000046494c49224842448000000, 27, 180) else none) else (if k = 822504740 then some (0x3ff003ffc03ffc00fff807fe001fff003ffe000fff, 0, 178) else none)) else (if k ≤ 899759716 then (if k = 899759716 then some (0xabf80000014bf800000075730000000d4b8c0000000, 30, 63) else none) else (if k = 915596228 then some (0x35fc0002400eaf80000000458000010000298, 3, 113) else none)))))

def bucket5 (k : Nat) : Option Hint :=
  if k ≤ 552054341 then (if k ≤ 245334373 then (if k ≤ 49013349 then (if k ≤ 26964613 then (if k = 26964613 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 49013349 then some (0xfc1f1fc1fffc1fc1f00f9f83e0fe07f3fc0fe01f01f, 0, 81) else none)) else (if k ≤ 79275045 then (if k = 79275045 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k ≤ 202279013 then (if k = 202279013 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 245334373 then some (0xffffffffffff, 0, 5) else none)))) else (if k ≤ 326419973 then (if k ≤ 309652581 then (if k = 309652581 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 326419973 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none)) else (if k ≤ 327737093 then (if k = 327737093 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k ≤ 433122277 then (if k = 433122277 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 552054341 then some (0xc2b0902b0102b000000078721581c40d03880000000, 31, 188) else none))))) else (if k ≤ 757451173 then (if k ≤ 715956773 then (if k ≤ 713513221 then (if k = 713513221 then some (0x3fd8000000030300000001f76000000000846, 1, 53) else none) else (if k = 715956773 then some (0xffffffffffff, 0, 73) else none)) else (if k ≤ 732305381 then (if k = 732305381 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k ≤ 749276517 then (if k = 749276517 then some (0xffc02400003ff8c880001afe089000001ddf631, 0, 142) else none) else (if k = 757451173 then some (0x7de1ce33f180000000000c7c70e7e3063, 0, 74) else none)))) else (if k ≤ 803000357 then (if k ≤ 778290885 then (if k = 778290885 then some (0x1a8280fe0583b40b001f018, 3, 190) else none) else (if k = 803000357 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none)) else (if k ≤ 831327173 then (if k = 831327173 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k ≤ 907646629 then (if k = 907646629 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k = 909157381 then some (0x7fe001fff003ffe000fff, 0, 134) else none)))))

def bucket6 (k : Nat) : Option Hint :=
  if k ≤ 520812838 then (if k ≤ 166393670 then (if k ≤ 26688582 then (if k ≤ 10704486 then (if k = 10704486 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k = 26688582 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)) else (if k ≤ 101507590 then (if k = 101507590 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k ≤ 149973030 then (if k = 149973030 then some (0x39b4b336d9b79db379e0780, 7, 11) else none) else (if k = 166393670 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none)))) else (if k ≤ 263510918 then (if k ≤ 179808806 then (if k = 179808806 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none) else (if k ≤ 256322054 then (if k = 256322054 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k = 263510918 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none))) else (if k ≤ 303045798 then (if k = 303045798 then some (0xc014160163801601800c180280b00583800b0018018, 3, 56) else none) else (if k ≤ 347588614 then (if k = 347588614 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k = 520812838 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none))))) else (if k ≤ 704793254 then (if k ≤ 658232678 then (if k ≤ 636383014 then (if k = 636383014 then some (0xc014160163801601800c080000b0000280000018000, 15, 69) else none) else (if k = 658232678 then some (0x5400ffc002b4003ff000080010b0000280001818000, 15, 93) else none)) else (if k ≤ 676215558 then (if k = 676215558 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 174) else none) else (if k ≤ 688786054 then (if k = 688786054 then some (0xfc1f1fc1fffc1fc1f00f9a8280fe0583b40b001f018, 3, 84) else none) else (if k = 704793254 then some (0xc2048620638206300c0018109030418380831800280, 7, 55) else none)))) else (if k ≤ 816858726 then (if k ≤ 766354438 then (if k = 766354438 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 166) else none) else (if k ≤ 774434758 then (if k = 774434758 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 816858726 then some (0x7fffffedf76862448606846, 1, 30) else none))) else (if k ≤ 877263718 then (if k = 877263718 then some (0x1ffffff000001ffffff, 0, 199) else none) else (if k ≤ 916906502 then (if k = 916906502 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k = 975172934 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none)))))

def bucket7 (k : Nat) : Option Hint :=
  if k ≤ 513151367 then (if k ≤ 195757671 then (if k ≤ 20013511 then (if k ≤ 2955591 then (if k = 2955591 then some (0x7fe001fff003ffe000fff, 0, 134) else none) else (if k = 20013511 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 117) else none)) else (if k ≤ 72304583 then (if k = 72304583 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 183) else none) else (if k ≤ 125786119 then (if k = 125786119 then some (0x3de361de1c7de1ce33f1e78c6f0e387c7c70e7e3063, 0, 31) else none) else (if k = 195757671 then some (0x3ff00000003fd800000007fe000000003eec000000, 26, 64) else none)))) else (if k ≤ 396171143 then (if k ≤ 268584807 then (if k = 268584807 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k ≤ 385861799 then (if k = 385861799 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 166) else none) else (if k = 396171143 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none))) else (if k ≤ 457477959 then (if k = 457477959 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 174) else none) else (if k ≤ 479962823 then (if k = 479962823 then some (0x318848188061881ac73646410c41020862040e6c98c, 2, 171) else none) else (if k = 513151367 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))))) else (if k ≤ 683714503 then (if k ≤ 636528167 then (if k ≤ 621380391 then (if k = 621380391 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k ≤ 623839495 then (if k = 623839495 then some (0x3ffc00fff80000000000003ffe000fff, 0, 128) else none) else (if k = 636528167 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none))) else (if k ≤ 662313831 then (if k = 662313831 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k ≤ 662874791 then (if k = 662874791 then some (0x7de1ce33f180000000000c7c70e7e3063, 0, 74) else none) else (if k = 683714503 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none)))) else (if k ≤ 843810919 then (if k ≤ 713657095 then (if k = 713657095 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none) else (if k ≤ 746603111 then (if k = 746603111 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 843810919 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none))) else (if k ≤ 887027303 then (if k = 887027303 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k ≤ 943782567 then (if k = 943782567 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 85) else none) else (if k = 957880007 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)))))

def bucket8 (k : Nat) : Option Hint :=
  if k ≤ 343172264 then (if k ≤ 216875368 then (if k ≤ 169213576 then (if k ≤ 13575144 then (if k = 13575144 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k ≤ 31015624 then (if k = 31015624 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k = 169213576 then some (0xfffffc00003fffff80001ffffff000001ffffff, 0, 143) else none))) else (if k ≤ 187889096 then (if k = 187889096 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k ≤ 196648552 then (if k = 196648552 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 67) else none) else (if k = 216875368 then some (0xabf80000014bf800000075730000000d4b8c0000000, 30, 63) else none)))) else (if k ≤ 280408488 then (if k ≤ 248181032 then (if k = 248181032 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k ≤ 260707528 then (if k = 260707528 then some (0x5400f8000020000840007ff31fc1c60862040604804, 2, 54) else none) else (if k = 280408488 then some (0xa81f000003fc1fc1f00f900280000003800b0018018, 3, 110) else none))) else (if k ≤ 284088008 then (if k = 284088008 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k ≤ 296271176 then (if k = 296271176 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none) else (if k = 343172264 then some (0x31a2411a1061a1082351660c4d08384c607086a2062, 1, 33) else none))))) else (if k ≤ 679741416 then (if k ≤ 555313736 then (if k ≤ 344980968 then (if k = 344980968 then some (0xce65a6e66f9e66f60cf039b4b336d9b79db379e0780, 7, 89) else none) else (if k ≤ 519406760 then (if k = 519406760 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k = 555313736 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))) else (if k ≤ 572470920 then (if k = 572470920 then some (0xfe78b827814a780000003fb313c0c605498c0000000, 30, 184) else none) else (if k ≤ 671355080 then (if k = 671355080 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 136) else none) else (if k = 679741416 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none)))) else (if k ≤ 821519176 then (if k ≤ 696893640 then (if k = 696893640 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k ≤ 746521928 then (if k = 746521928 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none) else (if k = 821519176 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none))) else (if k ≤ 922923720 then (if k ≤ 917545032 then (if k = 917545032 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k = 922923720 then some (0x7fffffedf76d4beec000000, 26, 175) else none)) else (if k ≤ 927149064 then (if k = 927149064 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 983617768 then some (0x3de361de1c7de1ce33f1e78c6f0e387c7c70e7e3063, 0, 31) else none)))))

def bucket9 (k : Nat) : Option Hint :=
  if k ≤ 536399529 then (if k ≤ 357759369 then (if k ≤ 205292745 then (if k ≤ 71707945 then (if k = 71707945 then some (0x3de0601e0049e00000007ff31fc1c60d4b8c0000000, 30, 191) else none) else (if k = 205292745 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none)) else (if k ≤ 252551369 then (if k = 252551369 then some (0xfc1f1fc1fffc1fc1f00f9f83e0fe07f3fc0fe01f01f, 0, 81) else none) else (if k = 357759369 then some (0xabf8000000418800000075730000000842040000000, 30, 57) else none))) else (if k ≤ 436139785 then (if k ≤ 409346025 then (if k = 409346025 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 436139785 then some (0x3fc1fc1f00f80000000000ffffffffffff, 0, 126) else none)) else (if k ≤ 507139209 then (if k = 507139209 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k = 536399529 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 117) else none)))) else (if k ≤ 843457897 then (if k ≤ 807550921 then (if k ≤ 613116585 then (if k = 613116585 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 807550921 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none)) else (if k ≤ 822232617 then (if k = 822232617 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 80) else none) else (if k = 843457897 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))) else (if k ≤ 882905385 then (if k ≤ 870447241 then (if k = 870447241 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 882905385 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)) else (if k ≤ 883731529 then (if k = 883731529 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k ≤ 931050249 then (if k = 931050249 then some (0x7fffffedf76d4beec000000, 26, 175) else none) else (if k = 990385033 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 52) else none)))))

def bucket10 (k : Nat) : Option Hint :=
  if k ≤ 512841066 then (if k ≤ 311471082 then (if k ≤ 142617418 then (if k ≤ 56009098 then (if k = 56009098 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 183) else none) else (if k ≤ 105377994 then (if k = 105377994 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k = 142617418 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 157) else none))) else (if k ≤ 199882570 then (if k ≤ 165898474 then (if k = 165898474 then some (0xfff8183f8061880043021ff300c1c60062040004804, 2, 46) else none) else (if k = 199882570 then some (0x5400ffc002b4003ff000080010b0000280001818000, 15, 93) else none)) else (if k ≤ 230436714 then (if k = 230436714 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 311471082 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none)))) else (if k ≤ 418730538 then (if k ≤ 387299946 then (if k ≤ 336442538 then (if k = 336442538 then some (0x7fffffedf76862448606846, 1, 30) else none) else (if k = 387299946 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none)) else (if k ≤ 396655498 then (if k = 396655498 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k = 418730538 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none))) else (if k ≤ 447167114 then (if k ≤ 424830378 then (if k = 424830378 then some (0x3fffff80000000000000001ffffff, 0, 173) else none) else (if k = 447167114 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)) else (if k ≤ 447290218 then (if k = 447290218 then some (0x3ff8c880000000000000001ddf631, 0, 182) else none) else (if k = 512841066 then some (0x1ffffff000001ffffff, 0, 199) else none))))) else (if k ≤ 824553706 then (if k ≤ 622618154 then (if k ≤ 562937450 then (if k = 562937450 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k ≤ 576778698 then (if k = 576778698 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 136) else none) else (if k = 622618154 then some (0x7fffffedf76d4beec000000, 26, 175) else none))) else (if k ≤ 759376938 then (if k ≤ 638705130 then (if k = 638705130 then some (0x3ff00000003fd800000007fe000000003eec000000, 26, 64) else none) else (if k = 759376938 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 38) else none)) else (if k ≤ 760467594 then (if k = 760467594 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 80) else none) else (if k = 824553706 then some (0x300a0b40b6700b41700b8200005a000230000017000, 12, 66) else none)))) else (if k ≤ 879952170 then (if k ≤ 853487466 then (if k ≤ 846674506 then (if k = 846674506 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none) else (if k = 853487466 then some (0x1ffffff000001ffffff, 0, 199) else none)) else (if k ≤ 866393162 then (if k = 866393162 then some (0x71814c33c18000000000087050a783063, 0, 91) else none) else (if k = 879952170 then some (0xfc1f1fc1fffc1fc1f00f9a8280fe0583b40b001f018, 3, 84) else none))) else (if k ≤ 917330826 then (if k ≤ 890039882 then (if k = 890039882 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none) else (if k = 917330826 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none)) else (if k ≤ 927460138 then (if k = 927460138 then some (0x3f8003f8003f80000007ff31fc1c60d4b8c0000000, 30, 198) else none) else (if k = 934822570 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 25) else none)))))

def bucket11 (k : Nat) : Option Hint :=
  if k ≤ 433110763 then (if k ≤ 276581355 then (if k ≤ 139847595 then (if k ≤ 130663659 then (if k = 130663659 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 76) else none) else (if k = 139847595 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)) else (if k ≤ 143330859 then (if k = 143330859 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 80) else none) else (if k ≤ 227371019 then (if k = 227371019 then some (0x39b4b336d9b79db379e0780, 7, 11) else none) else (if k = 276581355 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none)))) else (if k ≤ 327237227 then (if k ≤ 289756267 then (if k = 289756267 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k ≤ 310852555 then (if k = 310852555 then some (0xcc0506c06ffc1fc1f00f980080300183800b0018018, 3, 103) else none) else (if k = 327237227 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none))) else (if k ≤ 374231915 then (if k = 374231915 then some (0xc61208608086080000021842304102408204000000, 26, 115) else none) else (if k ≤ 422880299 then (if k = 422880299 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 135) else none) else (if k = 433110763 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none))))) else (if k ≤ 612751915 then (if k ≤ 526316555 then (if k ≤ 468433867 then (if k = 468433867 then some (0xffffffffffff, 0, 14) else none) else (if k = 526316555 then some (0xfff8f83f81eff81ac7367ff31fc1c60def8c0e6c98c, 2, 22) else none)) else (if k ≤ 568017419 then (if k = 568017419 then some (0x39b4b336d9b79db379e0780, 7, 11) else none) else (if k ≤ 570888267 then (if k = 570888267 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 612751915 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none)))) else (if k ≤ 696420651 then (if k ≤ 666053099 then (if k = 666053099 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k ≤ 689880843 then (if k = 689880843 then some (0xc2149621638216318c0c080010b0000280001818000, 15, 147) else none) else (if k = 696420651 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 166) else none))) else (if k ≤ 863251051 then (if k = 863251051 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k ≤ 919807723 then (if k = 919807723 then some (0x5400f8000020000840007ff31fc1c60862040604804, 2, 54) else none) else (if k = 963141643 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none)))))

def bucket12 (k : Nat) : Option Hint :=
  if k ≤ 408652524 then (if k ≤ 80528204 then (if k ≤ 32919660 then (if k ≤ 12280908 then (if k = 12280908 then some (0x1ffffff000001ffffff, 0, 199) else none) else (if k = 32919660 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 166) else none)) else (if k ≤ 34267148 then (if k = 34267148 then some (0x1fffb80000001fffd60, 5, 124) else none) else (if k ≤ 64264940 then (if k = 64264940 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 80528204 then some (0xfdf8781f8149f80000007f830fc0060d480c0000000, 30, 187) else none)))) else (if k ≤ 224334636 then (if k ≤ 167772748 then (if k = 167772748 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none) else (if k ≤ 211138124 then (if k = 211138124 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 16) else none) else (if k = 224334636 then some (0xc4120c40c1c40c600a000800206000014000140000, 18, 159) else none))) else (if k ≤ 262092012 then (if k = 262092012 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k ≤ 292982604 then (if k = 292982604 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none) else (if k = 408652524 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none))))) else (if k ≤ 664800556 then (if k ≤ 460811948 then (if k ≤ 425068428 then (if k = 425068428 then some (0x54a0f80a0020800841006ae01fc1800822000604800, 11, 59) else none) else (if k ≤ 453024172 then (if k = 453024172 then some (0x31824118107de1ce33f1c6084c08204c7c70e7e3063, 0, 20) else none) else (if k = 460811948 then some (0x39b4b336d9b79db379e0780, 7, 11) else none))) else (if k ≤ 559012556 then (if k = 559012556 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k ≤ 614044076 then (if k = 614044076 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none) else (if k = 664800556 then some (0x7fffffedf76862448606846, 1, 30) else none)))) else (if k ≤ 758780300 then (if k ≤ 682637356 then (if k = 682637356 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k ≤ 705593292 then (if k = 705593292 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k = 758780300 then some (0x3de0601e0061800803007ff31fc1c60862040604804, 2, 44) else none))) else (if k ≤ 759151724 then (if k = 759151724 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 174) else none) else (if k ≤ 824324204 then (if k = 824324204 then some (0xfc18f83f8060080843021f831fc1c60060040604804, 2, 48) else none) else (if k = 937259244 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none)))))

def bucket13 (k : Nat) : Option Hint :=
  if k ≤ 523685645 then (if k ≤ 349564685 then (if k ≤ 232660845 then (if k ≤ 41478957 then (if k = 41478957 then some (0x71814c33c18000000000087050a783063, 0, 1) else none) else (if k = 232660845 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none)) else (if k ≤ 276176973 then (if k = 276176973 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none) else (if k = 349564685 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 130) else none))) else (if k ≤ 449338317 then (if k ≤ 441571885 then (if k = 441571885 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 449338317 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 135) else none)) else (if k ≤ 503617229 then (if k = 503617229 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none) else (if k = 523685645 then some (0x39e66f60cf00000000000079db379e0780, 7, 24) else none)))) else (if k ≤ 819681645 then (if k ≤ 595304461 then (if k ≤ 589340333 then (if k = 589340333 then some (0x7fe001b80003fec000d60, 5, 162) else none) else (if k = 595304461 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none)) else (if k ≤ 646866125 then (if k = 646866125 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 819681645 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none))) else (if k ≤ 859129133 then (if k ≤ 828305005 then (if k = 828305005 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 176) else none) else (if k = 859129133 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none)) else (if k ≤ 868565261 then (if k = 868565261 then some (0x18109032499390933980680, 7, 3) else none) else (if k = 915675661 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none))))

def bucket14 (k : Nat) : Option Hint :=
  if k ≤ 464661422 then (if k ≤ 196650990 then (if k ≤ 81601742 then (if k ≤ 65693678 then (if k = 65693678 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k = 81601742 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none)) else (if k ≤ 128235694 then (if k = 128235694 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k = 196650990 then some (0xabf8000001eff81ac73675730000000def8c0e6c98c, 2, 168) else none))) else (if k ≤ 312666286 then (if k ≤ 300053486 then (if k = 300053486 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none) else (if k = 312666286 then some (0x1ffffff000001ffffff, 0, 70) else none)) else (if k ≤ 338816910 then (if k = 338816910 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 67) else none) else (if k ≤ 413705998 then (if k = 413705998 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 76) else none) else (if k = 464661422 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 174) else none))))) else (if k ≤ 731046542 then (if k ≤ 615574574 then (if k ≤ 465119822 then (if k = 465119822 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 615574574 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none)) else (if k ≤ 697938222 then (if k = 697938222 then some (0x318a491890418900000046494c49224842448000000, 27, 180) else none) else (if k = 731046542 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none))) else (if k ≤ 746403854 then (if k ≤ 731658190 then (if k = 731658190 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none) else (if k = 746403854 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none)) else (if k ≤ 806471982 then (if k = 806471982 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 60) else none) else (if k ≤ 827096974 then (if k = 827096974 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 85) else none) else (if k = 840971246 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)))))

def bucket15 (k : Nat) : Option Hint :=
  if k ≤ 482362703 then (if k ≤ 233814959 then (if k ≤ 76118703 then (if k ≤ 19166991 then (if k = 19166991 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none) else (if k ≤ 29009615 then (if k = 29009615 then some (0xa81f024027581fc11008900280100083000b0010010, 4, 114) else none) else (if k = 76118703 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 130) else none))) else (if k ≤ 87705167 then (if k = 87705167 then some (0xc2b0902b0102b000000078721581c40d03880000000, 31, 123) else none) else (if k ≤ 121859375 then (if k = 121859375 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 233814959 then some (0xfff8f83f816bf80843027ff31fc1c60d6b8c0604804, 2, 29) else none)))) else (if k ≤ 386116015 then (if k ≤ 234762319 then (if k = 234762319 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 98) else none) else (if k ≤ 282257231 then (if k = 282257231 then some (0xfff8183f814bf80000001ff300c1c6014b8c0000000, 30, 194) else none) else (if k = 386116015 then some (0x61a108235100000000000c607086a2062, 1, 13) else none))) else (if k ≤ 476437071 then (if k = 476437071 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k ≤ 480290319 then (if k = 480290319 then some (0xc2048620638206300c0039b4b336d9b79db379e0780, 7, 45) else none) else (if k = 482362703 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 26) else none))))) else (if k ≤ 695275727 then (if k ≤ 557872815 then (if k ≤ 516489455 then (if k = 516489455 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k ≤ 528017039 then (if k = 528017039 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k = 557872815 then some (0xfdf8781f8061880843027f830fc0060860040604004, 2, 39) else none))) else (if k ≤ 578464111 then (if k = 578464111 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k ≤ 584225551 then (if k = 584225551 then some (0x3188481880618808430246410c41020862040604804, 2, 111) else none) else (if k = 695275727 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 130) else none)))) else (if k ≤ 764552751 then (if k ≤ 704517615 then (if k = 704517615 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k ≤ 712355471 then (if k = 712355471 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k = 764552751 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none))) else (if k ≤ 926328495 then (if k ≤ 772857519 then (if k = 772857519 then some (0x54001fc002b40001f0000f8060fe0072fc00e01f003, 0, 83) else none) else (if k = 926328495 then some (0x757fe000000ffffffffffff, 0, 165) else none)) else (if k ≤ 986462671 then (if k = 986462671 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 85) else none) else (if k = 992588719 then some (0xc2048620638206300c0018109030418380831800280, 7, 55) else none)))))

def bucket16 (k : Nat) : Option Hint :=
  if k ≤ 516516272 then (if k ≤ 185364400 then (if k ≤ 109412912 then (if k ≤ 33659312 then (if k = 33659312 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k = 109412912 then some (0x31824118107de1ce33f1c6084c08204c7c70e7e3063, 0, 20) else none)) else (if k ≤ 135715728 then (if k = 135715728 then some (0x1afe089000001ddf631, 0, 7) else none) else (if k ≤ 138849776 then (if k = 138849776 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 185364400 then some (0xc014160163801601800c180280b00583800b0018018, 3, 56) else none)))) else (if k ≤ 315558224 then (if k ≤ 190218768 then (if k = 190218768 then some (0xfffffc00003fffff80001ffffff000001ffffff, 0, 143) else none) else (if k ≤ 259542256 then (if k = 259542256 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 117) else none) else (if k = 315558224 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 18) else none))) else (if k ≤ 426668144 then (if k = 426668144 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k ≤ 455604080 then (if k = 455604080 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 121) else none) else (if k = 516516272 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none))))) else (if k ≤ 810363472 then (if k ≤ 610484528 then (if k ≤ 535236304 then (if k = 535236304 then some (0x3fd80015000000000000003fec000d60, 5, 125) else none) else (if k = 610484528 then some (0x3188481880618808430246410c41020862040604804, 2, 111) else none)) else (if k ≤ 636470160 then (if k = 636470160 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k ≤ 656464240 then (if k = 656464240 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none) else (if k = 810363472 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 50) else none)))) else (if k ≤ 931752400 then (if k ≤ 853297072 then (if k = 853297072 then some (0x300a090093fc1fc1f00f820000480002b400001f000, 12, 62) else none) else (if k ≤ 887108816 then (if k = 887108816 then some (0xabf80000014bf800000075730000000d4b8c0000000, 30, 63) else none) else (if k = 931752400 then some (0xc2149621638216318c0c080010b0000280001818000, 15, 147) else none))) else (if k ≤ 944937744 then (if k = 944937744 then some (0x3ffc00fff80000000000003ffe000fff, 0, 128) else none) else (if k ≤ 977728208 then (if k = 977728208 then some (0x7fffffedf76d4beec000000, 26, 175) else none) else (if k = 979658384 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none)))))

def bucket17 (k : Nat) : Option Hint :=
  if k ≤ 511685073 then (if k ≤ 242578737 then (if k ≤ 33058001 then (if k ≤ 2503857 then (if k = 2503857 then some (0x1afe089000001ddf631, 0, 36) else none) else (if k ≤ 11353393 then (if k = 11353393 then some (0xc014160163801601800c180280b00583800b0018018, 3, 56) else none) else (if k = 33058001 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none))) else (if k ≤ 122673873 then (if k ≤ 116330161 then (if k = 116330161 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 25) else none) else (if k = 122673873 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none)) else (if k ≤ 181946769 then (if k = 181946769 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 242578737 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none)))) else (if k ≤ 405839217 then (if k ≤ 253897457 then (if k = 253897457 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k ≤ 284024017 then (if k = 284024017 then some (0x39b4b336d9b79db379e0780, 7, 34) else none) else (if k = 405839217 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none))) else (if k ≤ 476969809 then (if k ≤ 466235953 then (if k = 466235953 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 476969809 then some (0x3fd8000000030300000001f76000000000846, 1, 68) else none)) else (if k ≤ 505925457 then (if k = 505925457 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none) else (if k = 511685073 then some (0xcc051fc1ff9c06c1f00f980080b0058380030018018, 3, 101) else none))))) else (if k ≤ 700284881 then (if k ≤ 589938929 then (if k ≤ 563088881 then (if k = 563088881 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k ≤ 584582225 then (if k = 584582225 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 25) else none) else (if k = 589938929 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none))) else (if k ≤ 673990993 then (if k ≤ 624670417 then (if k = 624670417 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k = 673990993 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none)) else (if k ≤ 674292497 then (if k = 674292497 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 104) else none) else (if k = 700284881 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none)))) else (if k ≤ 866624625 then (if k ≤ 745777681 then (if k ≤ 727016113 then (if k = 727016113 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k = 745777681 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 141) else none)) else (if k ≤ 756074065 then (if k = 756074065 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 18) else none) else (if k = 866624625 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))) else (if k ≤ 912002385 then (if k ≤ 909560465 then (if k = 909560465 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k = 912002385 then some (0x7fffffedf76d4beec000000, 26, 175) else none)) else (if k ≤ 925228625 then (if k = 925228625 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 25) else none) else (if k = 936439249 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none)))))

def bucket18 (k : Nat) : Option Hint :=
  if k ≤ 577936594 then (if k ≤ 242470034 then (if k ≤ 63540466 then (if k ≤ 29533586 then (if k = 29533586 then some (0x39b4b336d9b79db379e0780, 7, 186) else none) else (if k = 63540466 then some (0xc21090210102100000007ff31fc1c60d4b8c0000000, 30, 118) else none)) else (if k ≤ 77636274 then (if k = 77636274 then some (0x300a0b40b6700b41700b8200005a000230000017000, 12, 145) else none) else (if k = 242470034 then some (0xffc00000003ff00000001ffffff000001ffffff, 0, 132) else none))) else (if k ≤ 453893490 then (if k ≤ 325209938 then (if k = 325209938 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none) else (if k = 453893490 then some (0xfc1d1ec1effc1ec0c006180280b00583800b0008008, 3, 92) else none)) else (if k ≤ 454202674 then (if k = 454202674 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k ≤ 504649266 then (if k = 504649266 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none) else (if k = 577936594 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none))))) else (if k ≤ 892849426 then (if k ≤ 752301490 then (if k ≤ 613299986 then (if k = 613299986 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none) else (if k = 752301490 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 197) else none)) else (if k ≤ 775928274 then (if k = 775928274 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 117) else none) else (if k ≤ 837176018 then (if k = 837176018 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 892849426 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)))) else (if k ≤ 938243314 then (if k ≤ 918582994 then (if k = 918582994 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 183) else none) else (if k = 938243314 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)) else (if k ≤ 968404434 then (if k = 968404434 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k ≤ 979179346 then (if k = 979179346 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 983924370 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 80) else none)))))

def bucket19 (k : Nat) : Option Hint :=
  if k ≤ 585267539 then (if k ≤ 183759059 then (if k ≤ 39354419 then (if k ≤ 21383123 then (if k = 21383123 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 39354419 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)) else (if k ≤ 94411507 then (if k = 94411507 then some (0x3f8003f8001880003027ff31fc1c60862040604804, 2, 51) else none) else (if k ≤ 95227891 then (if k = 95227891 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 183759059 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 32) else none)))) else (if k ≤ 254948083 then (if k ≤ 248410579 then (if k = 248410579 then some (0xce65a6e66f9e66f60cf039b4b336d9b79db379e0780, 7, 89) else none) else (if k = 254948083 then some (0xc4120c40c1c40c610a080800206000014000141000, 12, 65) else none)) else (if k ≤ 504240787 then (if k = 504240787 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k ≤ 526520243 then (if k = 526520243 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 174) else none) else (if k = 585267539 then some (0xc2b0902b0102b000000078721581c40d03880000000, 31, 123) else none))))) else (if k ≤ 827126355 then (if k ≤ 602513811 then (if k ≤ 594291731 then (if k = 594291731 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 602513811 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none)) else (if k ≤ 675173747 then (if k = 675173747 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none) else (if k ≤ 793217971 then (if k = 793217971 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 192) else none) else (if k = 827126355 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none)))) else (if k ≤ 952168979 then (if k ≤ 867166643 then (if k = 867166643 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 174) else none) else (if k = 952168979 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)) else (if k ≤ 958041715 then (if k = 958041715 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 121) else none) else (if k ≤ 972147539 then (if k = 972147539 then some (0x2b4003ff00000000000000ffffffffffff, 0, 129) else none) else (if k = 993437875 then some (0x678c6f0e387c7c70e7e3063, 0, 79) else none)))))

def bucket20 (k : Nat) : Option Hint :=
  if k ≤ 421142036 then (if k ≤ 188474708 then (if k ≤ 126289876 then (if k ≤ 111288404 then (if k = 111288404 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 12) else none) else (if k = 126289876 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none)) else (if k ≤ 148237908 then (if k = 148237908 then some (0xc2048620638206300c0039b4b336d9b79db379e0780, 7, 45) else none) else (if k = 188474708 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none))) else (if k ≤ 278569140 then (if k ≤ 204224468 then (if k = 204224468 then some (0xabf80000014bf800000075730000000d4b8c0000000, 30, 63) else none) else (if k = 278569140 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)) else (if k ≤ 307391540 then (if k = 307391540 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k ≤ 352252532 then (if k = 352252532 then some (0x7fffffedf76862448606846, 1, 30) else none) else (if k = 421142036 then some (0x7de1ce33f180000000000c7c70e7e3063, 0, 74) else none))))) else (if k ≤ 635947124 then (if k ≤ 526183732 then (if k ≤ 451934804 then (if k = 451934804 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 12) else none) else (if k = 526183732 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)) else (if k ≤ 549427060 then (if k = 549427060 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k ≤ 584990804 then (if k = 584990804 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none) else (if k = 635947124 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)))) else (if k ≤ 783572596 then (if k ≤ 715831124 then (if k = 715831124 then some (0xc4120c40c1c40c600a000800206000014000140000, 18, 61) else none) else (if k = 783572596 then some (0x7fffffedf76862448606846, 1, 30) else none)) else (if k ≤ 819301108 then (if k = 819301108 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k ≤ 876682932 then (if k = 876682932 then some (0x318a491890418900000046494c49224842448000000, 27, 180) else none) else (if k = 930528308 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none)))))

def bucket21 (k : Nat) : Option Hint :=
  if k ≤ 549369589 then (if k ≤ 236389461 then (if k ≤ 159103413 then (if k ≤ 138790773 then (if k ≤ 102267189 then (if k = 102267189 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 138790773 then some (0xcc051fc1ff9c06c1f00f888000fe00029400001f000, 12, 154) else none)) else (if k ≤ 159010165 then (if k = 159010165 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k = 159103413 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))) else (if k ≤ 193946933 then (if k ≤ 174125813 then (if k = 174125813 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none) else (if k = 193946933 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none)) else (if k ≤ 216327285 then (if k = 216327285 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 18) else none) else (if k = 236389461 then some (0x54001fc002b40001f000080000b0000280000018000, 15, 193) else none)))) else (if k ≤ 482136181 then (if k ≤ 337026069 then (if k ≤ 320381013 then (if k = 320381013 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 337026069 then some (0x3de0f83f80618008430267801fc1c60860000604804, 2, 43) else none)) else (if k ≤ 354260533 then (if k = 354260533 then some (0xabf8000000418800000075730000000842040000000, 30, 57) else none) else (if k = 482136181 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none))) else (if k ≤ 501075765 then (if k ≤ 497379797 then (if k = 497379797 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none) else (if k = 501075765 then some (0x7ffffffffffffffffffffff, 0, 10) else none)) else (if k ≤ 539994229 then (if k = 539994229 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 85) else none) else (if k = 549369589 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none))))) else (if k ≤ 678842613 then (if k ≤ 578467029 then (if k ≤ 554331829 then (if k ≤ 551570869 then (if k = 551570869 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k = 554331829 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none)) else (if k ≤ 554994325 then (if k = 554994325 then some (0x54a0f80a0020800841006ae01fc1800822000604800, 11, 59) else none) else (if k = 578467029 then some (0x7fffffedf76862448606846, 1, 30) else none))) else (if k ≤ 614080853 then (if k ≤ 594996757 then (if k = 594996757 then some (0xa81f024027581fc11008900280100083000b0010010, 4, 95) else none) else (if k = 614080853 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none)) else (if k ≤ 665407125 then (if k = 665407125 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k = 678842613 then some (0x678c6f0e387c7c70e7e3063, 0, 79) else none)))) else (if k ≤ 877915413 then (if k ≤ 689134293 then (if k ≤ 681769301 then (if k = 681769301 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k = 689134293 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none)) else (if k ≤ 791402933 then (if k = 791402933 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 877915413 then some (0x38216318c0c00000000000ffffffffffff, 0, 75) else none))) else (if k ≤ 901570229 then (if k ≤ 879802965 then (if k = 879802965 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 901570229 then some (0xffc00000003ff00000001ffffff000001ffffff, 0, 132) else none)) else (if k ≤ 935088949 then (if k = 935088949 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k ≤ 937389525 then (if k = 937389525 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none) else (if k = 972019893 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none))))))

def bucket22 (k : Nat) : Option Hint :=
  if k ≤ 595510134 then (if k ≤ 285438550 then (if k ≤ 232688918 then (if k ≤ 56125526 then (if k = 56125526 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k ≤ 83906294 then (if k = 83906294 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 232688918 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 174) else none))) else (if k ≤ 240405686 then (if k = 240405686 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none) else (if k ≤ 270119574 then (if k = 270119574 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k = 285438550 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none)))) else (if k ≤ 517527222 then (if k ≤ 428865910 then (if k = 428865910 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k ≤ 431607350 then (if k = 431607350 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 517527222 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none))) else (if k ≤ 550992918 then (if k = 550992918 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k ≤ 582492342 then (if k = 582492342 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 26) else none) else (if k = 595510134 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 136) else none))))) else (if k ≤ 827477174 then (if k ≤ 770436566 then (if k ≤ 626054230 then (if k = 626054230 then some (0x3ff00000003fd800000007fe000000003eec000000, 26, 64) else none) else (if k ≤ 761813878 then (if k = 761813878 then some (0xc014160163801601800c080000b0000280000018000, 15, 69) else none) else (if k = 770436566 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 135) else none))) else (if k ≤ 815469430 then (if k = 815469430 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k ≤ 825878902 then (if k = 825878902 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none) else (if k = 827477174 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 60) else none)))) else (if k ≤ 937958262 then (if k ≤ 843432214 then (if k = 843432214 then some (0xfff8f83f81eff81ac7367ff31fc1c60def8c0e6c98c, 2, 22) else none) else (if k ≤ 902982198 then (if k = 902982198 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 937958262 then some (0xcc0506c06ffc1fc1f00f888000360002b400001f000, 12, 156) else none))) else (if k ≤ 944628182 then (if k = 944628182 then some (0x16bf808430200000000000d6b8c0604804, 2, 102) else none) else (if k ≤ 967964374 then (if k = 967964374 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 104) else none) else (if k = 996641366 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)))))

def bucket23 (k : Nat) : Option Hint :=
  if k ≤ 473183991 then (if k ≤ 289828695 then (if k ≤ 108510263 then (if k ≤ 22849047 then (if k = 22849047 then some (0x3ff8603f804bf800000067f30f01c60c4b8c0000000, 30, 189) else none) else (if k ≤ 63718935 then (if k = 63718935 then some (0x3ffc00fff80000000000003ffe000fff, 0, 128) else none) else (if k = 108510263 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none))) else (if k ≤ 234015159 then (if k = 234015159 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k ≤ 265655223 then (if k = 265655223 then some (0x3fd8000000030300000501f76000000200846, 1, 58) else none) else (if k = 289828695 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none)))) else (if k ≤ 336245719 then (if k ≤ 294116375 then (if k = 294116375 then some (0x54001fc002b40001f000080000b0000280000018000, 15, 116) else none) else (if k ≤ 330224791 then (if k = 330224791 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 336245719 then some (0x46494c49224ffffffffffff, 0, 17) else none))) else (if k ≤ 460226263 then (if k ≤ 347198423 then (if k = 347198423 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k = 460226263 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)) else (if k ≤ 471459735 then (if k = 471459735 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none) else (if k = 473183991 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none))))) else (if k ≤ 679487927 then (if k ≤ 520405047 then (if k ≤ 476329111 then (if k = 476329111 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none) else (if k ≤ 511753367 then (if k = 511753367 then some (0x1fc1fffc1fc1f00f800000fe0002b400001f000, 12, 163) else none) else (if k = 520405047 then some (0x7fffffedf76d4beec000000, 26, 175) else none))) else (if k ≤ 593968279 then (if k ≤ 535500663 then (if k = 535500663 then some (0x3ff8603f80618808030267f30f01c60862040600804, 2, 41) else none) else (if k = 593968279 then some (0x660c4d08384c607086a2062, 1, 99) else none)) else (if k ≤ 594557911 then (if k = 594557911 then some (0x18109032499390933980680, 7, 181) else none) else (if k = 679487927 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none)))) else (if k ≤ 788586999 then (if k ≤ 687505559 then (if k = 687505559 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k ≤ 698266967 then (if k = 698266967 then some (0xa81f000003fc1fc1f00f900280000003800b0018018, 3, 110) else none) else (if k = 788586999 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none))) else (if k ≤ 936397879 then (if k ≤ 915330423 then (if k = 915330423 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k = 936397879 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 60) else none)) else (if k ≤ 971117303 then (if k = 971117303 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 988980727 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)))))

def bucket24 (k : Nat) : Option Hint :=
  if k ≤ 356270904 then (if k ≤ 219221112 then (if k ≤ 130179640 then (if k ≤ 1092408 then (if k = 1092408 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k ≤ 36999384 then (if k = 36999384 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k = 130179640 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none))) else (if k ≤ 200993560 then (if k ≤ 138936600 then (if k = 138936600 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none) else (if k = 200993560 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)) else (if k ≤ 218938328 then (if k = 218938328 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k = 219221112 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none)))) else (if k ≤ 256380984 then (if k ≤ 219633848 then (if k = 219633848 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none) else (if k ≤ 224080440 then (if k = 224080440 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 157) else none) else (if k = 256380984 then some (0x61a108235100000000000c607086a2062, 1, 153) else none))) else (if k ≤ 268538360 then (if k ≤ 266276984 then (if k = 266276984 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k = 268538360 then some (0xa81f024027581fc11008900280100083000b0010010, 4, 114) else none)) else (if k ≤ 322079416 then (if k = 322079416 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 67) else none) else (if k = 356270904 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none))))) else (if k ≤ 660210520 then (if k ≤ 529921336 then (if k ≤ 501844344 then (if k = 501844344 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 80) else none) else (if k ≤ 504499896 then (if k = 504499896 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 130) else none) else (if k = 529921336 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none))) else (if k ≤ 625791512 then (if k ≤ 541639960 then (if k = 541639960 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 12) else none) else (if k = 625791512 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 26) else none)) else (if k ≤ 655875032 then (if k = 655875032 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none) else (if k = 660210520 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none)))) else (if k ≤ 749251992 then (if k ≤ 723866584 then (if k ≤ 690734520 then (if k = 690734520 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 723866584 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 80) else none)) else (if k ≤ 738827096 then (if k = 738827096 then some (0xc61208608086080000021842304102408204000000, 26, 109) else none) else (if k = 749251992 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))) else (if k ≤ 832995800 then (if k ≤ 768085784 then (if k = 768085784 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 832995800 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)) else (if k ≤ 835539288 then (if k = 835539288 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 908465752 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)))))

def bucket25 (k : Nat) : Option Hint :=
  if k ≤ 317087577 then (if k ≤ 132672537 then (if k ≤ 68832345 then (if k ≤ 41189625 then (if k = 41189625 then some (0xfc181fc1fdec1801f00f980200b0058180080018018, 3, 96) else none) else (if k = 68832345 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 135) else none)) else (if k ≤ 109241881 then (if k = 109241881 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none) else (if k ≤ 117059769 then (if k = 117059769 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 25) else none) else (if k = 132672537 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 136) else none)))) else (if k ≤ 222102457 then (if k ≤ 157312665 then (if k = 157312665 then some (0x3ff00000003ffc00fff807fe000000003ffe000fff, 0, 164) else none) else (if k = 222102457 then some (0x3ffc008c880000000000003ffe000631, 0, 149) else none)) else (if k ≤ 235581017 then (if k = 235581017 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none) else (if k ≤ 240205081 then (if k = 240205081 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k = 317087577 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none))))) else (if k ≤ 688887193 then (if k ≤ 521136345 then (if k ≤ 350675865 then (if k = 350675865 then some (0x7fffffedf76862448606846, 1, 30) else none) else (if k = 521136345 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none)) else (if k ≤ 533041369 then (if k = 533041369 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k ≤ 571220505 then (if k = 571220505 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 80) else none) else (if k = 688887193 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none)))) else (if k ≤ 792017049 then (if k ≤ 718932089 then (if k = 718932089 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k = 792017049 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)) else (if k ≤ 823433657 then (if k = 823433657 then some (0xffc00000003ff00000001ffffff000001ffffff, 0, 132) else none) else (if k ≤ 844359481 then (if k = 844359481 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 902703993 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none)))))

def bucket26 (k : Nat) : Option Hint :=
  if k ≤ 478648122 then (if k ≤ 230148442 then (if k ≤ 83551322 then (if k ≤ 6841114 then (if k = 6841114 then some (0x300a090093fc1fc1f00f820000480002b400001f000, 12, 62) else none) else (if k ≤ 64443258 then (if k = 64443258 then some (0x1ffffff000001ffffff, 0, 179) else none) else (if k = 83551322 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none))) else (if k ≤ 195167482 then (if k ≤ 133102426 then (if k = 133102426 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 18) else none) else (if k = 195167482 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 135) else none)) else (if k ≤ 216494202 then (if k = 216494202 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 27) else none) else (if k = 230148442 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)))) else (if k ≤ 442741146 then (if k ≤ 356807482 then (if k = 356807482 then some (0x3ffc008c880000000000003ffe000631, 0, 8) else none) else (if k ≤ 405089658 then (if k = 405089658 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k = 442741146 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))) else (if k ≤ 452984602 then (if k ≤ 447063578 then (if k = 447063578 then some (0x39b4b336d9b79db379e0780, 7, 11) else none) else (if k = 452984602 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none)) else (if k ≤ 465702042 then (if k = 465702042 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k = 478648122 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none))))) else (if k ≤ 621202778 then (if k ≤ 551877978 then (if k ≤ 501609018 then (if k = 501609018 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k ≤ 541043322 then (if k = 541043322 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 551877978 then some (0x3de0601e007de1ce33f1e7800f00000c7c70e7e3063, 0, 97) else none))) else (if k ≤ 571733882 then (if k ≤ 565634138 then (if k = 565634138 then some (0x39206740cc000000000000390933980680, 7, 35) else none) else (if k = 571733882 then some (0x16bf808430200000000000d6b8c0604804, 2, 155) else none)) else (if k ≤ 606470938 then (if k = 606470938 then some (0x54001fc002b40001f000080000b0000280000018000, 15, 116) else none) else (if k = 621202778 then some (0x3ff5ffffeaf800000000003808b1818298, 3, 86) else none)))) else (if k ≤ 861868026 then (if k ≤ 692300378 then (if k = 692300378 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k ≤ 699122842 then (if k = 699122842 then some (0x300a0b40b6700b41700b8200005a000230000017000, 12, 66) else none) else (if k = 861868026 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 152) else none))) else (if k ≤ 901341210 then (if k ≤ 896205530 then (if k = 896205530 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 87) else none) else (if k = 901341210 then some (0x3188481880618808430246410c41020862040604804, 2, 111) else none)) else (if k ≤ 956396826 then (if k = 956396826 then some (0x318a491890618908630346494c49224862448606846, 1, 19) else none) else (if k = 995390746 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 104) else none)))))

def bucket27 (k : Nat) : Option Hint :=
  if k ≤ 351335931 then (if k ≤ 85534363 then (if k ≤ 64769819 then (if k ≤ 43215835 then (if k = 43215835 then some (0xc21090210102100000007ff31fc1c60d4b8c0000000, 30, 118) else none) else (if k = 64769819 then some (0x3ffc00fff80000000000003ffe000fff, 0, 144) else none)) else (if k ≤ 72696891 then (if k = 72696891 then some (0xc2048660679206740cc018109032499390933980680, 7, 88) else none) else (if k ≤ 73928027 then (if k = 73928027 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 85534363 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 38) else none)))) else (if k ≤ 208408571 then (if k ≤ 107384251 then (if k = 107384251 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k ≤ 200582619 then (if k = 200582619 then some (0x39b4b336d9b79db379e0780, 7, 11) else none) else (if k = 208408571 then some (0x3ff00000003fd800000007fe000000003eec000000, 26, 64) else none))) else (if k ≤ 247206683 then (if k = 247206683 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k ≤ 292613883 then (if k = 292613883 then some (0x7fffffedf76d4beec000000, 26, 175) else none) else (if k = 351335931 then some (0x54001fc002b40001f000080000b0000280000018000, 15, 116) else none))))) else (if k ≤ 690384635 then (if k ≤ 469534075 then (if k ≤ 359033691 then (if k = 359033691 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 121) else none) else (if k = 469534075 then some (0x39b4b336d9b79db379e0780, 7, 11) else none)) else (if k ≤ 596259003 then (if k = 596259003 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k ≤ 676067483 then (if k = 676067483 then some (0x35fc0002400eaf80000000458000010000298, 3, 113) else none) else (if k = 690384635 then some (0x7de1ce33f180000000000c7c70e7e3063, 0, 90) else none)))) else (if k ≤ 785643483 then (if k ≤ 736518619 then (if k = 736518619 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 158) else none) else (if k ≤ 743533659 then (if k = 743533659 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k = 785643483 then some (0xfc1f1fc1fffc1fc1f00f80000000000000000000000, 91, 38) else none))) else (if k ≤ 899120763 then (if k = 899120763 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k ≤ 927600187 then (if k = 927600187 then some (0x3188481880618808430246410c41020862040604804, 2, 111) else none) else (if k = 960858971 then some (0xfc1f1fc1fffc1fc1f00f9f83e0fe07f3fc0fe01f01f, 0, 81) else none)))))

def bucket28 (k : Nat) : Option Hint :=
  if k ≤ 454550140 then (if k ≤ 190359644 then (if k ≤ 144389948 then (if k ≤ 93364700 then (if k = 93364700 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k = 144389948 then some (0x678c6f0e387c7c70e7e3063, 0, 79) else none)) else (if k ≤ 152404796 then (if k = 152404796 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none) else (if k ≤ 169798364 then (if k = 169798364 then some (0xc61208608086080000021842304102408204000000, 26, 109) else none) else (if k = 190359644 then some (0x54001fc002b40001f0000a8000fe0002b400001f000, 12, 119) else none)))) else (if k ≤ 397618044 then (if k ≤ 265814236 then (if k = 265814236 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k ≤ 301721212 then (if k = 301721212 then some (0xfff8f83f814bf80000007ff31fc1c60d4b8c0000000, 30, 169) else none) else (if k = 397618044 then some (0xabff0000004189000000757fe000000842448000000, 27, 37) else none))) else (if k ≤ 436352924 then (if k = 436352924 then some (0x7de1ce33f180000000000c7c70e7e3063, 0, 74) else none) else (if k ≤ 454163804 then (if k = 454163804 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 454550140 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none))))) else (if k ≤ 648787132 then (if k ≤ 602015260 then (if k ≤ 489684284 then (if k = 489684284 then some (0xcc0506c06f9c06c0000039b4b336d9b79db379e0780, 7, 49) else none) else (if k ≤ 594167548 then (if k = 594167548 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 602015260 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 26) else none))) else (if k ≤ 615369052 then (if k = 615369052 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none) else (if k ≤ 628979292 then (if k = 628979292 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none) else (if k = 648787132 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none)))) else (if k ≤ 691168380 then (if k ≤ 663916060 then (if k = 663916060 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k ≤ 666958268 then (if k = 666958268 then some (0x16bf808430200000000000d6b8c0604804, 2, 15) else none) else (if k = 691168380 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 76) else none))) else (if k ≤ 701957788 then (if k = 701957788 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k ≤ 822474652 then (if k = 822474652 then some (0xc2048620638206300c0018109030418380831800280, 7, 55) else none) else (if k = 846610652 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)))))

def bucket29 (k : Nat) : Option Hint :=
  if k ≤ 291657021 then (if k ≤ 108882557 then (if k ≤ 25275453 then (if k ≤ 11482877 then (if k = 11482877 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k = 25275453 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none)) else (if k ≤ 93283517 then (if k = 93283517 then some (0xabff0000004189000000757fe000000842448000000, 27, 37) else none) else (if k ≤ 106819581 then (if k = 106819581 then some (0x3182411810618108230146084c08204860408602042, 1, 112) else none) else (if k = 108882557 then some (0xfc1f1fc1fffc1fc1f00f8a8000fe0002b400001f000, 12, 133) else none)))) else (if k ≤ 166472093 then (if k ≤ 127913277 then (if k = 127913277 then some (0xc2048620638206300c0039b4b336d9b79db379e0780, 7, 45) else none) else (if k = 166472093 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)) else (if k ≤ 198326205 then (if k = 198326205 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 135) else none) else (if k ≤ 210205885 then (if k = 210205885 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 291657021 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 172) else none))))) else (if k ≤ 602645469 then (if k ≤ 412880829 then (if k ≤ 400990589 then (if k = 400990589 then some (0xc014160163801601800c1803e0b007f3800fe01801f, 0, 138) else none) else (if k = 412880829 then some (0x3188481880418800000046410c41020842040000000, 30, 120) else none)) else (if k ≤ 436033373 then (if k = 436033373 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 76) else none) else (if k ≤ 599667389 then (if k = 599667389 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 104) else none) else (if k = 602645469 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none)))) else (if k ≤ 638616733 then (if k ≤ 606568221 then (if k = 606568221 then some (0x31824118107de1ce33f1c6084c08204c7c70e7e3063, 0, 20) else none) else (if k ≤ 614509469 then (if k = 614509469 then some (0xabf8000001eff81ac73675730000000def8c0e6c98c, 2, 168) else none) else (if k = 638616733 then some (0x7fe001fff003ffe000fff, 0, 134) else none))) else (if k ≤ 756818973 then (if k = 756818973 then some (0x3ffffffffff80000000000ffffffffffff, 0, 127) else none) else (if k ≤ 796373821 then (if k = 796373821 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none) else (if k = 971250461 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 76) else none)))))

def bucket30 (k : Nat) : Option Hint :=
  if k ≤ 482477342 then (if k ≤ 290942494 then (if k ≤ 133078558 then (if k ≤ 110270110 then (if k = 110270110 then some (0xc2048620638206300c0018109030418380831800280, 7, 55) else none) else (if k ≤ 112755646 then (if k = 112755646 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k = 133078558 then some (0x3182411810618108230146084c08204860408602042, 1, 112) else none))) else (if k ≤ 178983678 then (if k = 178983678 then some (0x3f8003f8003ffc00fff80730001c60003ffe000fff, 0, 151) else none) else (if k ≤ 192717950 then (if k = 192717950 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 290942494 then some (0x1a8280fe0583b40b001f018, 3, 42) else none)))) else (if k ≤ 431622302 then (if k ≤ 333031230 then (if k = 333031230 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k ≤ 425854334 then (if k = 425854334 then some (0xc61208608086080000021a42304902409204000000, 26, 122) else none) else (if k = 431622302 then some (0x1fc1fc000001f00f80001ffffff000001ffffff, 0, 196) else none))) else (if k ≤ 437677502 then (if k = 437677502 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none) else (if k ≤ 464247774 then (if k = 464247774 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 67) else none) else (if k = 482477342 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 0) else none))))) else (if k ≤ 728629918 then (if k ≤ 664111518 then (if k ≤ 533375326 then (if k = 533375326 then some (0xc4120c40c1c40c600a000800206000014000140000, 18, 61) else none) else (if k ≤ 607713214 then (if k = 607713214 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k = 664111518 then some (0xabf8000001cff812043075730000000dcf8c0860180, 7, 28) else none))) else (if k ≤ 668524126 then (if k = 668524126 then some (0xabff0000014bfd800000757fe000000d4beec000000, 26, 167) else none) else (if k ≤ 722596350 then (if k = 722596350 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none) else (if k = 728629918 then some (0x5400ffc002b4003ff0000a801afe0002b4001d5f000, 12, 131) else none)))) else (if k ≤ 818478046 then (if k ≤ 777313278 then (if k = 777313278 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 6) else none) else (if k ≤ 781873694 then (if k = 781873694 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 4) else none) else (if k = 818478046 then some (0x3ffc00fff80000000000003ffe000fff, 0, 106) else none))) else (if k ≤ 861471326 then (if k = 861471326 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 121) else none) else (if k ≤ 894590206 then (if k = 894590206 then some (0xc6120c60c1c60c600f02184230618341c3061e0000, 17, 23) else none) else (if k = 974884222 then some (0x1eff81ac73600000000000def8c0e6c98c, 2, 2) else none)))))

def bucket31 (k : Nat) : Option Hint :=
  if k ≤ 459574591 then (if k ≤ 197080639 then (if k ≤ 14306175 then (if k ≤ 12121407 then (if k = 12121407 then some (0xc2149621638216318c0c181290b04583808b1818298, 3, 77) else none) else (if k = 14306175 then some (0x3d4361d41c7d41ce32a182800a0e000034000543000, 12, 137) else none)) else (if k ≤ 157505119 then (if k = 157505119 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none) else (if k = 197080639 then some (0xce65a4a6490a6480000039b4b324d12509a24000000, 26, 170) else none))) else (if k ≤ 304465631 then (if k ≤ 235594111 then (if k = 235594111 then some (0x3ffc0000000fff80000001fff000000000fff, 0, 139) else none) else (if k = 304465631 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none)) else (if k ≤ 338890751 then (if k = 338890751 then some (0x3ff003ffc03ffc00fff807fe001fff003ffe000fff, 0, 178) else none) else (if k ≤ 418291935 then (if k = 418291935 then some (0x54a0f80a0020800841006ae01fc1800822000604800, 11, 47) else none) else (if k = 459574591 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none))))) else (if k ≤ 891900703 then (if k ≤ 649344767 then (if k ≤ 647597023 then (if k = 647597023 then some (0x3ff5ffffeaf800000000002b4001d5f000, 12, 140) else none) else (if k = 649344767 then some (0xfff8f83f8061880843027ff31fc1c60862040604804, 2, 21) else none)) else (if k ≤ 727807967 then (if k = 727807967 then some (0xfff8f83f81eff81ac7367ff31fc1c60def8c0e6c98c, 2, 22) else none) else (if k ≤ 865732255 then (if k = 865732255 then some (0x35f0035fc035fc00eaf801280004580008b0000298, 3, 82) else none) else (if k = 891900703 then some (0xfc1f1fc1fffc1fc1f00f980280b00583800b0018018, 3, 78) else none)))) else (if k ≤ 957403071 then (if k ≤ 905674847 then (if k = 905674847 then some (0xfff8f83f8000000000007ff31fc1c60000000000000, 53, 157) else none) else (if k = 957403071 then some (0xfdbfd8000008630300001fedf76000000606846, 1, 60) else none)) else (if k ≤ 971813471 then (if k = 971813471 then some (0xfc1f1801fdec1fc0c00f980280800581800b0008018, 3, 94) else none) else (if k ≤ 984568063 then (if k = 984568063 then some (0x1f83e0fe07f3fc0fe01f01f, 0, 25) else none) else (if k = 992338975 then some (0x38349130d98781b318a0780, 7, 71) else none)))))

def advice (k : Nat) : Option Hint :=
  match k % 32 with
  | 0 => bucket0 k
  | 1 => bucket1 k
  | 2 => bucket2 k
  | 3 => bucket3 k
  | 4 => bucket4 k
  | 5 => bucket5 k
  | 6 => bucket6 k
  | 7 => bucket7 k
  | 8 => bucket8 k
  | 9 => bucket9 k
  | 10 => bucket10 k
  | 11 => bucket11 k
  | 12 => bucket12 k
  | 13 => bucket13 k
  | 14 => bucket14 k
  | 15 => bucket15 k
  | 16 => bucket16 k
  | 17 => bucket17 k
  | 18 => bucket18 k
  | 19 => bucket19 k
  | 20 => bucket20 k
  | 21 => bucket21 k
  | 22 => bucket22 k
  | 23 => bucket23 k
  | 24 => bucket24 k
  | 25 => bucket25 k
  | 26 => bucket26 k
  | 27 => bucket27 k
  | 28 => bucket28 k
  | 29 => bucket29 k
  | 30 => bucket30 k
  | _ => bucket31 k

end Check515

namespace Check515
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet0_ok : goodClaim checkedSet0 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet1_ok : goodClaim checkedSet1 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet2_ok : goodClaim checkedSet2 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet3_ok : goodClaim checkedSet3 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet4_ok : goodClaim checkedSet4 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet5_ok : goodClaim checkedSet5 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet6_ok : goodClaim checkedSet6 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet7_ok : goodClaim checkedSet7 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet8_ok : goodClaim checkedSet8 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet9_ok : goodClaim checkedSet9 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet10_ok : goodClaim checkedSet10 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet11_ok : goodClaim checkedSet11 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet12_ok : goodClaim checkedSet12 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet13_ok : goodClaim checkedSet13 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet14_ok : goodClaim checkedSet14 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet15_ok : goodClaim checkedSet15 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet16_ok : goodClaim checkedSet16 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet17_ok : goodClaim checkedSet17 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet18_ok : goodClaim checkedSet18 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet19_ok : goodClaim checkedSet19 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet20_ok : goodClaim checkedSet20 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet21_ok : goodClaim checkedSet21 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet22_ok : goodClaim checkedSet22 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet23_ok : goodClaim checkedSet23 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet24_ok : goodClaim checkedSet24 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet25_ok : goodClaim checkedSet25 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet26_ok : goodClaim checkedSet26 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet27_ok : goodClaim checkedSet27 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet28_ok : goodClaim checkedSet28 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet29_ok : goodClaim checkedSet29 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet30_ok : goodClaim checkedSet30 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet31_ok : goodClaim checkedSet31 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet32_ok : goodClaim checkedSet32 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet33_ok : goodClaim checkedSet33 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet34_ok : goodClaim checkedSet34 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet35_ok : goodClaim checkedSet35 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet36_ok : goodClaim checkedSet36 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet37_ok : goodClaim checkedSet37 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet38_ok : goodClaim checkedSet38 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet39_ok : goodClaim checkedSet39 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet40_ok : goodClaim checkedSet40 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet41_ok : goodClaim checkedSet41 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet42_ok : goodClaim checkedSet42 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet43_ok : goodClaim checkedSet43 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet44_ok : goodClaim checkedSet44 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet45_ok : goodClaim checkedSet45 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet46_ok : goodClaim checkedSet46 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet47_ok : goodClaim checkedSet47 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet48_ok : goodClaim checkedSet48 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet49_ok : goodClaim checkedSet49 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet50_ok : goodClaim checkedSet50 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet51_ok : goodClaim checkedSet51 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet52_ok : goodClaim checkedSet52 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet53_ok : goodClaim checkedSet53 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet54_ok : goodClaim checkedSet54 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet55_ok : goodClaim checkedSet55 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet56_ok : goodClaim checkedSet56 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet57_ok : goodClaim checkedSet57 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet58_ok : goodClaim checkedSet58 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet59_ok : goodClaim checkedSet59 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet60_ok : goodClaim checkedSet60 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet61_ok : goodClaim checkedSet61 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet62_ok : goodClaim checkedSet62 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet63_ok : goodClaim checkedSet63 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet64_ok : goodClaim checkedSet64 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet65_ok : goodClaim checkedSet65 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet66_ok : goodClaim checkedSet66 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet67_ok : goodClaim checkedSet67 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet68_ok : goodClaim checkedSet68 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet69_ok : goodClaim checkedSet69 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet70_ok : goodClaim checkedSet70 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet71_ok : goodClaim checkedSet71 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet72_ok : goodClaim checkedSet72 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet73_ok : goodClaim checkedSet73 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet74_ok : goodClaim checkedSet74 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet75_ok : goodClaim checkedSet75 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet76_ok : goodClaim checkedSet76 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet77_ok : goodClaim checkedSet77 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet78_ok : goodClaim checkedSet78 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet79_ok : goodClaim checkedSet79 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet80_ok : goodClaim checkedSet80 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet81_ok : goodClaim checkedSet81 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet82_ok : goodClaim checkedSet82 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet83_ok : goodClaim checkedSet83 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet84_ok : goodClaim checkedSet84 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet85_ok : goodClaim checkedSet85 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet86_ok : goodClaim checkedSet86 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet87_ok : goodClaim checkedSet87 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet88_ok : goodClaim checkedSet88 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet89_ok : goodClaim checkedSet89 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet90_ok : goodClaim checkedSet90 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet91_ok : goodClaim checkedSet91 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet92_ok : goodClaim checkedSet92 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet93_ok : goodClaim checkedSet93 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet94_ok : goodClaim checkedSet94 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet95_ok : goodClaim checkedSet95 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet96_ok : goodClaim checkedSet96 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet97_ok : goodClaim checkedSet97 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet98_ok : goodClaim checkedSet98 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet99_ok : goodClaim checkedSet99 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet100_ok : goodClaim checkedSet100 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet101_ok : goodClaim checkedSet101 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet102_ok : goodClaim checkedSet102 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet103_ok : goodClaim checkedSet103 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet104_ok : goodClaim checkedSet104 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet105_ok : goodClaim checkedSet105 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet106_ok : goodClaim checkedSet106 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet107_ok : goodClaim checkedSet107 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet108_ok : goodClaim checkedSet108 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet109_ok : goodClaim checkedSet109 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet110_ok : goodClaim checkedSet110 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet111_ok : goodClaim checkedSet111 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet112_ok : goodClaim checkedSet112 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet113_ok : goodClaim checkedSet113 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet114_ok : goodClaim checkedSet114 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet115_ok : goodClaim checkedSet115 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet116_ok : goodClaim checkedSet116 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet117_ok : goodClaim checkedSet117 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet118_ok : goodClaim checkedSet118 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet119_ok : goodClaim checkedSet119 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet120_ok : goodClaim checkedSet120 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet121_ok : goodClaim checkedSet121 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet122_ok : goodClaim checkedSet122 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet123_ok : goodClaim checkedSet123 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet124_ok : goodClaim checkedSet124 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet125_ok : goodClaim checkedSet125 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet126_ok : goodClaim checkedSet126 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet127_ok : goodClaim checkedSet127 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet128_ok : goodClaim checkedSet128 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet129_ok : goodClaim checkedSet129 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet130_ok : goodClaim checkedSet130 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet131_ok : goodClaim checkedSet131 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet132_ok : goodClaim checkedSet132 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet133_ok : goodClaim checkedSet133 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet134_ok : goodClaim checkedSet134 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet135_ok : goodClaim checkedSet135 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet136_ok : goodClaim checkedSet136 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet137_ok : goodClaim checkedSet137 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet138_ok : goodClaim checkedSet138 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet139_ok : goodClaim checkedSet139 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet140_ok : goodClaim checkedSet140 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet141_ok : goodClaim checkedSet141 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet142_ok : goodClaim checkedSet142 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet143_ok : goodClaim checkedSet143 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet144_ok : goodClaim checkedSet144 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet145_ok : goodClaim checkedSet145 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet146_ok : goodClaim checkedSet146 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet147_ok : goodClaim checkedSet147 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet148_ok : goodClaim checkedSet148 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet149_ok : goodClaim checkedSet149 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet150_ok : goodClaim checkedSet150 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet151_ok : goodClaim checkedSet151 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet152_ok : goodClaim checkedSet152 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet153_ok : goodClaim checkedSet153 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet154_ok : goodClaim checkedSet154 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet155_ok : goodClaim checkedSet155 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet156_ok : goodClaim checkedSet156 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet157_ok : goodClaim checkedSet157 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet158_ok : goodClaim checkedSet158 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet159_ok : goodClaim checkedSet159 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet160_ok : goodClaim checkedSet160 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet161_ok : goodClaim checkedSet161 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet162_ok : goodClaim checkedSet162 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet163_ok : goodClaim checkedSet163 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet164_ok : goodClaim checkedSet164 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet165_ok : goodClaim checkedSet165 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet166_ok : goodClaim checkedSet166 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet167_ok : goodClaim checkedSet167 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet168_ok : goodClaim checkedSet168 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet169_ok : goodClaim checkedSet169 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet170_ok : goodClaim checkedSet170 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet171_ok : goodClaim checkedSet171 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet172_ok : goodClaim checkedSet172 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet173_ok : goodClaim checkedSet173 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet174_ok : goodClaim checkedSet174 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet175_ok : goodClaim checkedSet175 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet176_ok : goodClaim checkedSet176 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet177_ok : goodClaim checkedSet177 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet178_ok : goodClaim checkedSet178 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet179_ok : goodClaim checkedSet179 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet180_ok : goodClaim checkedSet180 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet181_ok : goodClaim checkedSet181 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet182_ok : goodClaim checkedSet182 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet183_ok : goodClaim checkedSet183 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet184_ok : goodClaim checkedSet184 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet185_ok : goodClaim checkedSet185 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet186_ok : goodClaim checkedSet186 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet187_ok : goodClaim checkedSet187 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet188_ok : goodClaim checkedSet188 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet189_ok : goodClaim checkedSet189 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet190_ok : goodClaim checkedSet190 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet191_ok : goodClaim checkedSet191 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet192_ok : goodClaim checkedSet192 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet193_ok : goodClaim checkedSet193 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet194_ok : goodClaim checkedSet194 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet195_ok : goodClaim checkedSet195 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet196_ok : goodClaim checkedSet196 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet197_ok : goodClaim checkedSet197 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet198_ok : goodClaim checkedSet198 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet199_ok : goodClaim checkedSet199 = true := by decide +kernel

end Check515

namespace Check515
def rootF (i : Nat) : Bool :=
  ((pairs inputs)[i]?).any (fun (a,b,rest) => dispatch 3 (front claims advice 2 9) a b rest)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier0 : rootF 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier1 : rootF 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier2 : rootF 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier3 : rootF 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier4 : rootF 4 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier5 : rootF 5 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier6 : rootF 6 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier7 : rootF 7 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier8 : rootF 8 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier9 : rootF 9 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier10 : rootF 10 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier11 : rootF 11 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier12 : rootF 12 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier13 : rootF 13 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier14 : rootF 14 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier15 : rootF 15 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier16 : rootF 16 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier17 : rootF 17 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier18 : rootF 18 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier19 : rootF 19 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier20 : rootF 20 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier21 : rootF 21 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier22 : rootF 22 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier23 : rootF 23 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier24 : rootF 24 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier25 : rootF 25 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier26 : rootF 26 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier27 : rootF 27 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem all_front : front claims advice 3 10 3 inputs = false := by
  have hlen : (pairs inputs).length = 28 := by decide
  have allRoots : ∀ i : Fin 28, rootF i.val = false := by
    intro i
    fin_cases i
    · exact frontier0
    · exact frontier1
    · exact frontier2
    · exact frontier3
    · exact frontier4
    · exact frontier5
    · exact frontier6
    · exact frontier7
    · exact frontier8
    · exact frontier9
    · exact frontier10
    · exact frontier11
    · exact frontier12
    · exact frontier13
    · exact frontier14
    · exact frontier15
    · exact frontier16
    · exact frontier17
    · exact frontier18
    · exact frontier19
    · exact frontier20
    · exact frontier21
    · exact frontier22
    · exact frontier23
    · exact frontier24
    · exact frontier25
    · exact frontier26
    · exact frontier27
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [front, Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with stop | step
  · exact (by decide : (inputs == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := allRoots (Fin.cast hlen i)
    simp only [Fin.val_cast, rootF, List.getElem?_eq_getElem i.isLt, Option.any_some] at no
    rw [← hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)

end Check515

namespace Check515
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem all_claims : claims.all goodClaim = true := by
  simp only [claims, List.all_cons, List.all_nil, Bool.true_and,
    checkedSet0_ok, checkedSet1_ok, checkedSet2_ok, checkedSet3_ok, checkedSet4_ok, checkedSet5_ok, checkedSet6_ok, checkedSet7_ok,
    checkedSet8_ok, checkedSet9_ok, checkedSet10_ok, checkedSet11_ok, checkedSet12_ok, checkedSet13_ok, checkedSet14_ok, checkedSet15_ok,
    checkedSet16_ok, checkedSet17_ok, checkedSet18_ok, checkedSet19_ok, checkedSet20_ok, checkedSet21_ok, checkedSet22_ok, checkedSet23_ok,
    checkedSet24_ok, checkedSet25_ok, checkedSet26_ok, checkedSet27_ok, checkedSet28_ok, checkedSet29_ok, checkedSet30_ok, checkedSet31_ok,
    checkedSet32_ok, checkedSet33_ok, checkedSet34_ok, checkedSet35_ok, checkedSet36_ok, checkedSet37_ok, checkedSet38_ok, checkedSet39_ok,
    checkedSet40_ok, checkedSet41_ok, checkedSet42_ok, checkedSet43_ok, checkedSet44_ok, checkedSet45_ok, checkedSet46_ok, checkedSet47_ok,
    checkedSet48_ok, checkedSet49_ok, checkedSet50_ok, checkedSet51_ok, checkedSet52_ok, checkedSet53_ok, checkedSet54_ok, checkedSet55_ok,
    checkedSet56_ok, checkedSet57_ok, checkedSet58_ok, checkedSet59_ok, checkedSet60_ok, checkedSet61_ok, checkedSet62_ok, checkedSet63_ok,
    checkedSet64_ok, checkedSet65_ok, checkedSet66_ok, checkedSet67_ok, checkedSet68_ok, checkedSet69_ok, checkedSet70_ok, checkedSet71_ok,
    checkedSet72_ok, checkedSet73_ok, checkedSet74_ok, checkedSet75_ok, checkedSet76_ok, checkedSet77_ok, checkedSet78_ok, checkedSet79_ok,
    checkedSet80_ok, checkedSet81_ok, checkedSet82_ok, checkedSet83_ok, checkedSet84_ok, checkedSet85_ok, checkedSet86_ok, checkedSet87_ok,
    checkedSet88_ok, checkedSet89_ok, checkedSet90_ok, checkedSet91_ok, checkedSet92_ok, checkedSet93_ok, checkedSet94_ok, checkedSet95_ok,
    checkedSet96_ok, checkedSet97_ok, checkedSet98_ok, checkedSet99_ok, checkedSet100_ok, checkedSet101_ok, checkedSet102_ok, checkedSet103_ok,
    checkedSet104_ok, checkedSet105_ok, checkedSet106_ok, checkedSet107_ok, checkedSet108_ok, checkedSet109_ok, checkedSet110_ok, checkedSet111_ok,
    checkedSet112_ok, checkedSet113_ok, checkedSet114_ok, checkedSet115_ok, checkedSet116_ok, checkedSet117_ok, checkedSet118_ok, checkedSet119_ok,
    checkedSet120_ok, checkedSet121_ok, checkedSet122_ok, checkedSet123_ok, checkedSet124_ok, checkedSet125_ok, checkedSet126_ok, checkedSet127_ok,
    checkedSet128_ok, checkedSet129_ok, checkedSet130_ok, checkedSet131_ok, checkedSet132_ok, checkedSet133_ok, checkedSet134_ok, checkedSet135_ok,
    checkedSet136_ok, checkedSet137_ok, checkedSet138_ok, checkedSet139_ok, checkedSet140_ok, checkedSet141_ok, checkedSet142_ok, checkedSet143_ok,
    checkedSet144_ok, checkedSet145_ok, checkedSet146_ok, checkedSet147_ok, checkedSet148_ok, checkedSet149_ok, checkedSet150_ok, checkedSet151_ok,
    checkedSet152_ok, checkedSet153_ok, checkedSet154_ok, checkedSet155_ok, checkedSet156_ok, checkedSet157_ok, checkedSet158_ok, checkedSet159_ok,
    checkedSet160_ok, checkedSet161_ok, checkedSet162_ok, checkedSet163_ok, checkedSet164_ok, checkedSet165_ok, checkedSet166_ok, checkedSet167_ok,
    checkedSet168_ok, checkedSet169_ok, checkedSet170_ok, checkedSet171_ok, checkedSet172_ok, checkedSet173_ok, checkedSet174_ok, checkedSet175_ok,
    checkedSet176_ok, checkedSet177_ok, checkedSet178_ok, checkedSet179_ok, checkedSet180_ok, checkedSet181_ok, checkedSet182_ok, checkedSet183_ok,
    checkedSet184_ok, checkedSet185_ok, checkedSet186_ok, checkedSet187_ok, checkedSet188_ok, checkedSet189_ok, checkedSet190_ok, checkedSet191_ok,
    checkedSet192_ok, checkedSet193_ok, checkedSet194_ok, checkedSet195_ok, checkedSet196_ok, checkedSet197_ok, checkedSet198_ok, checkedSet199_ok]

end Check515

theorem PEqualNP.Outside.L_meta_515 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 3 && x 7)) s → 11 ≤ s := Check515.lower_of_front _ _ _ Check515.all_claims Check515.all_front
