import Mathlib
import PEqualNP.Defs


section

namespace PEqualNP.Library.SearchHelpers.KSat.Hard

open PEqualNP.Search

def X (i : ℕ) : ℕ := 2 * i + 1

def Y (m : ℕ) : ℕ := 2 ^ (m + 1)

def chain (m : ℕ) : Clause → CNF
  | [] => [[(Y m, false)], [(Y (m + 1), true)]]
  | l :: c => [(Y m, false), (X l.1, l.2), (Y (m + 1), true)] :: chain (m + 1) c

def splitFrom (m : ℕ) : CNF → CNF
  | [] => []
  | c :: φ => chain m c ++ splitFrom (m + c.length + 1) φ

def split (φ : CNF) : CNF := [(Y 0, true)] :: splitFrom 0 φ

theorem isKCNF_chain (m : ℕ) (c : Clause) : IsKCNF 3 (chain m c) := by
  induction c generalizing m with
  | nil =>
    intro d hd
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp
  | cons l c ih =>
    intro d hd
    simp only [chain, List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp
    · exact ih _ d hd

theorem isKCNF_splitFrom (m : ℕ) (φ : CNF) : IsKCNF 3 (splitFrom m φ) := by
  induction φ generalizing m with
  | nil => intro d hd; simp [splitFrom] at hd
  | cons c φ ih =>
    intro d hd
    simp only [splitFrom, List.mem_append] at hd
    rcases hd with hd | hd
    · exact isKCNF_chain _ _ d hd
    · exact ih _ d hd

theorem isKCNF_split (φ : CNF) : IsKCNF 3 (split φ) := by
  intro d hd
  simp only [split, List.mem_cons] at hd
  rcases hd with rfl | hd
  · simp
  · exact isKCNF_splitFrom _ _ d hd

theorem eval_append (σ : Assignment) (φ ψ : CNF) :
    CNF.eval σ (φ ++ ψ) = (CNF.eval σ φ && CNF.eval σ ψ) := by
  simp [CNF.eval]

theorem eval_cons (σ : Assignment) (c : Clause) (φ : CNF) :
    CNF.eval σ (c :: φ) = (Clause.eval σ c && CNF.eval σ φ) := by
  simp [CNF.eval]

theorem ceval_cons (σ : Assignment) (l : Literal) (c : Clause) :
    Clause.eval σ (l :: c) = (Literal.eval σ l || Clause.eval σ c) := by
  simp [Clause.eval]

theorem chain_end (τ : Assignment) (c : Clause) : ∀ m : ℕ,
    CNF.eval τ (chain m c) = true → τ (Y (m + c.length + 1)) = true := by
  induction c with
  | nil =>
    intro m h
    simp only [chain, CNF.eval, Clause.eval, Literal.eval, List.all_cons, List.any_cons,
      List.any_nil, List.all_nil, Bool.or_false, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq] at h
    simpa using h.2
  | cons l c ih =>
    intro m h
    rw [chain, eval_cons, Bool.and_eq_true] at h
    rw [show m + (l :: c).length + 1 = (m + 1) + c.length + 1 by
      simp only [List.length_cons]; omega]
    exact ih (m + 1) h.2

theorem chain_sound (τ : Assignment) (c : Clause) : ∀ m : ℕ,
    CNF.eval τ (chain m c) = true → τ (Y m) = true →
      Clause.eval (fun i => τ (X i)) c = true := by
  induction c with
  | nil =>
    intro m h hm
    simp [chain, CNF.eval, Clause.eval, Literal.eval, hm] at h
  | cons l c ih =>
    intro m h hm
    rw [chain, eval_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [ceval_cons]
    by_cases hl : τ (X l.1) = l.2
    · simp [Literal.eval, hl]
    · have hy : τ (Y (m + 1)) = true := by
        simpa [Clause.eval, Literal.eval, hm, hl] using h1
      simp [ih (m + 1) h2 hy]

theorem splitFrom_sound (τ : Assignment) (φ : CNF) : ∀ m : ℕ,
    CNF.eval τ (splitFrom m φ) = true → τ (Y m) = true →
      CNF.eval (fun i => τ (X i)) φ = true := by
  induction φ with
  | nil => intro m _ _; rfl
  | cons c φ ih =>
    intro m h hm
    rw [splitFrom, eval_append, Bool.and_eq_true] at h
    rw [eval_cons, chain_sound τ c m h.1 hm, ih _ h.2 (chain_end τ c m h.1)]
    rfl

def mk (σ : Assignment) (t : ℕ → Bool) : Assignment :=
  fun v => if v % 2 = 1 then σ (v / 2) else t (Nat.log 2 v - 1)

theorem mk_X (σ : Assignment) (t : ℕ → Bool) (i : ℕ) : mk σ t (X i) = σ i := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [mk, X, h1, h2]

theorem mk_Y (σ : Assignment) (t : ℕ → Bool) (m : ℕ) : mk σ t (Y m) = t m := by
  have h1 : 2 ^ (m + 1) % 2 = 0 := by rw [pow_succ]; exact Nat.mul_mod_left _ _
  have h2 : Nat.log 2 (2 ^ (m + 1)) = m + 1 := Nat.log_pow (by norm_num) _
  simp [mk, Y, h1, h2]

def cv (σ : Assignment) : Clause → ℕ → Bool
  | _, 0 => true
  | [], _ + 1 => false
  | l :: c, j + 1 => !Literal.eval σ l && cv σ c j

def tv (σ : Assignment) : CNF → ℕ → Bool
  | [], _ => true
  | c :: φ, j => if j ≤ c.length then cv σ c j else tv σ φ (j - c.length - 1)

theorem cv_zero (σ : Assignment) (c : Clause) : cv σ c 0 = true := by
  cases c <;> rfl

theorem tv_zero (σ : Assignment) (φ : CNF) : tv σ φ 0 = true := by
  cases φ with
  | nil => rfl
  | cons c φ => simp [tv, cv_zero]

theorem chain_complete (σ : Assignment) (c : Clause) : ∀ (m : ℕ) (t : ℕ → Bool) (a : Bool),
    (∀ j ≤ c.length, t (m + j) = (a && cv σ c j)) → t (m + c.length + 1) = true →
    (a = true → Clause.eval σ c = true) → CNF.eval (mk σ t) (chain m c) = true := by
  induction c with
  | nil =>
    intro m t a ht hend ha
    have h0 := ht 0 (le_refl _)
    have ha' : a = false := by
      cases a
      · rfl
      · simpa [Clause.eval] using ha rfl
    rw [ha'] at h0
    simp only [Nat.add_zero, Bool.false_and] at h0
    simp only [List.length_nil, Nat.add_zero] at hend
    simp [chain, CNF.eval, Clause.eval, Literal.eval, mk_Y, h0, hend]
  | cons l c ih =>
    intro m t a ht hend ha
    have h0 := ht 0 (Nat.zero_le _)
    simp only [Nat.add_zero, cv, Bool.and_true] at h0
    have h1 := ht 1 (by simp)
    simp only [cv, cv_zero, Bool.and_true] at h1
    rw [chain, eval_cons, Bool.and_eq_true]
    constructor
    · simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval, mk_Y,
        mk_X, h0, h1]
      cases a <;> cases hl : (σ l.1 == l.2) <;> simp
    · refine ih (m + 1) t (a && !Literal.eval σ l) ?_ ?_ ?_
      · intro j hj
        have := ht (j + 1) (by simpa using hj)
        rw [show m + 1 + j = m + (j + 1) by omega, this, cv, Bool.and_assoc]
      · rw [show m + 1 + c.length + 1 = m + (l :: c).length + 1 by
          simp only [List.length_cons]; omega]
        exact hend
      · intro h
        rw [Bool.and_eq_true] at h
        have := ha h.1
        rw [ceval_cons] at this
        cases hl : Literal.eval σ l
        · simpa [hl] using this
        · simp [hl] at h

theorem splitFrom_complete (σ : Assignment) (φ : CNF) : ∀ (m : ℕ) (t : ℕ → Bool),
    (∀ j, t (m + j) = tv σ φ j) → CNF.eval σ φ = true →
      CNF.eval (mk σ t) (splitFrom m φ) = true := by
  induction φ with
  | nil => intro m t _ _; rfl
  | cons c φ ih =>
    intro m t ht h
    rw [eval_cons, Bool.and_eq_true] at h
    rw [splitFrom, eval_append, Bool.and_eq_true]
    constructor
    · refine chain_complete σ c m t true ?_ ?_ (fun _ => h.1)
      · intro j hj
        rw [ht j, tv]
        simp only [hj, ↓reduceIte, Bool.true_and]
      · have e : ¬ c.length + 1 ≤ c.length := by omega
        rw [show m + c.length + 1 = m + (c.length + 1) by omega, ht, tv]
        simp only [e, ↓reduceIte]
        rw [show c.length + 1 - c.length - 1 = 0 by omega, tv_zero]
    · refine ih _ t ?_ h.2
      intro j
      have e : ¬ c.length + 1 + j ≤ c.length := by omega
      rw [show m + c.length + 1 + j = m + (c.length + 1 + j) by omega, ht, tv]
      simp only [e, ↓reduceIte]
      rw [show c.length + 1 + j - c.length - 1 = j by omega]

theorem satisfiable_split (φ : CNF) : Satisfiable (split φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨τ, h⟩
    rw [split, eval_cons, Bool.and_eq_true] at h
    refine ⟨fun i => τ (X i), splitFrom_sound τ φ 0 h.2 ?_⟩
    simpa [Clause.eval, Literal.eval] using h.1
  · rintro ⟨σ, h⟩
    refine ⟨mk σ (tv σ φ), ?_⟩
    rw [split, eval_cons, Bool.and_eq_true]
    refine ⟨?_, splitFrom_complete σ φ 0 _ (fun j => by rw [Nat.zero_add]) h⟩
    simp [Clause.eval, Literal.eval, mk_Y, tv_zero]

end PEqualNP.Library.SearchHelpers.KSat.Hard

end

section

namespace PEqualNP.Library.Universal

inductive Instr
  | push (k : ℕ) (tbl : List ℕ) (next : ℕ)
  | pop (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | peek (k : ℕ) (tbl : List ℕ) (w : ℕ) (next : ℕ)
  | load (tbl : List ℕ) (next : ℕ)
  | branch (tbl : List ℕ) (next₁ next₂ : ℕ)
  | goto (tbl : List ℕ)
  | halt
  deriving DecidableEq, Repr

structure Cfg where
  pc : Option ℕ
  state : ℕ
  stk : List (List ℕ)
  deriving DecidableEq, Repr

def topIndex (st : List ℕ) : ℕ :=
  match st with
  | [] => 0
  | s :: _ => s + 1

def exec (i : Instr) (v : ℕ) (S : List (List ℕ)) : Cfg :=
  match i with
  | .push k tbl next => ⟨some next, v, S.set k (tbl.getD v 0 :: S.getD k [])⟩
  | .pop k tbl w next =>
    ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S.set k (S.getD k []).tail⟩
  | .peek k tbl w next => ⟨some next, tbl.getD (v * w + topIndex (S.getD k [])) 0, S⟩
  | .load tbl next => ⟨some next, tbl.getD v 0, S⟩
  | .branch tbl next₁ next₂ => ⟨some (if tbl.getD v 0 ≠ 0 then next₁ else next₂), v, S⟩
  | .goto tbl => ⟨some (tbl.getD v 0), v, S⟩
  | .halt => ⟨none, v, S⟩

def step (P : List Instr) (c : Cfg) : Cfg :=
  match c.pc with
  | none => c
  | some n =>
    match P[n]? with
    | none => ⟨none, c.state, c.stk⟩
    | some i => exec i c.state c.stk

structure Code where
  prog : List Instr
  nstk : ℕ
  pc₀ : ℕ
  state₀ : ℕ
  kin : ℕ
  kout : ℕ
  deriving DecidableEq, Repr

def Code.init (c : Code) (input : List ℕ) : Cfg :=
  ⟨some c.pc₀, c.state₀, (List.replicate c.nstk []).set c.kin input⟩

def Code.run (c : Code) (input : List ℕ) (t : ℕ) : Cfg :=
  (step c.prog)^[t] (c.init input)

def Code.outputsWithin (c : Code) (input : List ℕ) (t : ℕ) (out : List ℕ) : Prop :=
  (c.run input t).pc = none ∧ (c.run input t).stk.getD c.kout [] = out

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Universal

def un (n : ℕ) : List Bool := List.replicate n true

def pairB (a b : List Bool) : List Bool := un a.length ++ false :: (a ++ b)

def unpairB (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem unpairB_pairB (a b : List Bool) : unpairB (pairB a b) = (a, b) := by
  have h1 : (pairB a b).takeWhile id = un a.length := by
    simp [pairB, un]
  have h2 : (pairB a b).dropWhile id = false :: (a ++ b) := by
    simp [pairB, un]
  simp [unpairB, h1, h2, un]

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Universal

theorem un_succ (n : ℕ) : un (n + 1) = true :: un n := rfl

@[simp] theorem un_zero : un 0 = [] := rfl

@[simp] theorem un_length (n : ℕ) : (un n).length = n := by simp [un]

theorem un_inj {a b : ℕ} (h : un a = un b) : a = b := by
  have := congrArg List.length h
  simpa using this

def encN (n : ℕ) : List Bool := un (n + 1) ++ [false]

def encNs (l : List ℕ) : List Bool := l.flatMap encN

def encL (l : List ℕ) : List Bool := encNs l ++ [false]

def encLL (S : List (List ℕ)) : List Bool := S.flatMap encL

@[simp] theorem encNs_nil : encNs [] = [] := rfl

theorem encNs_cons (a : ℕ) (l : List ℕ) : encNs (a :: l) = encN a ++ encNs l := rfl

theorem encNs_append (l m : List ℕ) : encNs (l ++ m) = encNs l ++ encNs m := by
  simp [encNs]

@[simp] theorem encLL_nil : encLL [] = [] := rfl

theorem encLL_cons (a : List ℕ) (S : List (List ℕ)) :
    encLL (a :: S) = encNs a ++ false :: encLL S := by
  simp [encLL, encL]

theorem encLL_append (S T : List (List ℕ)) : encLL (S ++ T) = encLL S ++ encLL T := by
  simp [encLL]

def instrNs : Instr → List ℕ
  | .push k tbl next => [0, k, 0, next, 0] ++ tbl
  | .pop k tbl w next => [1, k, w, next, 0] ++ tbl
  | .peek k tbl w next => [2, k, w, next, 0] ++ tbl
  | .load tbl next => [3, 0, 0, next, 0] ++ tbl
  | .branch tbl next₁ next₂ => [4, 0, 0, next₁, next₂] ++ tbl
  | .goto tbl => [5, 0, 0, 0, 0] ++ tbl
  | .halt => [6, 0, 0, 0, 0]

def encP (P : List Instr) : List Bool := encLL (P.map instrNs)

def encPc : Option ℕ → List Bool
  | none => []
  | some n => un (n + 1)

def encCfg (P : List Instr) (c : Cfg) : List Bool :=
  pairB (encP P) (pairB (encPc c.pc) (pairB (un c.state) (encLL c.stk)))

def encCode (c : Code) : List Bool :=
  pairB (encP c.prog) (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout])

def hd (s : List Bool) : List Bool := s.takeWhile id

def dropN (s : List Bool) : List Bool := (s.dropWhile id).tail

def sel (f a b : List Bool) : List Bool := if f = [] then a else b

def mulU (u v : List Bool) : List Bool := un (u.length * v.length)

def takeLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => true :: takeLA true r
  | true, false :: r => false :: takeLA false r
  | false, false :: _ => []

def dropLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => dropLA true r
  | true, false :: r => dropLA false r
  | false, false :: r => r

def headLA : Bool → List Bool → List Bool
  | _, [] => []
  | _, true :: r => true :: headLA true r
  | true, false :: r => false :: headLA false r
  | false, false :: _ => [false]

def takeL (s : List Bool) : List Bool := takeLA false s

def dropL (s : List Bool) : List Bool := dropLA false s

def headL (s : List Bool) : List Bool := headLA false s

def move (y : List Bool) : List Bool :=
  pairB (dropL (unpairB y).1) ((unpairB y).2 ++ headL (unpairB y).1)

def popT : List Bool → List Bool
  | true :: r => dropN (true :: r)
  | s => s

def spread (s : List Bool) : List Bool := s.flatMap fun b => if b then [true, false] else [false]

def bump (s : List Bool) : List Bool := s.flatMap fun b => if b then [true] else [true, false]

def blank (s : List Bool) : List Bool := s.map fun _ => false

@[simp] theorem sel_nil (a b : List Bool) : sel [] a b = a := rfl

@[simp] theorem sel_cons (x : Bool) (f a b : List Bool) : sel (x :: f) a b = b := by
  simp [sel]

theorem sel_append_left (f p a b : List Bool) : sel f (p ++ a) (p ++ b) = p ++ sel f a b := by
  unfold sel; split <;> rfl

@[simp] theorem hd_nil : hd [] = [] := rfl

@[simp] theorem dropN_nil : dropN [] = [] := rfl

theorem hd_un (n : ℕ) (r : List Bool) : hd (un n ++ false :: r) = un n := by
  induction n with
  | zero => simp [hd]
  | succ n ih => simpa [hd, un_succ] using ih

theorem dropN_un (n : ℕ) (r : List Bool) : dropN (un n ++ false :: r) = r := by
  induction n with
  | zero => simp [dropN]
  | succ n ih => simpa [dropN, un_succ] using ih

@[simp] theorem hd_encNs_cons (a : ℕ) (l : List ℕ) : hd (encNs (a :: l)) = un (a + 1) := by
  rw [encNs_cons, encN, List.append_assoc]; exact hd_un _ _

@[simp] theorem dropN_encNs_cons (a : ℕ) (l : List ℕ) : dropN (encNs (a :: l)) = encNs l := by
  rw [encNs_cons, encN, List.append_assoc]; exact dropN_un _ _

theorem dropN_iter_encNs (i : ℕ) (l : List ℕ) : dropN^[i] (encNs l) = encNs (l.drop i) := by
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simpa using ih []
    | cons a l => simpa using ih l

theorem lookup_spec (i : ℕ) (l : List ℕ) :
    (hd (dropN^[i] (encNs l))).tail = un (l.getD i 0) := by
  rw [dropN_iter_encNs]
  induction i generalizing l with
  | zero => cases l <;> simp [un_succ]
  | succ i ih =>
    cases l with
    | nil => simp
    | cons a l => simpa using ih l

theorem takeLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    takeLA b (un n ++ true :: false :: r) = un n ++ true :: false :: takeLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [takeLA]
  | succ n ih => cases b <;> simp [un_succ, takeLA, ih]

theorem dropLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    dropLA b (un n ++ true :: false :: r) = dropLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [dropLA]
  | succ n ih => cases b <;> simp [un_succ, dropLA, ih]

theorem headLA_un (n : ℕ) (b : Bool) (r : List Bool) :
    headLA b (un n ++ true :: false :: r) = un n ++ true :: false :: headLA false r := by
  induction n generalizing b with
  | zero => cases b <;> simp [headLA]
  | succ n ih => cases b <;> simp [un_succ, headLA, ih]

theorem encN_eq (a : ℕ) : encN a = un a ++ [true, false] := by
  induction a with
  | zero => rfl
  | succ a ih => rw [encN, un_succ, List.cons_append, ← encN, ih, un_succ]; rfl

theorem takeL_encNs (l : List ℕ) (r : List Bool) : takeL (encNs l ++ false :: r) = encNs l := by
  induction l with
  | nil => simp [takeL, takeLA]
  | cons a l ih =>
    rw [takeL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [takeLA_un, ih]

theorem dropL_encNs (l : List ℕ) (r : List Bool) : dropL (encNs l ++ false :: r) = r := by
  induction l with
  | nil => simp [dropL, dropLA]
  | cons a l ih =>
    rw [dropL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [dropLA_un, ih]

theorem headL_encNs (l : List ℕ) (r : List Bool) :
    headL (encNs l ++ false :: r) = encNs l ++ [false] := by
  induction l with
  | nil => simp [headL, headLA]
  | cons a l ih =>
    rw [headL] at ih ⊢
    rw [encNs_cons, encN_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [headLA_un, ih]

@[simp] theorem takeL_nil : takeL [] = [] := rfl

@[simp] theorem dropL_nil : dropL [] = [] := rfl

@[simp] theorem headL_nil : headL [] = [] := rfl

theorem dropL_iter_nil (k : ℕ) : dropL^[k] [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

theorem dropL_iter_encLL (k : ℕ) (S : List (List ℕ)) :
    dropL^[k] (encLL S) = encLL (S.drop k) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases S with
    | nil => simpa using ih []
    | cons a S => rw [encLL_cons, dropL_encNs]; simpa using ih S

theorem fetch_spec (P : List Instr) (n : ℕ) :
    takeL (dropL^[n] (encP P)) = match P[n]? with
      | none => []
      | some i => encNs (instrNs i) := by
  rw [encP, dropL_iter_encLL]
  induction P generalizing n with
  | nil => simp
  | cons i P ih =>
    cases n with
    | zero => simp [encLL_cons, takeL_encNs]
    | succ n => simpa using ih n

theorem move_pairB (r d : List Bool) : move (pairB r d) = pairB (dropL r) (d ++ headL r) := by
  simp [move, unpairB_pairB]

theorem move_iter_encLL (k : ℕ) (S : List (List ℕ)) (d : List Bool) :
    move^[k] (pairB (encLL S) d) = pairB (encLL (S.drop k)) (d ++ encLL (S.take k)) := by
  induction k generalizing S d with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, move_pairB]
    cases S with
    | nil => simpa using ih [] d
    | cons a S =>
      rw [encLL_cons, dropL_encNs, headL_encNs, ih]
      simp [encLL_cons]

theorem hd_drop_encLL (S : List (List ℕ)) (k : ℕ) :
    hd (encLL (S.drop k)) = un (topIndex (S.getD k [])) := by
  induction S generalizing k with
  | nil => simp [topIndex]
  | cons a S ih =>
    cases k with
    | zero =>
      cases a with
      | nil => simp [encLL_cons, hd, topIndex]
      | cons s a =>
        simp only [List.drop_zero, encLL_cons, encNs_cons, encN, List.append_assoc,
          List.cons_append, List.nil_append]
        rw [hd_un]; simp [topIndex]
    | succ k => simpa using ih k

theorem ins_spec (l : List ℕ) (S : List (List ℕ)) (k : ℕ) :
    sel (encLL (S.drop k)) (encLL (S.take k))
        (encLL (S.take k) ++ (encNs l ++ encLL (S.drop k))) =
      encLL (S.set k (l ++ S.getD k [])) := by
  induction S generalizing k with
  | nil => simp
  | cons a S ih =>
    cases k with
    | zero =>
      simp [encLL_cons, encNs_append]
      cases h : encNs a <;> simp
    | succ k =>
      have := ih k
      simp only [List.drop_succ_cons, List.take_succ_cons, List.set_cons_succ, encLL_cons,
        List.getD_cons_succ, List.append_assoc, List.cons_append] at this ⊢
      rw [← this]
      unfold sel; split <;> simp

theorem pop_spec (S : List (List ℕ)) (k : ℕ) :
    encLL (S.take k) ++ popT (encLL (S.drop k)) = encLL (S.set k (S.getD k []).tail) := by
  induction S generalizing k with
  | nil => simp [popT]
  | cons a S ih =>
    cases k with
    | zero =>
      cases a with
      | nil => simp [encLL_cons, popT]
      | cons s a =>
        simp only [List.take_zero, encLL_nil, List.nil_append, List.drop_zero, List.set_cons_zero,
          List.getD_cons_zero, List.tail_cons]
        rw [encLL_cons, encLL_cons, encNs_cons, encN, un_succ]
        simp only [List.cons_append, List.append_assoc, popT]
        rw [← List.cons_append, ← un_succ, dropN_un]
        simp
    | succ k =>
      have := ih k
      simp only [List.drop_succ_cons, List.take_succ_cons, List.set_cons_succ, encLL_cons,
        List.getD_cons_succ, List.append_assoc, List.cons_append] at this ⊢
      rw [this]

theorem bump_append (a b : List Bool) : bump (a ++ b) = bump a ++ bump b := by
  simp [bump]

theorem inX_spec (x : List Bool) :
    bump (spread x) = encNs (x.map fun b => cond b 1 0) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h : spread (b :: x) = (if b then [true, false] else [false]) ++ spread x := by
      simp [spread]
    rw [h, bump_append, ih, List.map_cons, encNs_cons]
    cases b <;> rfl

theorem inW_spec (w : List Bool) :
    bump (bump (bump (spread w))) = encNs (w.map fun b => cond b 3 2) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have h : spread (b :: w) = (if b then [true, false] else [false]) ++ spread w := by
      simp [spread]
    rw [h, bump_append, bump_append, bump_append, ih, List.map_cons, encNs_cons]
    cases b <;> rfl

theorem blank_un (n : ℕ) : blank (un n) = encLL (List.replicate n []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [un_succ, List.replicate_succ, encLL_cons, ← ih]; rfl

theorem hd_length (s : List Bool) : (hd s).length ≤ s.length :=
  (List.takeWhile_prefix _).length_le

theorem dropN_length (s : List Bool) : (dropN s).length ≤ s.length := by
  have := (List.dropWhile_suffix (l := s) id).length_le
  simp only [dropN, List.length_tail]
  omega

theorem iter_length (g : List Bool → List Bool) (hg : ∀ s, (g s).length ≤ s.length) (k : ℕ)
    (s : List Bool) : (g^[k] s).length ≤ s.length := by
  induction k generalizing s with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply]; exact (ih _).trans (hg s)

theorem takeLA_length (b : Bool) (s : List Bool) : (takeLA b s).length ≤ s.length := by
  induction s generalizing b with
  | nil => simp [takeLA]
  | cons a s ih =>
    cases a <;> cases b <;> simp [takeLA] <;> exact ih _

theorem head_drop_LA (b : Bool) (s : List Bool) : headLA b s ++ dropLA b s = s := by
  induction s generalizing b with
  | nil => simp [headLA, dropLA]
  | cons a s ih =>
    cases a <;> cases b <;> simp [headLA, dropLA] <;> exact ih _

theorem headL_dropL (s : List Bool) : headL s ++ dropL s = s := head_drop_LA false s

theorem headL_dropL_length (s : List Bool) : (headL s).length + (dropL s).length = s.length := by
  have := congrArg List.length (headL_dropL s)
  simpa using this

theorem takeL_length (s : List Bool) : (takeL s).length ≤ s.length := takeLA_length false s

theorem dropL_length (s : List Bool) : (dropL s).length ≤ s.length := by
  have := headL_dropL_length s; omega

theorem popT_length (s : List Bool) : (popT s).length ≤ s.length := by
  unfold popT
  split
  · exact dropN_length _
  · exact le_rfl

theorem sel_length (f a b : List Bool) (B : ℕ) (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (sel f a b).length ≤ B := by
  unfold sel; split <;> assumption

theorem unpairB_length (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have h := congrArg List.length (List.takeWhile_append_dropWhile (p := id) (l := s))
  simp only [List.length_append] at h
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  omega

theorem pairB_length (a b : List Bool) : (pairB a b).length = 2 * a.length + b.length + 1 := by
  simp [pairB]; omega

theorem move_length (y : List Bool) : (move y).length ≤ y.length + 1 := by
  have h := unpairB_length y
  have h2 := headL_dropL_length (unpairB y).1
  simp only [move, pairB_length, List.length_append]
  omega

theorem move_iter (k : ℕ) (r d : List Bool) :
    ∃ d', move^[k] (pairB r d) = pairB (dropL^[k] r) d' ∧
      (dropL^[k] r).length + d'.length ≤ r.length + d.length := by
  induction k generalizing r d with
  | zero => exact ⟨d, rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨d', h1, h2⟩ := ih (dropL r) (d ++ headL r)
    refine ⟨d', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, move_pairB, h1, Function.iterate_succ_apply]
    · have := headL_dropL_length r
      rw [Function.iterate_succ_apply]
      simp only [List.length_append] at h2
      omega

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Universal

def fetch (ps pc : List Bool) : List Bool := takeL (dropL^[pc.tail.length] ps)

def fOp (I : List Bool) : List Bool := hd I

def fK (I : List Bool) : List Bool := (hd (dropN I)).tail

def fW (I : List Bool) : List Bool := (hd (dropN (dropN I))).tail

def fN1 (I : List Bool) : List Bool := hd (dropN (dropN (dropN I)))

def fN2 (I : List Bool) : List Bool := hd (dropN (dropN (dropN (dropN I))))

def fTb (I : List Bool) : List Bool := dropN (dropN (dropN (dropN (dropN I))))

def lookup (tb idx : List Bool) : List Bool := (hd (dropN^[idx.length] tb)).tail

def splitK (kf sk : List Bool) : List Bool := move^[kf.length] (pairB sk [])

def pcSel (pc o n1 n2 valS : List Bool) : List Bool :=
  sel pc pc (sel o [] (sel o.tail n1 (sel o.tail.tail n1 (sel o.tail.tail.tail n1
    (sel o.tail.tail.tail.tail n1 (sel o.tail.tail.tail.tail.tail (sel valS n2 n1)
      (sel o.tail.tail.tail.tail.tail.tail (true :: valS) [])))))))

def stSel (pc o st valS valT : List Bool) : List Bool :=
  sel pc st (sel o st (sel o.tail st (sel o.tail.tail valT (sel o.tail.tail.tail valT
    (sel o.tail.tail.tail.tail valS st)))))

def skSel (pc o sk r d pushed : List Bool) : List Bool :=
  sel pc sk (sel o sk (sel o.tail (sel r d (d ++ (pushed ++ r)))
    (sel o.tail.tail (d ++ popT r) sk)))

def pcOut (ps pc st : List Bool) : List Bool :=
  pcSel pc (fOp (fetch ps pc)) (fN1 (fetch ps pc)) (fN2 (fetch ps pc))
    (lookup (fTb (fetch ps pc)) st)

def stOut (ps pc st sk : List Bool) : List Bool :=
  stSel pc (fOp (fetch ps pc)) st (lookup (fTb (fetch ps pc)) st)
    (lookup (fTb (fetch ps pc))
      (mulU st (fW (fetch ps pc)) ++ hd (unpairB (splitK (fK (fetch ps pc)) sk)).1))

def skOut (ps pc st sk : List Bool) : List Bool :=
  skSel pc (fOp (fetch ps pc)) sk (unpairB (splitK (fK (fetch ps pc)) sk)).1
    (unpairB (splitK (fK (fetch ps pc)) sk)).2
    (true :: lookup (fTb (fetch ps pc)) st ++ [false])

def sstepParts (ps pc st sk : List Bool) : List Bool :=
  pairB ps (pairB (pcOut ps pc st) (pairB (stOut ps pc st sk) (skOut ps pc st sk)))

def sstep (y : List Bool) : List Bool :=
  sstepParts (unpairB y).1 (unpairB (unpairB y).2).1 (unpairB (unpairB (unpairB y).2).2).1
    (unpairB (unpairB (unpairB y).2).2).2

theorem fetch_encP (P : List Instr) (n : ℕ) :
    fetch (encP P) (un (n + 1)) = match P[n]? with
      | none => []
      | some i => encNs (instrNs i) := by
  rw [fetch, un_succ, List.tail_cons, un_length]
  exact fetch_spec P n

theorem lookup_encNs (tbl : List ℕ) (i : List Bool) :
    lookup (encNs tbl) i = un (tbl.getD i.length 0) := lookup_spec _ _

theorem splitK_encLL (k : ℕ) (S : List (List ℕ)) :
    unpairB (splitK (un k) (encLL S)) = (encLL (S.drop k), encLL (S.take k)) := by
  rw [splitK, un_length, move_iter_encLL, unpairB_pairB, List.nil_append]

section fields

variable (a b c d e : ℕ) (tbl : List ℕ)

theorem fOp_enc : fOp (encNs (a :: b :: c :: d :: e :: tbl)) = un (a + 1) := by simp [fOp]

theorem fK_enc : fK (encNs (a :: b :: c :: d :: e :: tbl)) = un b := by simp [fK, un_succ]

theorem fW_enc : fW (encNs (a :: b :: c :: d :: e :: tbl)) = un c := by simp [fW, un_succ]

theorem fN1_enc : fN1 (encNs (a :: b :: c :: d :: e :: tbl)) = un (d + 1) := by simp [fN1]

theorem fN2_enc : fN2 (encNs (a :: b :: c :: d :: e :: tbl)) = un (e + 1) := by simp [fN2]

theorem fTb_enc : fTb (encNs (a :: b :: c :: d :: e :: tbl)) = encNs tbl := by simp [fTb]

end fields

theorem un_one : un 1 = [true] := rfl
theorem un_two : un 2 = [true, true] := rfl
theorem un_three : un 3 = [true, true, true] := rfl
theorem un_four : un 4 = [true, true, true, true] := rfl
theorem un_five : un 5 = [true, true, true, true, true] := rfl
theorem un_six : un 6 = [true, true, true, true, true, true] := rfl
theorem un_seven : un 7 = [true, true, true, true, true, true, true] := rfl

theorem sel_un (n : ℕ) (a b : List Bool) : sel (un n) a b = if n = 0 then a else b := by
  cases n <;> simp [un_succ]

theorem out_spec (P : List Instr) (pc : Option ℕ) (v : ℕ) (S : List (List ℕ)) :
    pcOut (encP P) (encPc pc) (un v) = encPc (step P ⟨pc, v, S⟩).pc ∧
    stOut (encP P) (encPc pc) (un v) (encLL S) = un (step P ⟨pc, v, S⟩).state ∧
    skOut (encP P) (encPc pc) (un v) (encLL S) = encLL (step P ⟨pc, v, S⟩).stk := by
  cases pc with
  | none => simp [pcOut, stOut, skOut, pcSel, stSel, skSel, encPc, step]
  | some n =>
    have hf := fetch_encP P n
    simp only [pcOut, stOut, skOut, encPc, step]
    cases h : P[n]? with
    | none =>
      rw [h] at hf
      simp only [hf]
      simp [pcSel, stSel, skSel, fOp, un_succ]
    | some i =>
      rw [h] at hf
      simp only [hf]
      cases i with
      | push k tbl next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · have := ins_spec [tbl.getD v 0] S k
          simp only [encNs_cons, encN, encNs_nil, List.append_nil,
            un_succ, List.cons_append] at this
          simpa [skSel, un_succ] using this
      | pop k tbl w next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length, hd_drop_encLL,
          List.length_append, mulU]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ, pop_spec]
      | peek k tbl w next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length, hd_drop_encLL,
          List.length_append, mulU]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | load tbl next =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | branch tbl next₁ next₂ =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp only [pcSel, sel_un]
          by_cases hz : tbl[v]?.getD 0 = 0 <;> simp [hz, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | goto tbl =>
        simp only [instrNs, List.cons_append, List.nil_append, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]
      | halt =>
        simp only [instrNs, fOp_enc, fK_enc, fW_enc, fN1_enc,
          fN2_enc, fTb_enc, lookup_encNs, splitK_encLL, exec, un_length]
        refine ⟨?_, ?_, ?_⟩
        · simp [pcSel, un_succ]
        · simp [stSel, un_succ]
        · simp [skSel, un_succ]

theorem sstep_encCfg (P : List Instr) (cfg : Cfg) :
    sstep (encCfg P cfg) = encCfg P (step P cfg) := by
  obtain ⟨pc, v, S⟩ := cfg
  obtain ⟨h1, h2, h3⟩ := out_spec P pc v S
  simp only [sstep, encCfg, unpairB_pairB, sstepParts, h1, h2, h3]

theorem sstep_iter (P : List Instr) (cfg : Cfg) (t : ℕ) :
    sstep^[t] (encCfg P cfg) = encCfg P ((step P)^[t] cfg) := by
  induction t generalizing cfg with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sstep_encCfg, ih]

theorem tail_length_le (s : List Bool) : s.tail.length ≤ s.length := by simp

theorem fetch_length (ps pc : List Bool) : (fetch ps pc).length ≤ ps.length :=
  (takeL_length _).trans (iter_length dropL dropL_length _ _)

theorem lookup_length (tb idx : List Bool) : (lookup tb idx).length ≤ tb.length :=
  (tail_length_le _).trans ((hd_length _).trans (iter_length dropN dropN_length _ _))

theorem fN1_length (I : List Bool) : (fN1 I).length ≤ I.length :=
  (hd_length _).trans ((dropN_length _).trans ((dropN_length _).trans (dropN_length _)))

theorem fN2_length (I : List Bool) : (fN2 I).length ≤ I.length :=
  (hd_length _).trans ((dropN_length _).trans ((dropN_length _).trans
    ((dropN_length _).trans (dropN_length _))))

theorem fTb_length (I : List Bool) : (fTb I).length ≤ I.length :=
  (dropN_length _).trans ((dropN_length _).trans ((dropN_length _).trans
    ((dropN_length _).trans (dropN_length _))))

theorem pcOut_length (ps pc st : List Bool) :
    (pcOut ps pc st).length ≤ pc.length + ps.length + 1 := by
  have h0 := fetch_length ps pc
  have h1 := fN1_length (fetch ps pc)
  have h2 := fN2_length (fetch ps pc)
  have h3 := (lookup_length (fTb (fetch ps pc)) st).trans (fTb_length _)
  unfold pcOut pcSel
  repeat' apply sel_length
  all_goals (try simp only [List.length_cons, List.length_nil]); omega

theorem stOut_length (ps pc st sk : List Bool) :
    (stOut ps pc st sk).length ≤ st.length + ps.length := by
  have h0 := fetch_length ps pc
  have h3 := fun idx => (lookup_length (fTb (fetch ps pc)) idx).trans (fTb_length _)
  have h4 := h3 st
  have h5 := h3 (mulU st (fW (fetch ps pc)) ++ hd (unpairB (splitK (fK (fetch ps pc)) sk)).1)
  unfold stOut stSel
  repeat' apply sel_length
  all_goals omega

theorem skOut_length (ps pc st sk : List Bool) :
    (skOut ps pc st sk).length ≤ sk.length + ps.length + 2 := by
  have h0 := fetch_length ps pc
  have h3 := (lookup_length (fTb (fetch ps pc)) st).trans (fTb_length _)
  obtain ⟨d', e1, e2⟩ := move_iter (fK (fetch ps pc)).length sk []
  have e3 : unpairB (splitK (fK (fetch ps pc)) sk) = (dropL^[(fK (fetch ps pc)).length] sk, d') := by
    rw [splitK, e1, unpairB_pairB]
  have h6 := popT_length (dropL^[(fK (fetch ps pc)).length] sk)
  unfold skOut skSel
  rw [e3]
  repeat' apply sel_length
  all_goals simp only [List.length_cons, List.length_nil, List.length_append] at *; omega

def smeasure (y : List Bool) : ℕ := 5 * (unpairB y).1.length + 7

theorem smeasure_sstep (y : List Bool) : smeasure (sstep y) ≤ smeasure y := by
  simp [smeasure, sstep, sstepParts, unpairB_pairB]

theorem sstep_length (y : List Bool) : (sstep y).length ≤ y.length + smeasure y := by
  have a1 := unpairB_length y
  have a2 := unpairB_length (unpairB y).2
  have a3 := unpairB_length (unpairB (unpairB y).2).2
  have b1 := pcOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1
  have b2 := stOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2
  have b3 := skOut_length (unpairB y).1 (unpairB (unpairB y).2).1
    (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2
  simp only [sstep, sstepParts, pairB_length, smeasure]
  omega

theorem smeasure_le (y : List Bool) : smeasure y ≤ 7 * y.length + 7 := by
  have a1 := unpairB_length y
  simp only [smeasure]
  omega

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Universal

def hNst (h : List Bool) : List Bool := (hd h).tail

def hPc (h : List Bool) : List Bool := hd (dropN h)

def hSt (h : List Bool) : List Bool := (hd (dropN (dropN h))).tail

def hKin (h : List Bool) : List Bool := (hd (dropN (dropN (dropN h)))).tail

def hKout (h : List Bool) : List Bool := (hd (dropN (dropN (dropN (dropN h))))).tail

def insK (kf new sk : List Bool) : List Bool :=
  sel (unpairB (splitK kf sk)).1 (unpairB (splitK kf sk)).2
    ((unpairB (splitK kf sk)).2 ++ (new ++ (unpairB (splitK kf sk)).1))

def inSyms (x w : List Bool) : List Bool := bump (spread x) ++ bump (bump (bump (spread w)))

def initS (cs x w : List Bool) : List Bool :=
  pairB (unpairB cs).1 (pairB (hPc (unpairB cs).2) (pairB (hSt (unpairB cs).2)
    (insK (hKin (unpairB cs).2) (inSyms x w) (blank (hNst (unpairB cs).2)))))

def haltedS (y : List Bool) : Bool := (unpairB (unpairB y).2).1.isEmpty

def stkS (y : List Bool) : List Bool := (unpairB (unpairB (unpairB y).2).2).2

def outOne (kout sk : List Bool) : Bool :=
  decide ((dropL^[kout.length] sk).take 4 = [true, true, false, false])

def V (p : List Bool × List Bool) : Bool :=
  decide (p.2.length ≤ (unpairB (unpairB p.1).2).2.length) &&
    (haltedS (sstep^[(unpairB (unpairB p.1).2).2.length]
      (initS (unpairB p.1).1 (unpairB (unpairB p.1).2).1 p.2)) &&
    outOne (hKout (unpairB (unpairB p.1).1).2)
      (stkS (sstep^[(unpairB (unpairB p.1).2).2.length]
        (initS (unpairB p.1).1 (unpairB (unpairB p.1).2).1 p.2))))

theorem getD_replicate_nil (n k : ℕ) : (List.replicate n ([] : List ℕ)).getD k [] = [] := by
  induction n generalizing k with
  | zero => simp
  | succ n ih => cases k with
    | zero => simp [List.replicate_succ]
    | succ k => simpa [List.replicate_succ] using ih k

theorem insK_spec (k : ℕ) (l : List ℕ) (S : List (List ℕ)) :
    insK (un k) (encNs l) (encLL S) = encLL (S.set k (l ++ S.getD k [])) := by
  rw [insK, splitK_encLL, ins_spec]

theorem inSyms_spec (x w : List Bool) :
    inSyms x w = encNs ((x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2) := by
  rw [inSyms, inX_spec, inW_spec, encNs_append]

theorem initS_spec (c : Code) (x w : List Bool) :
    initS (encCode c) x w =
      encCfg c.prog (c.init ((x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2)) := by
  have h1 : hNst (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.nstk := by
    simp [hNst, un_succ]
  have h2 : hPc (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un (c.pc₀ + 1) := by
    simp [hPc]
  have h3 : hSt (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.state₀ := by
    simp [hSt, un_succ]
  have h4 : hKin (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.kin := by
    simp [hKin, un_succ]
  simp only [initS, encCode, unpairB_pairB, h1, h2, h3, h4, blank_un, inSyms_spec, insK_spec,
    getD_replicate_nil, List.append_nil, encCfg, Code.init, encPc]

theorem haltedS_encCfg (P : List Instr) (cfg : Cfg) :
    haltedS (encCfg P cfg) = true ↔ cfg.pc = none := by
  obtain ⟨pc, v, S⟩ := cfg
  cases pc <;> simp [haltedS, encCfg, unpairB_pairB, encPc, un_succ]

theorem stkS_encCfg (P : List Instr) (cfg : Cfg) : stkS (encCfg P cfg) = encLL cfg.stk := by
  simp [stkS, encCfg, unpairB_pairB]

theorem outOne_spec (k : ℕ) (S : List (List ℕ)) :
    outOne (un k) (encLL S) = true ↔ S.getD k [] = [1] := by
  rw [outOne, un_length, dropL_iter_encLL, decide_eq_true_eq]
  induction S generalizing k with
  | nil => simp
  | cons a S ih =>
    cases k with
    | zero =>
      rcases a with _ | ⟨s, a⟩
      · simp [encLL_cons]
      · rcases s with _ | _ | s
        · simp [encLL_cons, encNs_cons, encN, un_succ]
        · rcases a with _ | ⟨s', a⟩
          · simp [encLL_cons, encNs_cons, encN, un_succ]
          · simp [encLL_cons, encNs_cons, encN, un_succ]
        · simp [encLL_cons, encNs_cons, encN, un_succ]
    | succ k => simpa using ih k

theorem V_spec (c : Code) (x w : List Bool) (t : ℕ) :
    V (pairB (encCode c) (pairB x (un t)), w) = true ↔
      (w.length ≤ t ∧ c.outputsWithin
        (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2)) t [1]) := by
  have h5 : hKout (unpairB (encCode c)).2 = un c.kout := by
    simp [hKout, encCode, unpairB_pairB, un_succ]
  simp only [V, unpairB_pairB, un_length, initS_spec, sstep_iter, h5, Bool.and_eq_true,
    decide_eq_true_eq, haltedS_encCfg, stkS_encCfg, outOne_spec, Code.outputsWithin, Code.run]

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Machines

open Turing

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

section pushes

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

end pushes

noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step tm.m a with
    | none =>
      have e : flip bind (TM2.step tm.m) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l

def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l

theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁)
    (q : Q) (l : List Γ₀) :
    fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1, (δ q a).2, none)) fin q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun, fstRun2, ih]

inductive TrK : Type
  | inp | tmp | out
  deriving DecidableEq

instance : Fintype TrK :=
  Fintype.ofList [.inp, .tmp, .out] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ Q : Type}

abbrev TrΓ (Γ₀ Γ₁ Q : Type) : TrK → Type
  | .inp => Γ₀
  | .tmp => Q × Option Γ₀
  | .out => Γ₁

abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool

def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.1
  | (q, none) => fin q

def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.2
  | (_, none) => none

def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁)
    (e : Q × Option Γ₀) : List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList

def trTrace (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q → List Γ₀ → List (Q × Option Γ₀)
  | q, [] => [(q, none)]
  | q, a :: l => (q, some a) :: trTrace δ (δ q a).1 l

theorem trTrace_length (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
    (trTrace δ q l).length = l.length + 1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [trTrace, ih]

theorem trTrace_out (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q : Q)
    (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
  induction l generalizing q with
  | nil => simp [trTrace, trOut, trO1, trO2, fstRun2]
  | cons a l ih => simp [trTrace, trOut, trO1, trO2, fstRun2, ih]

def trWrite (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s => (o s).isSome)
    (match d with
      | some dd => .push .out (fun s => (o s).getD dd) next
      | none => next)
    next

def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
    (d : Option Γ₁) : Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o => (s.1, o, o.isSome))
      (.branch (fun s => s.2.2)
        (.push .tmp (fun s => (s.1, s.2.1))
          (.load (fun s => (match s.2.1 with
              | some a => (δ s.1 a).1
              | none => s.1, none, false))
            (.goto fun _ => false)))
        (.push .tmp (fun s => (s.1, none))
          (.load (fun _ => (q₀, none, false)) (.goto fun _ => true))))
  | true =>
    .pop .tmp (fun _ o => match o with
        | some e => (e.1, e.2, true)
        | none => (q₀, none, false))
      (.branch (fun s => s.2.2)
        (trWrite (fun s => trO2 δ (s.1, s.2.1)) d
          (trWrite (fun s => trO1 δ fin (s.1, s.2.1)) d (.goto fun _ => true)))
        .halt)

def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
  K := TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main := false
  σ := TrS Γ₀ Q
  initialState := (q₀, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := trProg δ fin q₀ d

def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)
  | .inp => l
  | .tmp => t
  | .out => u

theorem trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .inp l' = trSt l' t u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .tmp t' = trSt l t' u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
    Function.update (trSt l t u) .out u' = trSt l t u' := by
  funext k; cases k <;> simp [trSt]

theorem trSt_start (l : List Γ₀) :
    (trSt l [] [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .inp l := by
  funext k; cases k <;> simp [trSt]

theorem trSt_end (u : List Γ₁) :
    (trSt [] [] u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .out u := by
  funext k; cases k <;> simp [trSt]

abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)

theorem trWrite_stepAux (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁, d ≠ none)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.stepAux (trWrite o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
  cases ho : o s with
  | none => cases d <;> simp [trWrite, TM2.stepAux, ho]
  | some y =>
    cases d with
    | none => exact absurd rfl (hd y)
    | some dd => simp [trWrite, TM2.stepAux, ho, trSt, trSt_set_out]

variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
  (d : Option Γ₁)

theorem trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
    (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (q₀, none, false), trSt [] ((s.1, none) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trB_cons (hd : ∀ _ : Γ₁, d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ := by
  simp only [TM2.step, trProg, TM2.stepAux]
  have e1 : (trSt [] (e :: t) u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .tmp = e :: t := rfl
  rw [e1]
  simp only [List.head?_cons, List.tail_cons, Bool.cond_true]
  rw [trSt_set_tmp, trWrite_stepAux _ _ hd, trWrite_stepAux _ _ hd]
  simp [TM2.stepAux, trOut]

theorem trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨none, (q₀, none, false), trSt [] [] u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_tmp]

theorem trLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
          (some (⟨some false, s, trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (q₀, none, false), trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e, ih]
    simp [trTrace]

theorem trLoopB (hd : ∀ _ : Γ₁, d ≠ none) :
    ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
          (some (⟨some true, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none, (q₀, none, false), trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e' : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e', ih]
    simp [List.flatMap_append]

theorem trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁, d ≠ none) (l : List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
    (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
    (some (⟨some false, (q₀, none, false), Function.update (fun _ => []) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none, (q₀, none, false), Function.update (fun _ => []) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
      (some (⟨some false, (q₀, none, false), trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ := by
    have := trLoopA δ fin q₀ d [] l [] (q₀, none, false)
    rw [List.append_nil] at this
    exact this
  have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
      (some (⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none, (q₀, none, false), trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
    have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀, none, false)
    rw [List.length_reverse, trTrace_length, List.reverse_reverse, trTrace_out,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply, ← trSt_start, hA, hB, trSt_end]

theorem fst2_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

theorem fst_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin : Q → Option βΓ) (q₀ : Q)
    (h : ∀ a, eb (f a) = fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a => ((δ q a).1, (δ q a).2, none)) fin q₀
    (fun a => (h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Universal

open PEqualNP.Library.Machines

def halfD (q : Bool) (_ : Bool) : Bool × Option Bool := (!q, if q then some true else none)

def half (u : List Bool) : List Bool := fstRun halfD (fun _ => none) false u

theorem halfD_run (q : Bool) (u : List Bool) :
    fstRun halfD (fun _ => none) q u = un ((u.length + (if q then 1 else 0)) / 2) := by
  induction u generalizing q with
  | nil => cases q <;> rfl
  | cons b l ih =>
    cases q
    · simp [fstRun, halfD, ih]
    · have e : (l.length + 1 + 1) / 2 = l.length / 2 + 1 := by omega
      simp [fstRun, halfD, ih, e, un_succ]

theorem half_eq (u : List Bool) : half u = un (u.length / 2) := by
  simp [half, halfD_run]

def lgStep (s : List Bool) : List Bool :=
  sel (unpairB s).2 s (pairB (true :: (unpairB s).1) (half (unpairB s).2))

def lgU (u : List Bool) : List Bool := (unpairB (lgStep^[u.length] (pairB [] u))).1

theorem size_half {r : ℕ} (hr : r ≠ 0) : Nat.size r = Nat.size (r / 2) + 1 := by
  apply le_antisymm
  · rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self (r / 2)
    omega
  · rw [Nat.succ_le_iff, Nat.lt_size]
    rcases Nat.eq_zero_or_pos (Nat.size (r / 2)) with h | h
    · rw [h]; simp; omega
    · have h1 : Nat.size (r / 2) - 1 < Nat.size (r / 2) := by omega
      rw [Nat.lt_size] at h1
      have h2 : 2 ^ Nat.size (r / 2) = 2 ^ (Nat.size (r / 2) - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      omega

theorem lgStep_zero (c : ℕ) : lgStep (pairB (un c) (un 0)) = pairB (un c) (un 0) := by
  simp [lgStep, unpairB_pairB, sel]

theorem lgStep_pos (c r : ℕ) (hr : r ≠ 0) :
    lgStep (pairB (un c) (un r)) = pairB (un (c + 1)) (un (r / 2)) := by
  have h : un r ≠ [] := by
    intro h
    exact hr (by simpa using congrArg List.length h)
  simp [lgStep, unpairB_pairB, sel, h, half_eq, un_succ]

theorem lgStep_iter (k : ℕ) : ∀ r c : ℕ, r < 2 ^ k →
    lgStep^[k] (pairB (un c) (un r)) = pairB (un (c + Nat.size r)) (un 0) := by
  induction k with
  | zero =>
    intro r c hr
    obtain rfl : r = 0 := by simpa using hr
    simp
  | succ k ih =>
    intro r c hr
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      rw [lgStep_zero]
      exact ih 0 c (Nat.pos_of_ne_zero (by positivity))
    · rw [lgStep_pos c r (by omega), ih (r / 2) (c + 1) (by rw [pow_succ] at hr; omega),
        size_half (by omega : r ≠ 0)]
      congr 2
      omega

theorem lgU_un (n : ℕ) : lgU (un n) = un (Nat.size n) := by
  have h := lgStep_iter n n 0 Nat.lt_two_pow_self
  rw [un_zero] at h
  simp [lgU, h, unpairB_pairB]

theorem un_length_eq (u : List Bool) (h : ∀ b ∈ u, b = true) : u = un u.length :=
  List.eq_replicate_iff.2 ⟨rfl, h⟩

theorem lgU_length (n : ℕ) : (lgU (un n)).length = Nat.size n := by
  rw [lgU_un, un_length]

def condC (y mu : List Bool) : Bool := decide (y.length ≤ (lgU (lgU mu)).length)

theorem condC_un (y : List Bool) (m : ℕ) :
    condC y (un m) = decide (y.length ≤ Nat.size (Nat.size m)) := by
  simp [condC, lgU_un]

def succD (carry : Bool) (b : Bool) : Bool × Option Bool :=
  if carry then (b, some (!b)) else (false, some b)

def succFin (carry : Bool) : Option Bool := if carry then some false else none

def succB (s : List Bool) : List Bool := fstRun succD succFin true s

def cand (j : ℕ) : List Bool := succB^[j] []

theorem succD_run_false (s : List Bool) : fstRun succD succFin false s = s := by
  induction s with
  | nil => rfl
  | cons b l ih => simp [fstRun, succD, ih]

theorem succB_nil : succB [] = [false] := rfl

theorem succB_false (r : List Bool) : succB (false :: r) = true :: r := by
  simp [succB, fstRun, succD, succD_run_false]

theorem succB_true (r : List Bool) : succB (true :: r) = false :: succB r := by
  simp [succB, fstRun, succD]

def idx : List Bool → ℕ
  | [] => 0
  | false :: r => 1 + 2 * idx r
  | true :: r => 2 + 2 * idx r

theorem idx_succB (s : List Bool) : idx (succB s) = idx s + 1 := by
  induction s with
  | nil => rfl
  | cons b r ih =>
    cases b
    · rw [succB_false]; simp [idx]; omega
    · rw [succB_true]; simp [idx, ih]; omega

theorem idx_cand (j : ℕ) : idx (cand j) = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cand, Function.iterate_succ_apply', ← cand, idx_succB, ih]

theorem idx_inj : ∀ s t : List Bool, idx s = idx t → s = t
  | [], [], _ => rfl
  | [], false :: _, h => by simp [idx] at h; omega
  | [], true :: _, h => by simp [idx] at h; omega
  | false :: _, [], h => by simp [idx] at h
  | true :: _, [], h => by simp [idx] at h
  | false :: r, false :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | true :: r, true :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | false :: _, true :: _, h => by simp [idx] at h; omega
  | true :: _, false :: _, h => by simp [idx] at h; omega

theorem cand_idx (s : List Bool) : cand (idx s) = s := idx_inj _ _ (idx_cand _)

theorem idx_bound (s : List Bool) : idx s + 2 ≤ 2 ^ (s.length + 1) := by
  induction s with
  | nil => simp [idx]
  | cons b r ih =>
    have e : 2 ^ ((b :: r).length + 1) = 2 * 2 ^ (r.length + 1) := by
      rw [List.length_cons, pow_succ, Nat.mul_comm]
    cases b <;> simp only [idx] <;> omega

theorem idx_lt_of_length_le {s : List Bool} {b : ℕ} (h : s.length ≤ b) :
    idx s + 2 ≤ 2 ^ (b + 1) :=
  (idx_bound s).trans (Nat.pow_le_pow_right (by omega) (by omega))

def bflag (b : Bool) : List Bool := if b then [true] else []

theorem bflag_eq_nil (b : Bool) : bflag b = [] ↔ b = false := by
  cases b <;> simp [bflag]

def srchStep (s : List Bool) : List Bool :=
  pairB (unpairB s).1 (pairB (succB (unpairB (unpairB s).2).1)
    ((unpairB (unpairB s).2).2 ++ bflag (V ((unpairB s).1, (unpairB (unpairB s).2).1))))

def srch (F n : List Bool) : List Bool :=
  (unpairB (unpairB (srchStep^[n.length] (pairB F (pairB [] [])))).2).2

theorem srchStep_pair (F c fl : List Bool) :
    srchStep (pairB F (pairB c fl)) = pairB F (pairB (succB c) (fl ++ bflag (V (F, c)))) := by
  simp [srchStep, unpairB_pairB]

theorem srchStep_iter (F : List Bool) (k : ℕ) : ∀ c fl : List Bool, ∃ fl' : List Bool,
    srchStep^[k] (pairB F (pairB c fl)) = pairB F (pairB (succB^[k] c) fl') ∧
      (fl' = [] ↔ fl = [] ∧ ∀ j < k, V (F, succB^[j] c) = false) := by
  induction k with
  | zero => intro c fl; exact ⟨fl, rfl, by simp⟩
  | succ k ih =>
    intro c fl
    obtain ⟨fl', h1, h2⟩ := ih (succB c) (fl ++ bflag (V (F, c)))
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, srchStep_pair, h1, Function.iterate_succ_apply]
    · rw [h2, List.append_eq_nil_iff, bflag_eq_nil, Nat.forall_lt_succ_left, and_assoc]
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

theorem srch_eq_nil (F n : List Bool) :
    srch F n = [] ↔ ∀ j < n.length, V (F, cand j) = false := by
  obtain ⟨fl', h1, h2⟩ := srchStep_iter F n.length [] []
  rw [srch, h1]
  simpa [unpairB_pairB, cand] using h2

def csOf (z : List Bool) : List Bool := (unpairB z).1

def muOf (z : List Bool) : List Bool := (unpairB (unpairB z).2).2

def y0Of (z : List Bool) : List Bool := pairB (unpairB z).1 (pairB (unpairB (unpairB z).2).1 [])

def RD (p : List Bool × List Bool) : Bool :=
  (!condC (y0Of p.1) (muOf p.1) &&
      V (pairB (csOf p.1) (pairB (p.1 ++ [true]) (unpairB p.2).2), (unpairB p.2).1)) ||
    (condC (y0Of p.1) (muOf p.1) && (!condC (y0Of p.1) (muOf p.1).tail &&
      (srch (pairB (csOf p.1) (pairB (y0Of p.1) (lgU (muOf p.1))))
        (muOf p.1 ++ (muOf p.1 ++ (muOf p.1 ++ muOf p.1)))).isEmpty))

def DLang : Language Bool :=
  {z | ∃ w : List Bool, w.length ≤ 2 ^ (z.length ^ 2) + 2 ∧ RD (z, w) = true}

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.SearchHelpers

open PEqualNP.Search

theorem bits_injective : Function.Injective Nat.bits := by
  intro n m h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

theorem digits_append_inj : ∀ (ds ds' : List Bool) (b b' : Bool) (r r' : List Bool),
    (ds.flatMap fun d => [true, d]) ++ (false :: b :: r) =
      (ds'.flatMap fun d => [true, d]) ++ (false :: b' :: r') →
    ds = ds' ∧ b = b' ∧ r = r' := by
  intro ds
  induction ds with
  | nil =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp_all
    | cons d ds' => simp at h
  | cons d ds ih =>
    intro ds' b b' r r' h
    cases ds' with
    | nil => simp at h
    | cons d' ds' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hd, h⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih ds' b b' r r' h
      exact ⟨by rw [hd, h1], h2, h3⟩

theorem literal_append_inj (l l' : Literal) (r r' : List Bool)
    (h : encodeLiteral l ++ r = encodeLiteral l' ++ r') : l = l' ∧ r = r' := by
  obtain ⟨i, b⟩ := l
  obtain ⟨i', b'⟩ := l'
  simp only [encodeLiteral, List.cons_append, List.nil_append, List.append_assoc,
    List.cons.injEq, true_and] at h
  obtain ⟨hb, h⟩ := h
  obtain ⟨h1, -, h3⟩ := digits_append_inj _ _ true true r r' h
  exact ⟨by rw [bits_injective h1, hb], h3⟩

theorem encodeLiteral_head (l : Literal) (r : List Bool) :
    ∃ t, encodeLiteral l ++ r = true :: t := ⟨_, rfl⟩

theorem clause_append_inj : ∀ (c c' : Clause) (r r' : List Bool),
    encodeClause c ++ r = encodeClause c' ++ r' → c = c' ∧ r = r' := by
  intro c
  induction c with
  | nil =>
    intro c' r r' h
    cases c' with
    | nil => simpa [encodeClause] using h
    | cons l' c' =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l' (c'.flatMap encodeLiteral ++ [false, false] ++ r')
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
  | cons l c ih =>
    intro c' r r' h
    cases c' with
    | nil =>
      exfalso
      obtain ⟨t, ht⟩ := encodeLiteral_head l (c.flatMap encodeLiteral ++ [false, false] ++ r)
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h ht
      rw [ht] at h
      simp at h
    | cons l' c' =>
      simp only [encodeClause, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := literal_append_inj l l' _ _ h
      have := ih c' r r' (by simpa [encodeClause, List.append_assoc] using h2)
      exact ⟨by rw [h1, this.1], this.2⟩

theorem encodeCNF_injective : Function.Injective encodeCNF := by
  intro φ
  induction φ with
  | nil =>
    intro φ' h
    cases φ' with
    | nil => rfl
    | cons c φ' => simp [encodeCNF, encodeClause] at h
  | cons c φ ih =>
    intro φ' h
    cases φ' with
    | nil => simp [encodeCNF, encodeClause] at h
    | cons c' φ' =>
      simp only [encodeCNF, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := clause_append_inj c c' _ _ h
      rw [h1, ih h2]

end PEqualNP.Library.SearchHelpers

end

section

namespace PEqualNP.Library.SearchHelpers.SatV

open PEqualNP.Search PEqualNP.Library.Universal

def headI : List Bool → List Bool
  | [] => []
  | [a] => [a]
  | true :: d :: r => true :: d :: headI r
  | false :: d :: _ => [false, d]

def dropI : List Bool → List Bool
  | [] => []
  | [_] => []
  | true :: _ :: r => dropI r
  | false :: _ :: r => r

def polB : List Bool → Bool
  | _ :: b :: _ => b
  | _ => false

def isEnd : List Bool → Bool
  | false :: false :: _ => true
  | _ => false

def vcode (i : ℕ) : List Bool := (i.bits.flatMap fun d => [true, d]) ++ [false, true]

inductive WS : Type
  | a | b | c | d | abT | abF | cT | cF | dead
  deriving DecidableEq

instance : Fintype WS :=
  ⟨{.a, .b, .c, .d, .abT, .abF, .cT, .cF, .dead}, fun q => by cases q <;> simp⟩

def wfD : WS → Bool → WS
  | .a, true => .abT
  | .a, false => .abF
  | .b, true => .abT
  | .b, false => .abF
  | .abT, _ => .c
  | .abF, false => .a
  | .abF, true => .dead
  | .c, true => .cT
  | .c, false => .cF
  | .d, true => .cT
  | .d, false => .dead
  | .cT, true => .c
  | .cT, false => .d
  | .cF, true => .b
  | .cF, false => .dead
  | .dead, _ => .dead

def wfB (x : List Bool) : Bool := decide (x.foldl wfD .a = .a)

def memStep (s : List Bool) : List Bool :=
  pairB (unpairB s).1 (pairB (dropI (unpairB (unpairB s).2).1)
    ((unpairB (unpairB s).2).2 ++
      bflag (decide (headI (unpairB (unpairB s).2).1 = (unpairB s).1))))

def memB (c w : List Bool) : Bool :=
  !(unpairB (unpairB (memStep^[w.length] (pairB c (pairB w [])))).2).2.isEmpty

def litB (it w : List Bool) : Bool :=
  (memB it.tail.tail w && polB it) || (!memB it.tail.tail w && !polB it)

def stW (s : List Bool) : List Bool := (unpairB s).1

def stR (s : List Bool) : List Bool := (unpairB (unpairB s).2).1

def stC (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s).2).2).1

def stB (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s).2).2).2

def evStep (s : List Bool) : List Bool :=
  pairB (stW s) (pairB (dropI (stR s))
    (sel (bflag (isEnd (stR s)))
      (pairB (stC s ++ bflag (litB (headI (stR s)) (stW s))) (stB s))
      (pairB [] (stB s ++ bflag (stC s).isEmpty))))

def evalB (x w : List Bool) : Bool :=
  (stB (evStep^[x.length] (pairB w (pairB x (pairB [] []))))).isEmpty

def SV (p : List Bool × List Bool) : Bool := wfB p.1 && evalB p.1 p.2

end PEqualNP.Library.SearchHelpers.SatV

end

section

namespace PEqualNP.Library.SearchHelpers.SatV

open PEqualNP.Search PEqualNP.Library.Universal PEqualNP.Library.Machines

theorem headI_dropI : ∀ s : List Bool, headI s ++ dropI s = s
  | [] => rfl
  | [_] => rfl
  | true :: d :: r => by simp [headI, dropI, headI_dropI r]
  | false :: d :: r => by simp [headI, dropI]

theorem dropI_length (s : List Bool) : (dropI s).length ≤ s.length := by
  have h := congrArg List.length (headI_dropI s)
  simp only [List.length_append] at h
  omega

theorem headI_digits (ds : List Bool) (b : Bool) (r : List Bool) :
    headI ((ds.flatMap fun d => [true, d]) ++ false :: b :: r) =
      (ds.flatMap fun d => [true, d]) ++ [false, b] := by
  induction ds with
  | nil => simp [headI]
  | cons d ds ih => simpa [headI] using ih

theorem dropI_digits (ds : List Bool) (b : Bool) (r : List Bool) :
    dropI ((ds.flatMap fun d => [true, d]) ++ false :: b :: r) = r := by
  induction ds with
  | nil => simp [dropI]
  | cons d ds ih => simpa [dropI] using ih

theorem headI_vcode (i : ℕ) (r : List Bool) : headI (vcode i ++ r) = vcode i := by
  simpa [vcode] using headI_digits i.bits true r

theorem dropI_vcode (i : ℕ) (r : List Bool) : dropI (vcode i ++ r) = r := by
  simpa [vcode] using dropI_digits i.bits true r

theorem encodeLiteral_eq (l : Literal) : encodeLiteral l = true :: l.2 :: vcode l.1 := by
  simp [encodeLiteral, vcode]

theorem headI_lit (l : Literal) (r : List Bool) :
    headI (encodeLiteral l ++ r) = encodeLiteral l := by
  simp [encodeLiteral_eq, headI, headI_vcode]

theorem dropI_lit (l : Literal) (r : List Bool) : dropI (encodeLiteral l ++ r) = r := by
  simp [encodeLiteral_eq, dropI, dropI_vcode]

theorem vcode_ne_nil (i : ℕ) : vcode i ≠ [] := by simp [vcode]

theorem vcode_length_pos (i : ℕ) : 1 ≤ (vcode i).length := by simp [vcode]

theorem vcode_injective : Function.Injective vcode := by
  intro i j h
  have h' : (i.bits.flatMap fun d => [true, d]) ++ (false :: true :: []) =
      (j.bits.flatMap fun d => [true, d]) ++ (false :: true :: []) := h
  exact bits_injective (digits_append_inj _ _ true true [] [] h').1

theorem vcode_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    vcode (Nat.bit b n) = true :: b :: vcode n := by
  simp [vcode, Nat.bits_append_bit n b h]

theorem vcode_zero : vcode 0 = [false, true] := by simp [vcode]

theorem bflag_length (b : Bool) : (bflag b).length ≤ 1 := by cases b <;> simp [bflag]

theorem memStep_length (s : List Bool) : (memStep s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := dropI_length (unpairB (unpairB s).2).1
  have h4 := bflag_length (decide (headI (unpairB (unpairB s).2).1 = (unpairB s).1))
  simp only [memStep, pairB_length, List.length_append]
  omega

theorem evStep_length (s : List Bool) : (evStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have h4 := dropI_length (stR s)
  have h5 := bflag_length (litB (headI (stR s)) (stW s))
  have h6 := bflag_length (stC s).isEmpty
  have h7 := sel_length (bflag (isEnd (stR s)))
    (pairB (stC s ++ bflag (litB (headI (stR s)) (stW s))) (stB s))
    (pairB [] (stB s ++ bflag (stC s).isEmpty)) (2 * (stC s).length + (stB s).length + 3)
    (by simp only [pairB_length, List.length_append]; omega)
    (by simp only [pairB_length, List.length_append, List.length_nil]; omega)
  simp only [evStep, pairB_length]
  simp only [stW, stR, stC, stB] at h4 h7 ⊢
  omega

theorem memStep_pair (c r fl : List Bool) :
    memStep (pairB c (pairB r fl)) =
      pairB c (pairB (dropI r) (fl ++ bflag (decide (headI r = c)))) := by
  simp [memStep, unpairB_pairB]

theorem memStep_iter (c : List Bool) (k : ℕ) : ∀ r fl : List Bool, ∃ fl' : List Bool,
    memStep^[k] (pairB c (pairB r fl)) = pairB c (pairB (dropI^[k] r) fl') ∧
      (fl' = [] ↔ fl = [] ∧ ∀ j < k, headI (dropI^[j] r) ≠ c) := by
  induction k with
  | zero => intro r fl; exact ⟨fl, rfl, by simp⟩
  | succ k ih =>
    intro r fl
    obtain ⟨fl', h1, h2⟩ := ih (dropI r) (fl ++ bflag (decide (headI r = c)))
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, memStep_pair, h1, Function.iterate_succ_apply]
    · rw [h2, List.append_eq_nil_iff, bflag_eq_nil, Nat.forall_lt_succ_left, and_assoc]
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply,
        decide_eq_false_iff_not]

theorem memB_iff (c w : List Bool) :
    memB c w = true ↔ ∃ j < w.length, headI (dropI^[j] w) = c := by
  obtain ⟨fl', h1, h2⟩ := memStep_iter c w.length w []
  rw [memB, h1]
  simp only [unpairB_pairB, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, h2, true_and,
    not_forall, not_not, exists_prop]

def asg (w : List Bool) : Assignment := fun i => memB (vcode i) w

theorem litB_lit (l : Literal) (w : List Bool) :
    litB (encodeLiteral l) w = Literal.eval (asg w) l := by
  obtain ⟨i, b⟩ := l
  simp only [litB, encodeLiteral_eq, List.tail_cons, polB, Literal.eval, asg]
  cases memB (vcode i) w <;> cases b <;> rfl

theorem isEnd_lit (l : Literal) (r : List Bool) : isEnd (encodeLiteral l ++ r) = false := by
  simp [encodeLiteral_eq, isEnd]

theorem evStep_lit (w : List Bool) (l : Literal) (r cl bad : List Bool) :
    evStep (pairB w (pairB (encodeLiteral l ++ r) (pairB cl bad))) =
      pairB w (pairB r (pairB (cl ++ bflag (Literal.eval (asg w) l)) bad)) := by
  simp [evStep, stW, stR, stC, stB, unpairB_pairB, isEnd_lit, headI_lit, dropI_lit, litB_lit,
    bflag]

theorem evStep_end (w r cl bad : List Bool) :
    evStep (pairB w (pairB (false :: false :: r) (pairB cl bad))) =
      pairB w (pairB r (pairB [] (bad ++ bflag cl.isEmpty))) := by
  simp [evStep, stW, stR, stC, stB, unpairB_pairB, isEnd, dropI, bflag]

theorem evStep_nil (w cl bad : List Bool) :
    evStep (pairB w (pairB [] (pairB cl bad))) =
      pairB w (pairB [] (pairB (cl ++ bflag (litB [] w)) bad)) := by
  simp [evStep, stW, stR, stC, stB, unpairB_pairB, isEnd, dropI, headI, bflag]

theorem evStep_nil_iter (w bad : List Bool) (k : ℕ) : ∀ cl : List Bool, ∃ cl' : List Bool,
    evStep^[k] (pairB w (pairB [] (pairB cl bad))) = pairB w (pairB [] (pairB cl' bad)) := by
  induction k with
  | zero => intro cl; exact ⟨cl, rfl⟩
  | succ k ih =>
    intro cl
    obtain ⟨cl', h⟩ := ih (cl ++ bflag (litB [] w))
    exact ⟨cl', by rw [Function.iterate_succ_apply, evStep_nil, h]⟩

theorem evStep_clause (w : List Bool) : ∀ (c : Clause) (r cl bad : List Bool),
    ∃ bad' : List Bool,
      evStep^[c.length + 1] (pairB w (pairB (encodeClause c ++ r) (pairB cl bad))) =
        pairB w (pairB r (pairB [] bad')) ∧
      (bad' = [] ↔ bad = [] ∧ (cl ≠ [] ∨ Clause.eval (asg w) c = true)) := by
  intro c
  induction c with
  | nil =>
    intro r cl bad
    refine ⟨bad ++ bflag cl.isEmpty, ?_, ?_⟩
    · simp [encodeClause, evStep_end]
    · simp [bflag_eq_nil, Clause.eval]
  | cons l c ih =>
    intro r cl bad
    obtain ⟨bad', h1, h2⟩ := ih r (cl ++ bflag (Literal.eval (asg w) l)) bad
    refine ⟨bad', ?_, ?_⟩
    · have e : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
        simp [encodeClause]
      rw [List.length_cons, Function.iterate_succ_apply, e, evStep_lit, h1]
    · rw [h2]
      simp only [ne_eq, List.append_eq_nil_iff, bflag_eq_nil, Clause.eval, List.any_cons,
        Bool.or_eq_true]
      cases Literal.eval (asg w) l <;> simp

def nIt : CNF → ℕ
  | [] => 0
  | c :: φ => nIt φ + (c.length + 1)

theorem evStep_cnf (w : List Bool) : ∀ (φ : CNF) (bad : List Bool), ∃ bad' : List Bool,
    evStep^[nIt φ] (pairB w (pairB (encodeCNF φ) (pairB [] bad))) =
        pairB w (pairB [] (pairB [] bad')) ∧
      (bad' = [] ↔ bad = [] ∧ CNF.eval (asg w) φ = true) := by
  intro φ
  induction φ with
  | nil => intro bad; exact ⟨bad, rfl, by simp [CNF.eval]⟩
  | cons c φ ih =>
    intro bad
    obtain ⟨bad1, h1, h2⟩ := evStep_clause w c (encodeCNF φ) [] bad
    obtain ⟨bad', h3, h4⟩ := ih bad1
    refine ⟨bad', ?_, ?_⟩
    · have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
      rw [nIt, Function.iterate_add_apply, e, h1, h3]
    · rw [h4, h2]
      simp [CNF.eval, and_assoc]

theorem length_le_flatMap_lit (c : Clause) : c.length ≤ (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih => simp [encodeLiteral_eq]; omega

theorem nIt_le (φ : CNF) : nIt φ ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [nIt]
  | cons c φ ih =>
    have := length_le_flatMap_lit c
    simp only [nIt, encodeCNF, encodeClause, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at ih ⊢
    omega

theorem evalB_enc (φ : CNF) (w : List Bool) :
    evalB (encodeCNF φ) w = CNF.eval (asg w) φ := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le' (nIt_le φ)
  obtain ⟨bad', h1, h2⟩ := evStep_cnf w φ []
  obtain ⟨cl', h3⟩ := evStep_nil_iter w bad' e []
  rw [evalB, he, Function.iterate_add_apply, h1, h3]
  simp only [stB, unpairB_pairB]
  rw [Bool.eq_iff_iff, List.isEmpty_iff, h2]
  simp

theorem foldl_dead (s : List Bool) : s.foldl wfD .dead = .dead := by
  induction s with
  | nil => rfl
  | cons x s ih => simpa [wfD] using ih

theorem foldl_vcode (n : ℕ) : ∀ r : List Bool,
    (vcode n ++ r).foldl wfD .c = r.foldl wfD .b ∧
      (n ≠ 0 → (vcode n ++ r).foldl wfD .d = r.foldl wfD .b) := by
  induction n using Nat.binaryRec' with
  | zero => intro r; simp [vcode_zero, wfD]
  | bit b n h ih =>
    intro r
    obtain ⟨ih1, ih2⟩ := ih r
    rw [vcode_bit b n h]
    cases b
    · have hn : n ≠ 0 := fun h0 => by simpa using h h0
      simp [wfD, ih2 hn]
    · simp [wfD, ih1]

theorem foldl_lit (l : Literal) (r : List Bool) :
    (encodeLiteral l ++ r).foldl wfD .a = r.foldl wfD .b ∧
      (encodeLiteral l ++ r).foldl wfD .b = r.foldl wfD .b := by
  simp [encodeLiteral_eq, wfD, (foldl_vcode l.1 r).1]

theorem foldl_clause (c : Clause) (r : List Bool) :
    (encodeClause c ++ r).foldl wfD .a = r.foldl wfD .a ∧
      (encodeClause c ++ r).foldl wfD .b = r.foldl wfD .a := by
  induction c with
  | nil => simp [encodeClause, wfD]
  | cons l c ih =>
    have e : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
      simp [encodeClause]
    rw [e, (foldl_lit l _).1, (foldl_lit l _).2, ih.2]
    exact ⟨rfl, rfl⟩

theorem foldl_cnf (φ : CNF) : (encodeCNF φ).foldl wfD .a = .a := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
    rw [e, (foldl_clause c _).1, ih]

def Good : WS → List Bool → Prop
  | .a, s => ∃ φ : CNF, s = encodeCNF φ
  | .b, s => ∃ (c : Clause) (φ : CNF), s = encodeClause c ++ encodeCNF φ
  | .c, s => ∃ (n : ℕ) (c : Clause) (φ : CNF), s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | .d, s => ∃ (n : ℕ) (c : Clause) (φ : CNF),
      n ≠ 0 ∧ s = vcode n ++ (encodeClause c ++ encodeCNF φ)
  | _, _ => True

theorem enc_cons_cons (n : ℕ) (p : Bool) (c : Clause) (φ : CNF) :
    true :: p :: (vcode n ++ (encodeClause c ++ encodeCNF φ)) =
      encodeClause ((n, p) :: c) ++ encodeCNF φ := by
  simp [encodeClause, encodeLiteral_eq]

theorem good_of_accept : ∀ (s : List Bool) (q : WS), s.foldl wfD q = .a → Good q s
  | [], q, h => by
    cases q <;> first | trivial | exact ⟨[], rfl⟩
  | [x], q, h => by
    cases q <;> first | trivial | (cases x <;> simp [wfD] at h)
  | x :: y :: r, q, h => by
    have ih := good_of_accept r
    cases q
    case abT | abF | cT | cF | dead => trivial
    case a =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h
          exact ⟨[] :: φ, by simp [encodeCNF, encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨((n, y) :: c) :: φ, by rw [enc_cons_cons]; simp [encodeCNF]⟩
    case b =>
      cases x
      · cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
        · obtain ⟨φ, rfl⟩ := ih _ h
          exact ⟨[], φ, by simp [encodeClause]⟩
        · exact absurd h (by decide)
      · simp only [List.foldl_cons, wfD] at h
        obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨(n, y) :: c, φ, enc_cons_cons _ _ _ _⟩
    case c =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · obtain ⟨c, φ, rfl⟩ := ih _ h
        exact ⟨0, c, φ, by simp [vcode_zero]⟩
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩
    case d =>
      cases x <;> cases y <;> simp only [List.foldl_cons, wfD, foldl_dead] at h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · obtain ⟨n, c, φ, hn, rfl⟩ := ih _ h
        exact ⟨Nat.bit false n, c, φ, by simp [hn],
          by rw [vcode_bit false n (fun h0 => absurd h0 hn)]; rfl⟩
      · obtain ⟨n, c, φ, rfl⟩ := ih _ h
        exact ⟨Nat.bit true n, c, φ, by simp,
          by rw [vcode_bit true n (fun _ => rfl)]; rfl⟩

theorem wfB_iff (x : List Bool) : wfB x = true ↔ ∃ φ : CNF, encodeCNF φ = x := by
  rw [wfB, decide_eq_true_iff]
  constructor
  · intro h
    obtain ⟨φ, rfl⟩ := good_of_accept x .a h
    exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact foldl_cnf φ

theorem wfB_eq_fstRun (x : List Bool) :
    bflag (wfB x) =
      fstRun (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
        (fun q => if q = WS.a then some true else none) WS.a x := by
  have key : ∀ (s : List Bool) (q : WS),
      fstRun (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
        (fun q => if q = WS.a then some true else none) q s =
      bflag (decide (s.foldl wfD q = .a)) := by
    intro s
    induction s with
    | nil => intro q; by_cases hq : q = .a <;> simp [fstRun, bflag, hq]
    | cons a s ih =>
      intro q
      simp only [fstRun, Option.toList_none, List.nil_append, List.foldl_cons]
      exact ih _
  rw [key, wfB]

theorem SV_iff (x w : List Bool) :
    SV (x, w) = true ↔ ∃ φ : CNF, encodeCNF φ = x ∧ CNF.eval (asg w) φ = true := by
  simp only [SV, Bool.and_eq_true, wfB_iff]
  constructor
  · rintro ⟨⟨φ, rfl⟩, h⟩
    exact ⟨φ, rfl, by rw [← evalB_enc]; exact h⟩
  · rintro ⟨φ, rfl, h⟩
    exact ⟨⟨φ, rfl⟩, by rw [evalB_enc]; exact h⟩

theorem dropI_iter_nil (j : ℕ) : dropI^[j] [] = [] := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact ih

theorem dropI_iter_codes (j : ℕ) : ∀ vs : List ℕ,
    dropI^[j] (vs.flatMap vcode) = (vs.drop j).flatMap vcode := by
  induction j with
  | zero => intro vs; rfl
  | succ j ih =>
    intro vs
    cases vs with
    | nil => simpa using dropI_iter_nil (j + 1)
    | cons v vs =>
      rw [Function.iterate_succ_apply, List.flatMap_cons, dropI_vcode, ih]
      rfl

theorem length_le_flatMap_vcode (vs : List ℕ) : vs.length ≤ (vs.flatMap vcode).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have := vcode_length_pos v
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem asg_codes (vs : List ℕ) (i : ℕ) : asg (vs.flatMap vcode) i = true ↔ i ∈ vs := by
  rw [asg, memB_iff]
  constructor
  · rintro ⟨j, -, h⟩
    rw [dropI_iter_codes] at h
    cases hd : vs.drop j with
    | nil =>
      rw [hd] at h
      exact absurd h.symm (vcode_ne_nil i)
    | cons v t =>
      rw [hd, List.flatMap_cons, headI_vcode] at h
      have hv : v ∈ vs.drop j := by rw [hd]; exact List.mem_cons_self
      rw [← vcode_injective h]
      exact List.mem_of_mem_drop hv
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    refine ⟨j, lt_of_lt_of_le hj (length_le_flatMap_vcode vs), ?_⟩
    rw [dropI_iter_codes, List.drop_eq_getElem_cons hj, List.flatMap_cons, headI_vcode]

def trueVars (σ : Assignment) (φ : CNF) : List ℕ :=
  ((φ.flatMap id).map Prod.fst).filter σ

def wit (σ : Assignment) (φ : CNF) : List Bool := (trueVars σ φ).flatMap vcode

theorem length_filter_flatMap {α : Type} (p : α → Bool) (f : α → List Bool) (l : List α) :
    ((l.filter p).flatMap f).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons]
    split
    · simp only [List.flatMap_cons, List.length_append]; omega
    · simp only [List.flatMap_cons, List.length_append]; omega

theorem length_codes_clause (c : Clause) :
    ((c.map Prod.fst).flatMap vcode).length ≤ (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, encodeLiteral_eq,
      List.length_cons]
    omega

theorem length_codes_cnf (φ : CNF) :
    (((φ.flatMap id).map Prod.fst).flatMap vcode).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
    have := length_codes_clause c
    simp only [List.flatMap_cons, id_eq, List.map_append, List.flatMap_append,
      List.length_append, encodeCNF, encodeClause, List.length_cons, List.length_nil] at ih ⊢
    omega

theorem wit_length (σ : Assignment) (φ : CNF) : (wit σ φ).length ≤ (encodeCNF φ).length :=
  (length_filter_flatMap _ _ _).trans (length_codes_cnf φ)

theorem eval_wit (σ : Assignment) (φ : CNF) :
    CNF.eval (asg (wit σ φ)) φ = CNF.eval σ φ := by
  have key : ∀ c ∈ φ, ∀ l ∈ c, Literal.eval (asg (wit σ φ)) l = Literal.eval σ l := by
    intro c hc l hl
    have hmem : l.1 ∈ (φ.flatMap id).map Prod.fst :=
      List.mem_map.2 ⟨l, List.mem_flatMap.2 ⟨c, hc, hl⟩, rfl⟩
    have : asg (wit σ φ) l.1 = σ l.1 := by
      rw [Bool.eq_iff_iff, wit, asg_codes, trueVars, List.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
    simp [Literal.eval, this]
  rw [Bool.eq_iff_iff]
  simp only [CNF.eval, Clause.eval, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h c hc
    obtain ⟨l, hl, hv⟩ := h c hc
    exact ⟨l, hl, by rw [← key c hc l hl]; exact hv⟩
  · intro h c hc
    obtain ⟨l, hl, hv⟩ := h c hc
    exact ⟨l, hl, by rw [key c hc l hl]; exact hv⟩

theorem SV_spec (x : List Bool) :
    x ∈ PEqualNP.Search.SAT ↔ ∃ w : List Bool, w.length ≤ x.length ∧ SV (x, w) = true := by
  constructor
  · rintro ⟨φ, rfl, σ, hσ⟩
    exact ⟨wit σ φ, wit_length σ φ, (SV_iff _ _).2 ⟨φ, rfl, by rw [eval_wit]; exact hσ⟩⟩
  · rintro ⟨w, -, h⟩
    obtain ⟨φ, hφ, hv⟩ := (SV_iff _ _).1 h
    exact ⟨φ, hφ, asg w, hv⟩

theorem SAT_in_NP_of (h : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
    Computability.encodeBool SV) : PEqualNP.Search.SAT ∈ PEqualNP.Library.NP := by
  refine ⟨{p | SV p = true}, Polynomial.X, ⟨SV, fun _ => Iff.rfl, h⟩, fun x => ?_⟩
  rw [SV_spec]
  simp

end PEqualNP.Library.SearchHelpers.SatV

end

section

namespace PEqualNP.Library.Machines

open Turing

section update

variable {ι : Type} [DecidableEq ι] {β : ι → Type}

theorem update3_fst (E : ∀ i, β i) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z := by
  rw [Function.update_comm hac.symm, Function.update_comm hab.symm, Function.update_idem]

theorem update3_snd (E : ∀ i, β i) {a b c : ι} (hbc : b ≠ c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z := by
  rw [Function.update_comm hbc.symm, Function.update_idem]

end update

variable (M1 M2 : FinTM2)

abbrev CK : Type := Option (M1.K ⊕ M2.K)

abbrev CΓ : CK M1 M2 → Type
  | none => M2.Γ M2.k₀
  | some (Sum.inl k) => M1.Γ k
  | some (Sum.inr k) => M2.Γ k

abbrev CΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Bool

abbrev Cσ : Type := M1.σ × M2.σ × Option (M2.Γ M2.k₀)

variable {M1 M2}

def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt

variable (M1 M2)

def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o => (s.1, s.2.1, o.map φ))
      (.branch (fun s => s.2.2.isSome)
        (.push none (fun s => s.2.2.getD d) (.goto fun _ => Sum.inr (Sum.inr false)))
        (.goto fun _ => Sum.inr (Sum.inr true)))

def tB : Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o => (s.1, s.2.1, o))
      (.branch (fun s => s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s => s.2.2.getD d)
          (.goto fun _ => Sum.inr (Sum.inr true)))
        (.goto fun _ => Sum.inr (Sum.inl M2.main)))

def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr false) => tA M1 M2 φ d
  | Sum.inr (Sum.inr true) => tB M1 M2 d

def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) : FinTM2 :=
  haveI := M1.kFin
  haveI := M2.kFin
  haveI := M1.ΛFin
  haveI := M2.ΛFin
  haveI := M1.σFin
  haveI := M2.σFin
  haveI := M2.Γk₀Fin
  { K := CK M1 M2
    k₀ := some (Sum.inl M1.k₀)
    k₁ := some (Sum.inr M2.k₁)
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main := Sum.inl M1.main
    σ := Cσ M1 M2
    initialState := (M1.initialState, M2.initialState, none)
    Γk₀Fin := M1.Γk₀Fin
    m := prog M1 M2 φ d }

variable {M1 M2}

def embStk1 (S : ∀ k, List (M1.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl k) => S k
  | some (Sum.inr _) => []

def embStk2 (S : ∀ k, List (M2.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl _) => []
  | some (Sum.inr k) => S k

theorem embStk1_update (S : ∀ k, List (M1.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
    (embStk1 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk1 S) (some (Sum.inl k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem embStk2_update (S : ∀ k, List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
    (embStk2 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk2 S) (some (Sum.inr k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]

theorem embStk1_nil :
    (embStk1 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

theorem embStk2_nil :
    (embStk2 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

def emb1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, w), embStk1 c.stk⟩

def emb2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (u, c.var, b), embStk2 c.stk⟩

theorem sim1 (w : M2.σ × Option (M2.Γ M2.k₀)) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
    (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Cσ M1 M2) (embStk1 S) = emb1 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk1_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk1_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem sim2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
    (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u, v, b) : Cσ M1 M2) (embStk2 S) = emb2 u b (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk2_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk2_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀))

theorem step1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c) = some (emb1 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)

theorem step2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c) = some (emb2 u b c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)

def st (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) : ∀ k, List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u

theorem st_fst (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) = l := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem st_snd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) none = t := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem st_thd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) = u := by
  unfold st
  rw [Function.update_self]

theorem st_set_fst (l l' : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l' = st l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem st_set_snd (l : List (M1.Γ M1.k₁)) (t t' u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) none t' = st l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem st_set_thd (l : List (M1.Γ M1.k₁)) (t u u' : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u' = st l t u' :=
  Function.update_idem _ _ _

theorem st_start (l : List (M1.Γ M1.k₁)) :
    (st l [] [] : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l := by
  unfold st
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem st_end (u : List (M2.Γ M2.k₀)) :
    (st [] [] u : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u := by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

variable {M1 M2 : FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)

abbrev CCfg (M1 M2 : FinTM2) : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)

theorem stepA_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M1.Γ M1.k₁) (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true,
    Option.getD_some]
  rw [st_set_fst, st_snd, st_set_snd]

theorem stepA_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] t u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [st_set_fst]

theorem stepB_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M2.Γ M2.k₀) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [st_set_snd, st_thd, st_set_thd]

theorem stepB_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] [] u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] u⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [st_set_snd]

theorem loopA (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (u : List (M2.Γ M2.k₀)) :
    ∀ (l : List (M1.Γ M1.k₁)) (t : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length + 1]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st l t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] ((l.map φ).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact stepA_nil φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ :=
      stepA_cons φ dd v1 v2 b x l t u
    rw [e, ih]
    simp

theorem loopB (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) :
    ∀ (t u : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length + 1]
          (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact stepB_nil φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ :=
      stepB_cons φ dd v1 v2 b x t u
    rw [e, ih]
    simp

theorem transfer (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (v1 : M1.σ) (v2 : M2.σ) (o : List (M1.Γ M1.k₁)) :
    ∃ n, n ≤ 2 * o.length + 2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, none),
            Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none),
          Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩ := by
  cases d with
  | none =>
    have := hd rfl
    have ho : o = [] := by
      cases o with
      | nil => rfl
      | cons x _ => exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1, by omega, ?_⟩
    show some _ = some _
    simp only [prog, tA, TM2.stepAux, List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl, Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse ++ []).length + 1 + (o.length + 1), by simp; omega, ?_⟩
    rw [Function.iterate_add_apply, ← st_start, loopA, loopB, ← st_end]
    simp

theorem emb1_init (d : Option (M2.Γ M2.k₀)) (i : List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState, none) (initList M1 i) = initList (comp M1 M2 φ d) i := by
  rw [initList_eq]
  refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb1_halt (w : M2.σ × Option (M2.Γ M2.k₀)) (o : List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)), (M1.initialState, w),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2) := by
  rw [haltList_eq]
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb2_init (u : M1.σ) (i : List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)), (u, M2.initialState, none),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2) := by
  rw [initList_eq]
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem emb2_halt (d : Option (M2.Γ M2.k₀)) (o : List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o) = haltList (comp M1 M2 φ d) o := by
  rw [haltList_eq]
  refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem comp_run (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (s1 s2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n, n ≤ s1 + (2 * o1.length + 2) + s2 ∧ o1.length ≤ i.length + maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2) := by
  have p1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState, none)) (step1 φ d _) s1 _ _ h1
  rw [emb1_init φ d, emb1_halt] at p1
  obtain ⟨nt, hnt, pt⟩ := transfer φ d hd M1.initialState M2.initialState o1
  have p2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [emb2_init, emb2_halt φ d] at p2
  refine ⟨s2 + (nt + s1), by omega, ?_, ?_⟩
  · have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; simp
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, p1, pt, p2]
    rfl

theorem comp_polyTime {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1 : TM2ComputableInPolyTime ea eb f)
    (c2 : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a => g (f a))) := by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : Polynomial ℕ :=
    c1.time + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time)
  have key : ∀ a, ∃ n, n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, hlen, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 := r1.steps_le_m
    have b2 := r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul : maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time := Nat.mul_le_mul_left _ b1
    have b3 : Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length + maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time := eval_mono _ (by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

variable {Γ₀ Γ₁ : Type}

abbrev FΓ (Γ₀ Γ₁ : Type) : Option Bool → Type
  | some false => Γ₀
  | none => Option Γ₀
  | some true => Γ₁

def fmProg (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push none (fun s => s) (.goto fun _ => false))
        (.goto fun _ => true))
  | true =>
    .pop none (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.branch (fun s => (s.bind φ).isSome)
          (match d with
            | some dd => .push (some true) (fun s => (s.bind φ).getD dd) (.goto fun _ => true)
            | none => .goto fun _ => true)
          (.goto fun _ => true))
        .halt)

def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := Option Bool
  k₀ := some false
  k₁ := some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main := false
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := fmProg φ d

def fst3 (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some false) l) none t) (some true) u

theorem fst3_fst (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some false) = l := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem fst3_snd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u none = t := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem fst3_thd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some true) = u := by
  unfold fst3
  rw [Function.update_self]

theorem fst3_set_fst (l l' : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem fst3_set_snd (l : List Γ₀) (t t' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) none t' = fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem fst3_set_thd (l : List Γ₀) (t : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
  Function.update_idem _ _ _

theorem fst3_start (l : List Γ₀) :
    (fst3 l [] [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some false) l := by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem fst3_end (u : List Γ₁) :
    (fst3 [] [] u : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some true) u := by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

abbrev FCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)

variable (φ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem fmA_cons (b : Option Γ₀) (x : Γ₀) (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some false, some x, fst3 l (some x :: t) u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
  rw [fst3_set_fst, fst3_snd, fst3_set_snd]

theorem fmA_nil (b : Option Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 [] t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, none, fst3 [] t u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [fst3_set_fst]

theorem fmB_cons (hd : d = none → ∀ x, φ x = none) (b : Option Γ₀) (x : Γ₀)
    (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] (some x :: t) u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, some x, fst3 [] t ((φ x).toList ++ u)⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true, Option.bind_some]
  rw [fst3_set_snd]
  cases hφ : φ x with
  | none => simp
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some, Bool.cond_true, TM2.stepAux,
        Option.toList_some, List.singleton_append]
      rw [fst3_thd, fst3_set_thd]
      simp [hφ]

theorem fmB_nil (b : Option Γ₀) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] [] u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨none, none, fst3 [] [] u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]

theorem fmLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Option Γ₀)) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length + 1]
          (some (⟨some false, b, fst3 l t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, none, fst3 [] (l.reverse.map some ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact fmA_nil φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some false, some x, fst3 l (some x :: t) u⟩ := fmA_cons φ d b x l t u
    rw [e, ih]
    simp

theorem fmLoopB (hd : d = none → ∀ x, φ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length + 1]
          (some (⟨some true, b, fst3 [] (t.map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨none, none, fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact fmB_nil φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some true, b, fst3 [] ((x :: t).map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, some x, fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ d hd b x (t.map some) u
    rw [e, ih]
    cases hφ : φ x <;> simp [hφ]

theorem fm_run [Fintype Γ₀] (hd : d = none → ∀ x, φ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
        (some (initList (fm φ d) l)) = some (haltList (fm φ d) (l.filterMap φ)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some c)) (initList_eq (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some (⟨some false, none, Function.update (fun _ => []) (some false) l⟩ : FCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply, ← fst3_start, fmLoopA, ← fst3_end]
  have := fmLoopB φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this

theorem filterMap_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : d = none → ∀ x, φ x = none := by
    intro hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := fm φ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := fm_run φ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (fmProg φ d)))^[(ea a).length + 1 +
            ((ea a).length + 1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

inductive TPK : Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq

instance : Fintype TPK :=
  Fintype.ofList [.inp, .t1, .t2, .t3, .out] (fun x => by cases x <;> simp)

inductive TPL : Type
  | a | b | c | e
  deriving DecidableEq

instance : Fintype TPL :=
  Fintype.ofList [.a, .b, .c, .e] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ : Type}

abbrev TPΓ (Γ₀ Γ₁ : Type) : TPK → Type
  | .inp => Γ₀
  | .t1 => Option Γ₀
  | .t2 => Option Γ₀
  | .t3 => Option Γ₀
  | .out => Γ₁

def tpWrite (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) (lbl : TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s => (s.bind φ).isSome)
    (match d with
      | some dd => .push .out (fun s => (s.bind φ).getD dd) (.goto fun _ => lbl)
      | none => .goto fun _ => lbl)
    (.goto fun _ => lbl)

def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .t1 (fun s => s) (.goto fun _ => .a))
        (.goto fun _ => .b))
  | .b =>
    .pop .t1 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t2 (fun s => s) (tpWrite φ₂ d .b))
        (.goto fun _ => .c))
  | .c =>
    .pop .t2 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t3 (fun s => s) (.goto fun _ => .c))
        (.goto fun _ => .e))
  | .e =>
    .pop .t3 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (tpWrite φ₁ d .e)
        .halt)

def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := tpProg φ₁ φ₂ d

def st5 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (TPΓ Γ₀ Γ₁ k)
  | .inp => l
  | .t1 => a
  | .t2 => b
  | .t3 => c
  | .out => u

theorem st5_set_inp (l l' : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .inp l' = st5 l' a b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t1 (l : List Γ₀) (a a' b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t1 a' = st5 l a' b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t2 (l : List Γ₀) (a b b' c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t2 b' = st5 l a b' c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t3 (l : List Γ₀) (a b c c' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t3 c' = st5 l a b c' u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_out (l : List Γ₀) (a b c : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (st5 l a b c u) .out u' = st5 l a b c u' := by
  funext k; cases k <;> simp [st5]

theorem st5_start (l : List Γ₀) :
    (st5 l [] [] [] [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .inp l := by
  funext k; cases k <;> simp [st5]

theorem st5_end (u : List Γ₁) :
    (st5 [] [] [] [] u : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .out u := by
  funext k; cases k <;> simp [st5]

abbrev TPCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)

variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem tpA_cons (s : Option Γ₀) (x : Γ₀) (l : List Γ₀) (a b c : List (Option Γ₀))
    (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp, st5_set_t1]

theorem tpA_nil (s : Option Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 [] a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, none, st5 [] a b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp]

theorem tpB_cons (hd : d = none → ∀ x, φ₂ x = none) (s : Option Γ₀) (x : Γ₀)
    (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] (some x :: a) b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, some x, st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩ := by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2,
        st5_set_out, hφ]

theorem tpB_nil (s : Option Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] [] b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, none, st5 [] [] b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t1]

theorem tpC_cons (s : Option Γ₀) (x : Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] (some x :: b) c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, some x, st5 [] [] b (some x :: c) u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2, st5_set_t3]

theorem tpC_nil (s : Option Γ₀) (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] [] c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, none, st5 [] [] [] c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2]

theorem tpE_cons (hd : d = none → ∀ x, φ₁ x = none) (s : Option Γ₀) (x : Γ₀)
    (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] (some x :: c) u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, some x, st5 [] [] [] c ((φ₁ x).toList ++ u)⟩ := by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, st5_set_out, hφ]

theorem tpE_nil (s : Option Γ₀) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] [] u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨none, none, st5 [] [] [] [] u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t3]

theorem tpLoopA (b c : List (Option Γ₀)) (u : List Γ₁) :
    ∀ (l : List Γ₀) (a : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
          (some (⟨some .a, s, st5 l a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, none, st5 [] (l.reverse.map some ++ a) b c u⟩ := by
  intro l
  induction l with
  | nil => intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := tpA_cons φ₁ φ₂ d s x l a b c u
    rw [e, ih]
    simp

theorem tpLoopB (hd : d = none → ∀ x, φ₂ x = none) (c : List (Option Γ₀)) :
    ∀ (t : List Γ₀) (b : List (Option Γ₀)) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .b, s, st5 [] (t.map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, none,
          st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .b, s, st5 [] ((x :: t).map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, some x, st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
      tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e, ih]
    cases hφ : φ₂ x <;> simp [hφ]

theorem tpLoopC (u : List Γ₁) :
    ∀ (t : List Γ₀) (c : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .c, s, st5 [] [] (t.map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, none, st5 [] [] [] (t.reverse.map some ++ c) u⟩ := by
  intro t
  induction t with
  | nil => intro c s; exact tpC_nil φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .c, s, st5 [] [] ((x :: t).map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, some x, st5 [] [] (t.map some) (some x :: c) u⟩ :=
      tpC_cons φ₁ φ₂ d s x (t.map some) c u
    rw [e, ih]
    simp

theorem tpLoopE (hd : d = none → ∀ x, φ₁ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .e, s, st5 [] [] [] (t.map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨none, none, st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact tpE_nil φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .e, s, st5 [] [] [] ((x :: t).map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, some x, st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
      tpE_cons φ₁ φ₂ d hd s x (t.map some) u
    rw [e, ih]
    cases hφ : φ₁ x <;> simp [hφ]

theorem tp_run [Fintype Γ₀] (hd₁ : d = none → ∀ x, φ₁ x = none)
    (hd₂ : d = none → ∀ x, φ₂ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
        (l.length + 1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 +
    (l.length + 1) + (l.length + 1) + (l.length + 1)]
    (some c)) (initList_eq (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (haltList_eq (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
      (l.length + 1)]
    (some (⟨some .a, none, Function.update (fun _ => []) .inp l⟩ : TPCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) .out
      (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)
  have hA : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .a, none, st5 l [] [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ := by
    simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
  have hB : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ := by
    have := tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ := by
    simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none, none, st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ := by
    have := tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    ← st5_start, hA, hB, hC, hE, st5_end]

theorem twoPass_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ φ : αΓ → Option βΓ, d = none → ∀ x, φ x = none := by
    intro φ hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1) + ((ea a).length + 1) +
          ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length + 1 +
            ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

inductive FX
  | I | W | T | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.T, FX.O] (fun x => by cases x <;> simp)

inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => Bool ⊕ Bool
  | Sum.inr FX.W => Bool
  | Sum.inr FX.T => Bool
  | Sum.inr FX.O => Bool ⊕ Bool

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (Bool ⊕ Bool)

def bit : Option (Bool ⊕ Bool) → Bool
  | none => false
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b

def isFst : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

variable {M}

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M)

def firstProg (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l => trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (bit s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (bit s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

def firstM (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := firstProg M e₀ e₁ }

variable {M}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) : ∀ k, List (FstΓ M k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.T => t
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w t o) (Sum.inl k) x = fstk (Function.update S k x) i w t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.I) i' = fstk S i' w t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.W) w' = fstk S i w' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_T (t' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.T) t' = fstk S i w t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.O) o' = fstk S i w t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

abbrev FCfg1 (M : FinTM2) : Type := TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)

def embF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w t o⟩

theorem simF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF q) ((v, b) : Fstσ M) (fstk S i w t o) =
      embF b i w t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) (b : Option (Bool ⊕ Bool))
    (i : List (Bool ⊕ Bool)) (w t : List Bool) (o : List (Bool ⊕ Bool))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M e₀ e₁) (embF b i w t o c) = some (embF b i w t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

section fstk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k : M.K) : fstk S i w t o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w t o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w t o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_T : fstk S i w t o (Sum.inr FX.T) = t := rfl
@[simp] theorem fstk_O : fstk S i w t o (Sum.inr FX.O) = o := rfl
end fstk

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List Bool) (o : List (Bool ⊕ Bool))

theorem f1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_T, isFst, bit]

theorem f1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isFst, bit]

theorem f1_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 : ∀ (i : List (Bool ⊕ Bool)) (w t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f2_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop2 : ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := f2_cons e₀ e₁ v S w o b a t
    rw [e, ih]; simp

theorem f3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (w : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, bit]

theorem f3_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 : ∀ (w : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w [] o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w
    rw [e, ih]; simp

theorem f4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f4_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, none), fstk (Function.update S M.k₁ []) [] [] t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 : ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := f4_cons e₀ e₁ v S o b y m t
    rw [e, ih]; simp

theorem f5_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_O, bit]

theorem f5_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨none, (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop5 : ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] t o⟩ : FCfg1 M)) =
      some ⟨none, (v, none), fstk S [] [] [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a t
    rw [e, ih]; simp

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

theorem fstk_nil : (fstk (fun _ => []) [] [] [] [] : ∀ k, List (FstΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl

theorem fstk_nil_I (i : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) i [] [] [] : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [fstk_nil])

theorem fstk_nil_O (o : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) [] [] [] o : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [fstk_nil])

theorem embF_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (l : List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w t o⟩ : FCfg1 M) := by
  rw [initList_eq]; rfl

theorem embF_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (m : List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w t o⟩ : FCfg1 M) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem encodePair_left (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem encodePair_right (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem encodePair_length (x w : List Bool) :
    (encodePair (x, w)).length = x.length + w.length := by
  simp [encodePair]

theorem first_run (x w0 : List Bool) (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(encodePair (x, w0)).length + 1]
      (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] (encodePair (x, w0)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M e₀ e₁)))^[
      (encodePair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M e₀ e₁) (encodePair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] []⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁, w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [encodePair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime (f : List Bool → List Bool)
    (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2))) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open PEqualNP.Library

private theorem filterMap_map_some_pv2 {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a, φ (h a) = some (g a)) (l : List α) : (l.map h).filterMap φ = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

private theorem filterMap_map_none_pv1 {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a, φ (h a) = none) (l : List α) : (l.map h).filterMap φ = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg : PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a => g (f a)) := by
  obtain ⟨c1⟩ := hf
  obtain ⟨c2⟩ := hg
  exact comp_polyTime ea eb ec f g c1 c2

theorem cpt_swap :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none_pv1 Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some_pv2 Sum.inr _ Sum.inl (fun _ => rfl) w,
    filterMap_map_some_pv2 Sum.inl _ Sum.inr (fun _ => rfl) x,
    filterMap_map_none_pv1 Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_dup :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (x, x)) := by
  refine twoPass_polyTime _ _ _
    (fun b : Bool => some (Sum.inl b)) (fun b : Bool => some (Sum.inr b)) ?_
  intro x
  have h1 := filterMap_map_some_pv2 (fun b : Bool => b) (fun b : Bool => some (Sum.inl (β := Bool) b))
    Sum.inl (fun _ => rfl) x
  have h2 := filterMap_map_some_pv2 (fun b : Bool => b) (fun b : Bool => some (Sum.inr (α := Bool) b))
    Sum.inr (fun _ => rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair, h1, h2]

theorem cpt_fst :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some_pv2 Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_none_pv1 Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_snd :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none_pv1 Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some_pv2 Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_append :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some_pv2 Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_some_pv2 Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_first {f : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  obtain ⟨c⟩ := hf
  exact first_polyTime f c

theorem cpt_second {g : List Bool → List Bool}
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.1, g p.2)) :=
  cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap

theorem cpt_pair {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (f x, g x)) :=
  cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)

theorem cpt_id :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => x) := by
  refine filterMap_polyTime _ _ _ (fun b : Bool => some b) ?_
  intro x
  have h := filterMap_map_some_pv2 (fun b : Bool => b) (fun b : Bool => some b) (fun b => b)
    (fun _ => rfl) x
  simp only [List.map_id'] at h
  exact h.symm

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open Turing

def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _ => a) (pushList l)

def constListProg (l : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .pop () (fun _ o => o.isSome)
    (.branch (fun s => s)
      (.load (fun _ => false) (.goto fun _ => ()))
      (pushList l.reverse))

def constList (l : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := constListProg l

abbrev CLCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool

theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp

theorem pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
    TM2.stepAux (pushList l) v (fun _ : Unit => S) =
      (⟨none, v, fun _ => l.reverse ++ S⟩ : CLCfg) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    simp only [pushList, TM2.stepAux]
    rw [update_unit, ih]
    simp

theorem constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => x :: a⟩ : CLCfg) =
      some ⟨some (), false, fun _ => a⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp

theorem constList_nil (l : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => []⟩ : CLCfg) =
      some ⟨none, false, fun _ => l⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  rw [pushList_stepAux]
  simp

theorem constList_loop (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (⟨some (), false, fun _ => a⟩ : CLCfg)) =
      some ⟨none, false, fun _ => l⟩ := by
  induction a with
  | nil => exact constList_nil l
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constListProg l))
        (some (⟨some (), false, fun _ => x :: a⟩ : CLCfg)) =
        some ⟨some (), false, fun _ => a⟩ := constList_cons l x a
    rw [e, ih]

theorem constList_run (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (initList (constList l) a)) = some (haltList (constList l) l) := by
  refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some (⟨some (), false, Function.update (fun _ => []) () a⟩ : CLCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () l⟩ : CLCfg)
  rw [update_unit, update_unit]
  exact constList_loop l a

theorem constList_polyTime (l : List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun _ : List Bool => l)) :=
  ⟨{
    tm := constList l
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun a =>
      { steps := a.length + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
        steps_le_m := by simp } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines.Iter

open Turing

inductive IX
  | I | C | T | O
  deriving DecidableEq

instance : Fintype IX :=
  Fintype.ofList [IX.I, IX.C, IX.T, IX.O] (fun x => by cases x <;> simp)

inductive IL
  | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq

instance : Fintype IL :=
  Fintype.ofList [IL.l1, IL.l2, IL.l3, IL.l4, IL.l5, IL.l6] (fun x => by cases x <;> simp)

variable (M : FinTM2)

abbrev ItΓ : M.K ⊕ IX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr IX.I => Bool ⊕ Bool
  | Sum.inr IX.C => Bool
  | Sum.inr IX.T => Bool
  | Sum.inr IX.O => Bool

abbrev ItΛ : Type := M.Λ ⊕ IL

abbrev Itσ : Type := M.σ × Option (Bool ⊕ Bool)

variable {M}

def trI : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trI q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trI q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trI q₁) (trI q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr IL.l4)

variable (M)

def iterProg (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) :
    ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l => trI (M.m l)
  | Sum.inr IL.l1 =>
    .pop (Sum.inr IX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1))
          (.push (Sum.inr IX.C) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l1)))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l2 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr IL.l2))
        (.goto fun _ => Sum.inr IL.l3))
  | Sum.inr IL.l3 =>
    .pop (Sum.inr IX.C) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.goto fun _ => Sum.inl M.main)
        (.goto fun _ => Sum.inr IL.l5))
  | Sum.inr IL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l4))
        (.goto fun _ => Sum.inr IL.l2))
  | Sum.inr IL.l5 =>
    .pop (Sum.inl M.k₀) (fun s o => (s.1, o.map fun y => Sum.inl (d₀ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l5))
        (.goto fun _ => Sum.inr IL.l6))
  | Sum.inr IL.l6 =>
    .pop (Sum.inr IX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr IX.O) (fun s => bit s.2) (.goto fun _ => Sum.inr IL.l6))
        .halt)

def iterM (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ IX
    k₀ := Sum.inr IX.I
    k₁ := Sum.inr IX.O
    Γ := ItΓ M
    Λ := ItΛ M
    main := Sum.inr IL.l1
    σ := Itσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := iterProg M e₀ d₀ e₁ }

variable {M}

def istk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    ∀ k, List (ItΓ M k)
  | Sum.inl k => S k
  | Sum.inr IX.I => i
  | Sum.inr IX.C => cn
  | Sum.inr IX.T => t
  | Sum.inr IX.O => o

section istk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)

@[simp] theorem istk_M (k : M.K) : istk S i cn t o (Sum.inl k) = S k := rfl
@[simp] theorem istk_I : istk S i cn t o (Sum.inr IX.I) = i := rfl
@[simp] theorem istk_C : istk S i cn t o (Sum.inr IX.C) = cn := rfl
@[simp] theorem istk_T : istk S i cn t o (Sum.inr IX.T) = t := rfl
@[simp] theorem istk_O : istk S i cn t o (Sum.inr IX.O) = o := rfl

theorem istk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (istk S i cn t o) (Sum.inl k) x = istk (Function.update S k x) i cn t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem istk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (istk S i cn t o) (Sum.inr IX.I) i' = istk S i' cn t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_C (cn' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.C) cn' = istk S i cn' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_T (t' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.T) t' = istk S i cn t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem istk_set_O (o' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.O) o' = istk S i cn t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end istk

abbrev ICfg (M : FinTM2) : Type := TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)

def embI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c : TM2.Cfg M.Γ M.Λ M.σ) : ICfg M :=
  ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl), (c.var, b), istk c.stk i cn t o⟩

theorem simI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trI q) ((v, b) : Itσ M) (istk S i cn t o) =
      embI b i cn t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← istk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← istk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trI, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepI (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)
    (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (iterProg M e₀ d₀ e₁) (embI b i cn t o c) = some (embI b i cn t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)

theorem embI_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (l : List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₀ l) i cn t o⟩ : ICfg M) := by
  rw [initList_eq]; rfl

theorem embI_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (m : List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (Sum.inr IL.l4), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₁ m) i cn t o⟩ : ICfg M) := by
  rw [haltList_eq]; rfl

theorem istk_nil : (istk (fun _ => []) [] [] [] [] : ∀ k, List (ItΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl

theorem istk_nil_I (i : List (Bool ⊕ Bool)) :
    (istk (fun _ => []) i [] [] [] : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.I) i :=
  (istk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [istk_nil])

theorem istk_nil_O (o : List Bool) :
    (istk (fun _ => []) [] [] [] o : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr IX.O) o :=
  (istk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [istk_nil])

end PEqualNP.Library.Machines.Iter

end

section

namespace PEqualNP.Library.Machines.Iter

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)

variable (v : M.σ) (S : ∀ k, List (M.Γ k))

theorem i1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_T, isFst, bit]

theorem i1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_C, isFst, bit]

theorem i1_nil (b : Option (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1), (v, b), istk S [] cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk S [] cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I]

theorem iloop1 (o : List Bool) :
    ∀ (i : List (Bool ⊕ Bool)) (cn t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[i.length + 1]
        (some (⟨some (Sum.inr IL.l1), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk S [] ((i.filterMap Sum.getRight?).reverse ++ cn)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro cn t b; exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr IL.l1), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]

theorem i2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
        istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i2_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l3), (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop2 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr IL.l3), (v, none),
        istk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) i cn [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact i2_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l2), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l2), (v, some (Sum.inl a)),
          istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      i2_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem i3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i (a :: cn) t o⟩ : ICfg M) =
      some ⟨some (Sum.inl M.main), (v, some (Sum.inl a)), istk S i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i3_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3), (v, b), istk S i [] t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, none), istk S i [] t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
        istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i4_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l2), (v, none), istk (Function.update S M.k₁ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop4 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l4), (v, b), istk (Function.update S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l2), (v, none),
        istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l4), (v, b),
          istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l4), (v, some (Sum.inl (e₁ y))),
          istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      i4_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i5_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₀) (m : List (M.Γ M.k₀))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
        istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i5_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, none), istk (Function.update S M.k₀ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop5 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₀)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr IL.l5), (v, b), istk (Function.update S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l6), (v, none),
        istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l5), (v, b),
          istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (v, some (Sum.inl (d₀ y))),
          istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      i5_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i6_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_O, bit]

theorem i6_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨none, (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop6 (i : List (Bool ⊕ Bool)) (cn : List Bool) :
    ∀ (t o : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨none, (v, none), istk S i cn [] (t.reverse ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l6), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l6), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ :=
      i6_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem update_nil_nil (k : M.K) :
    Function.update (fun _ => [] : ∀ k, List (M.Γ k)) k [] = fun _ => [] :=
  Function.update_eq_self k (fun _ => [] : ∀ k, List (M.Γ k))

theorem main_loop (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)), z.length + k * cn.length ≤ L →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    simp only [List.length_reverse, List.length_map, List.length_nil] at hL ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hgz : (g z).length ≤ z.length + k := hk z
    have hkk : k * (cn.length + 1) = k * cn.length + k := Nat.mul_succ _ _
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (by omega)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : y.length + k * u.length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iter_polyTime (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (k : ℕ) (hk : ∀ y : List Bool, (g y).length ≤ y.length + k) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ := Polynomial.X + Polynomial.C k * Polynomial.X
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hku : k * u.length ≤ k * (y.length + u.length) := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨n, hn, hr⟩ := iter_run e₀ d₀ e₁ g k c.time hk hd hrun y u
      (y.length + u.length + k * (y.length + u.length)) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    have hmul : u.length * (Polynomial.eval (y.length + u.length + k * (y.length + u.length))
          c.time + 2 * (y.length + u.length + k * (y.length + u.length)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          (y.length + u.length + k * (y.length + u.length)) c.time +
            2 * (y.length + u.length + k * (y.length + u.length)) + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize k * (y.length + u.length) = B at hmul ⊢
    omega
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Library.Machines.Iter

end

section

namespace PEqualNP.Library.Machines.Iter

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)

theorem main_loop_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)),
      (∀ j ≤ cn.length, (g^[j] z).length ≤ L) →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr IL.l5), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    simp only [List.length_reverse, List.length_map, List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    have hgz : (g z).length ≤ L := hL 1 (by omega)
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (fun j hj => by
      have := hL (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : ∀ j ≤ u.length, (g^[j] y).length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr IL.l2), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop_bdd e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iterate_length_measure (g : List Bool → List Bool) (m : List Bool → ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y) (y : List Bool) :
    ∀ j : ℕ, m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    have h1 := hm (g^[j] y)
    have h2 := hg (g^[j] y)
    obtain ⟨i1, i2⟩ := ih
    generalize j * m y = A at i2 ⊢
    exact ⟨by omega, by omega⟩

theorem measure_arith (A B L V y u : ℕ) (hLV : L ≤ V) (hAB : A ≤ B) :
    A + 2 * L + 2 * y + u + 5 ≤ B + 2 * V + 3 * (y + u) + 5 := by
  omega

theorem iter_polyTime_measure (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y)
    (ha : ∀ y : List Bool, m y ≤ a * y.length + a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ :=
    Polynomial.X + Polynomial.X * (Polynomial.C a * Polynomial.X + Polynomial.C a)
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hL : ∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length + u.length * (a * y.length + a) := by
      intro j hj
      have h1 := (iterate_length_measure g m hm hg y j).2
      have h2 : j * m y ≤ u.length * (a * y.length + a) := Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n, hn, hr⟩ := iter_run_bdd e₀ d₀ e₁ g c.time hd hrun y u
      (y.length + u.length * (a * y.length + a)) hL
    have hLV : y.length + u.length * (a * y.length + a) ≤
        (y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp := eval_mono c.time hLV
    have hmul : u.length * (Polynomial.eval (y.length + u.length * (a * y.length + a)) c.time +
          2 * (y.length + u.length * (a * y.length + a)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          ((y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a))
            c.time +
            2 * ((y.length + u.length) +
              (y.length + u.length) * (a * (y.length + u.length) + a)) + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    exact measure_arith _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Library.Machines.Iter

end

section

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

def gpair {A C : Type} (p : List A × List C) : List (A ⊕ C) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

inductive FX
  | I | W | TA | TB | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.TA, FX.TB, FX.O] (fun x => by cases x <;> simp)

inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2) (A B C : Type)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => A ⊕ C
  | Sum.inr FX.W => C
  | Sum.inr FX.TA => A
  | Sum.inr FX.TB => B
  | Sum.inr FX.O => B ⊕ C

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (A ⊕ B ⊕ C)

variable {A B C}

def getA [Inhabited A] : Option (A ⊕ B ⊕ C) → A
  | some (Sum.inl a) => a
  | _ => default

def getB [Inhabited B] : Option (A ⊕ B ⊕ C) → B
  | some (Sum.inr (Sum.inl b)) => b
  | _ => default

def getC [Inhabited C] : Option (A ⊕ B ⊕ C) → C
  | some (Sum.inr (Sum.inr c)) => c
  | _ => default

def isA : Option (A ⊕ B ⊕ C) → Bool
  | some (Sum.inl _) => true
  | _ => false

def ofI : A ⊕ C → A ⊕ B ⊕ C
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (Sum.inr c)

variable {M}
variable (A B C)

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M) {A B}
variable [Inhabited A] [Inhabited B] [Inhabited C]

def firstProg (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FstΛ M → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | Sum.inl l => trF A B C (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o.map ofI))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isA s.2)
          (.push (Sum.inr FX.TA) (fun s => getA s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => getC s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.TA) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (getA s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map fun c => Sum.inr (Sum.inr c)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (getC s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inr (Sum.inl (e₁ y))))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.TB) (fun s => getB s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.TB) (fun s o => (s.1, o.map fun b => Sum.inr (Sum.inl b)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (getB s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

def firstM [Fintype A] [Fintype B] [Fintype C] (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M A B C
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M A B C
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (A ⊕ C))
    m := firstProg M C e₀ e₁ }

omit [Inhabited A] [Inhabited B] [Inhabited C]
variable {M} {C}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) : ∀ k, List (FstΓ M A B C k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.TA => ta
  | Sum.inr FX.TB => tb
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
  (o : List (B ⊕ C))

@[simp] theorem fstk_M (k : M.K) : fstk S i w ta tb o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w ta tb o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w ta tb o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_TA : fstk S i w ta tb o (Sum.inr FX.TA) = ta := rfl
@[simp] theorem fstk_TB : fstk S i w ta tb o (Sum.inr FX.TB) = tb := rfl
@[simp] theorem fstk_O : fstk S i w ta tb o (Sum.inr FX.O) = o := rfl

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w ta tb o) (Sum.inl k) x =
      fstk (Function.update S k x) i w ta tb o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (A ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.I) i' = fstk S i' w ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List C) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.W) w' = fstk S i w' ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TA (ta' : List A) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TA) ta' = fstk S i w ta' tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TB (tb' : List B) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TB) tb' = fstk S i w ta tb' o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (B ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.O) o' = fstk S i w ta tb o' := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

variable (M A B C) in

abbrev FCfg : Type := TM2.Cfg (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)

def embF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg M A B C :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w ta tb o⟩

theorem simF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF A B C q) ((v, b) : Fstσ M A B C) (fstk S i w ta tb o) =
      embF b i w ta tb o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF [Inhabited A] [Inhabited B] [Inhabited C] (e₀ : A → M.Γ M.k₀)
    (e₁ : M.Γ M.k₁ → B) (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C)
    (ta : List A) (tb : List B) (o : List (B ⊕ C))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M C e₀ e₁) (embF b i w ta tb o c) = some (embF b i w ta tb o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w ta tb o (M.m l) v S)

end PEqualNP.Library.Machines.Gen

end

section

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} {A B C : Type} [Inhabited A] [Inhabited B] [Inhabited C]
  (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B)

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List C) (o : List (B ⊕ C))

theorem f1_inl (b : Option (A ⊕ B ⊕ C)) (a : A) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_TA, isA, getA, ofI]

theorem f1_inr (b : Option (A ⊕ B ⊕ C)) (a : C) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
        fstk S i (a :: w) t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isA, getC, ofI]

theorem f1_nil (b : Option (A ⊕ B ⊕ C)) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 (tb : List B) : ∀ (i : List (A ⊕ C)) (w : List C) (t : List A)
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) tb o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t tb
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
            fstk S i (a :: w) t tb o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (A ⊕ B ⊕ C)) (a : A) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA, fstk_set_M, getA]

theorem f2_nil (b : Option (A ⊕ B ⊕ C)) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA]

theorem loop2 (tb : List B) : ∀ (t : List A) (S : ∀ k, List (M.Γ k))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] tb o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List A).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b tb
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ :=
      f2_cons e₀ e₁ v S w o b a t tb
    rw [e, ih]; simp

theorem f3_cons (b : Option (A ⊕ B ⊕ C)) (a : C) (w : List C) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
        fstk S [] w ta tb (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, getC]

theorem f3_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] ta tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 (ta : List A) (tb : List B) : ∀ (w : List C) (o : List (B ⊕ C))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w ta tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l4), (v, none),
        fstk S [] [] ta tb (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b ta tb
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
          fstk S [] w ta tb (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w ta tb
    rw [e, ih]; simp

theorem f4_cons (b : Option (A ⊕ B ⊕ C)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (ta : List A)
    (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
        fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_M, getB]

theorem f4_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 (ta : List A) : ∀ (m : List (M.Γ M.k₁)) (t : List B) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] ta t o⟩ :
          FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b ta t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b),
          fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
          fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ :=
      f4_cons e₀ e₁ v S o b y m ta t
    rw [e, ih]; simp

theorem f5_cons (b : Option (A ⊕ B ⊕ C)) (a : B) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
        fstk S [] [] ta t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_O, getB]

theorem f5_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta [] o⟩ : FCfg M A B C) =
      some ⟨none, (v, none), fstk S [] [] ta [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB]

theorem loop5 (ta : List A) : ∀ (t : List B) (o : List (B ⊕ C)) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta t o⟩ : FCfg M A B C)) =
      some ⟨none, (v, none), fstk S [] [] ta [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b ta
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
          fstk S [] [] ta t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a ta t
    rw [e, ih]; simp

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil :
    (fstk (fun _ => []) [] [] [] [] [] : ∀ k, List (FstΓ M A B C k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _ | _) <;> rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_I (i : List (A ⊕ C)) :
    (fstk (fun _ => []) i [] [] [] [] : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] [] i).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_O (o : List (B ⊕ C)) :
    (fstk (fun _ => []) [] [] [] [] o : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] [] o).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_init (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (l : List (M.Γ M.k₀)) :
    embF b i w ta tb o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w ta tb o⟩ : FCfg M A B C) := by
  rw [initList_eq]; rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_halt (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (m : List (M.Γ M.k₁)) :
    embF b i w ta tb o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w ta tb o⟩ : FCfg M A B C) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem gpair_left {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : A → A ⊕ C) : A → Option A) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : C → A ⊕ C) : C → Option A) = fun _ => none := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem gpair_right {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : A → A ⊕ C) : A → Option C) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : C → A ⊕ C) : C → Option C) = some := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem gpair_length {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).length = x.length + w.length := by
  simp [gpair]

theorem first_run [Fintype A] [Fintype B] [Fintype C] (x : List A) (w0 : List C)
    (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M C e₀ e₁)))^[n]
          (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
        some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(gpair (x, w0)).length + 1]
      (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] [] (gpair (x, w0)) [] [] none
    rw [gpair_left, gpair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M C e₀ e₁)))^[
      (gpair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M C e₀ e₁) (gpair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C)) =
      some (embF none [] w0.reverse [] [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse ([] : List (B ⊕ C)) [] x.reverse
      (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M C e₀ e₁))
    (embF none [] w0.reverse [] [] []) (stepF e₀ e₁ none [] w0.reverse [] [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] [] []⟩ : FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) ([] : List A)
      ([] : List B) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) ([] : List A) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C)) =
      some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) ([] : List A) (m.reverse.map e₁)
      (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M C e₀ e₁) (gpair (m.map e₁, w0)))).symm)
    simp [gpair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [gpair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime {α β A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [Inhabited A] [Inhabited B] [Inhabited C]
    (ea : α → List A) (eb : β → List B) (f : α → β)
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : α × List C => gpair (ea p.1, p.2))
      (fun p : β × List C => gpair (eb p.1, p.2))
      (fun p : α × List C => (f p.1, p.2))) := by
  let e₀ : A → c.tm.Γ c.tm.k₀ := fun a => c.inputAlphabet.invFun a
  let e₁ : c.tm.Γ c.tm.k₁ → B := fun y => c.outputAlphabet y
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : α × List C, ∃ n, n ≤ T.eval (gpair (ea p.1, p.2)).length ∧
      (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[n]
          (some (initList (firstM c.tm C e₀ e₁) (gpair (ea p.1, p.2)))) =
        some (haltList (firstM c.tm C e₀ e₁) (gpair (eb (f p.1), p.2))) := by
    rintro ⟨a, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval (ea a).length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm ((ea a).map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (eb (f a)))) :=
      ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run (C := C) e₀ e₁ (ea a) w _ s h
    have hm : (List.map c.outputAlphabet.invFun (eb (f a))).map e₁ = eb (f a) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (eb (f a))]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ ((ea a).map e₀))
        c.tm.k₁).length ≤ (ea a).length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval (ea a).length c.time ≤
        Polynomial.eval ((ea a).length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval ((ea a).length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, gpair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm C e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm C e₀ e₁) l)))
            (hm _ (gpair (ea p.1, p.2)))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm C e₀ e₁) l))
              (hm _ (gpair (eb (f p.1), p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines.Gen

end

section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem cpt_congr_pv3 {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem fm_elim_pv12 {A B C : Type} (φl : A → Option C) (φr : B → Option C) (x : List A)
    (w : List B) :
    (x.map Sum.inl ++ w.map Sum.inr).filterMap (Sum.elim φl φr) =
      x.filterMap φl ++ w.filterMap φr := by
  have h1 : ∀ x : List A, (x.map Sum.inl).filterMap (Sum.elim φl φr) = x.filterMap φl := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  have h2 : ∀ w : List B, (w.map Sum.inr).filterMap (Sum.elim φl φr) = w.filterMap φr := by
    intro w; induction w with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  rw [List.filterMap_append, h1, h2]

private theorem fm_some_pv14 {A C : Type} (g : A → C) (l : List A) :
    l.filterMap (fun a => some (g a)) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem fm_none_pv13 {A C : Type} (l : List A) :
    l.filterMap (fun _ : A => (none : Option C)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem cpt_pairB :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
  have hA : ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (p.1, p.1 ++ p.2)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun b : Bool => some (Sum.inl b)) (fun _ : Bool => none))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun b : Bool => some (Sum.inr b))) ?_
    rintro ⟨x, w⟩
    simp only [encodePair]
    rw [fm_elim_pv12, fm_elim_pv12, fm_some_pv14, fm_some_pv14, fm_some_pv14, fm_none_pv13]
    simp
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a : List Bool => a.map (fun _ => true) ++ [false]) := by
    refine fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true))
      (fun _ => some false) () ?_
    intro a
    induction a with
    | nil => rfl
    | cons b l ih =>
      simp only [fstRun, List.map_cons, List.cons_append, Option.toList_some] at ih ⊢
      rw [← ih]; rfl
  refine cpt_congr_pv3 (cpt_comp (cpt_comp hA (cpt_first hU)) cpt_append) ?_
  rintro ⟨x, w⟩
  simp [pairB, un]

theorem cpt_ifEmpty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then p.2 else []) := by
  obtain ⟨c⟩ := constList_polyTime []
  have hI := Iter.iter_polyTime (fun _ : List Bool => ([] : List Bool)) c 0 (by simp)
  refine cpt_congr_pv3 (cpt_comp cpt_swap hI) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp [Function.iterate_succ_apply']

theorem cpt_ifNonempty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then [] else p.2) := by
  have hneg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => if x = [] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (constList_polyTime [true])) cpt_ifEmpty
  refine cpt_congr_pv3 (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp

theorem cpt_bitFlag {α αΓ : Type} {ea : α → List αΓ} {f : α → Bool}
    (hf : ComputableInPolyTime ea Computability.encodeBool f) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun a => if f a then [true] else []) := by
  have h : ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
      (fun b : Bool => if b then [true] else []) := by
    refine filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h

theorem cpt_pairG {α αΓ : Type} [Fintype αΓ] [Inhabited αΓ] {ea : α → List αΓ}
    {f g : α → List Bool}
    (hf : ComputableInPolyTime ea (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime ea (fun x : List Bool => x) g) :
    ComputableInPolyTime ea encodePair (fun a => (f a, g a)) := by
  obtain ⟨cf⟩ := hf
  obtain ⟨cg⟩ := hg
  have s0 : ComputableInPolyTime ea (fun a : α => Gen.gpair (ea a, ea a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s)) (fun s => some (Sum.inr s)) ?_
    intro a
    simp only [Gen.gpair, fm_some_pv14]
  have s1 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, ea a))
      (fun a : α => Gen.gpair (f a, ea a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := αΓ) ea (fun x : List Bool => x) f cf
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, ea a)⟩⟩
  have s2 : ComputableInPolyTime (fun a : α => Gen.gpair (f a, ea a))
      (fun a : α => Gen.gpair (ea a, f a)) (fun a : α => a) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : αΓ => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : αΓ => none)) ?_
    intro a
    simp only [Gen.gpair]
    rw [fm_elim_pv12, fm_elim_pv12, fm_some_pv14, fm_some_pv14, fm_none_pv13, fm_none_pv13]
    simp
  have s3 : ComputableInPolyTime (fun a : α => Gen.gpair (ea a, f a))
      (fun a : α => Gen.gpair (g a, f a)) (fun a : α => a) := by
    obtain ⟨c⟩ := Gen.first_polyTime (C := Bool) ea (fun x : List Bool => x) g cg
    exact ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (a, f a)⟩⟩
  have s4 : ComputableInPolyTime (fun a : α => Gen.gpair (g a, f a))
      encodePair (fun a : α => (f a, g a)) := by
    refine twoPass_polyTime _ _ _
      (Sum.elim (fun _ : Bool => none) (fun c : Bool => some (Sum.inl c)))
      (Sum.elim (fun b : Bool => some (Sum.inr b)) (fun _ : Bool => none)) ?_
    intro a
    simp only [Gen.gpair, encodePair]
    rw [fm_elim_pv12, fm_elim_pv12, fm_some_pv14, fm_some_pv14, fm_none_pv13, fm_none_pv13]
    simp
  exact cpt_comp (cpt_comp (cpt_comp (cpt_comp s0 s1) s2) s3) s4

private def encT_pv11 (u : List Bool) : List Bool := u.flatMap (fun b => [true, b])

private def encF_pv10 (v : List Bool) : List Bool := v.flatMap (fun b => [false, b])

private def twD_pv25 : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem twD_run_pv26 (l : List Bool) :
    fstRun twD_pv25 (fun _ => none) false l = [] ∧
      fstRun twD_pv25 (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, twD_pv25, ih.1, ih.2]

private def e0D_pv7 : Bool → Bool → Bool × Option Bool × Option Bool
  | false, true => (false, none, none)
  | false, false => (true, none, none)
  | true, b => (true, some false, some b)

private theorem e0D_run_true_pv9 (l : List Bool) :
    fstRun2 e0D_pv7 (fun _ => none) true l = encF_pv10 l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun2, e0D_pv7, encF_pv10, ih]

private theorem e0D_run_false_pv8 (l : List Bool) :
    fstRun2 e0D_pv7 (fun _ => none) false l = encF_pv10 (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, e0D_pv7, ih, e0D_run_true_pv9]

private def mkD_pv16 : Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (d, false), t => ((d || !t, true), some (t || !d))
  | (d, true), b => ((d, false), some b)

private def mk_pv15 (l : List Bool) : List Bool := fstRun mkD_pv16 (fun _ => none) (false, false) l

private theorem mkD_length_pv18 (q : Bool × Bool) (l : List Bool) :
    (fstRun mkD_pv16 (fun _ => none) q l).length = l.length := by
  induction l generalizing q with
  | nil => rfl
  | cons b l ih => obtain ⟨d, ph⟩ := q; cases ph <;> simp [fstRun, mkD_pv16, ih]

private theorem mkD_done_pv17 (v : List Bool) :
    fstRun mkD_pv16 (fun _ => none) (true, false) (encF_pv10 v) = encF_pv10 v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, mkD_pv16, encF_pv10] at ih ⊢; exact ih

private theorem mkD_marked_pv19 (u r : List Bool) :
    fstRun mkD_pv16 (fun _ => none) (false, false) (encT_pv11 u ++ r) =
      encT_pv11 u ++ fstRun mkD_pv16 (fun _ => none) (false, false) r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, mkD_pv16, encT_pv11] at ih ⊢; exact ih

private theorem mk_nil_pv22 (u : List Bool) : mk_pv15 (encT_pv11 u ++ encF_pv10 []) = encT_pv11 u ++ encF_pv10 [] := by
  unfold mk_pv15; rw [mkD_marked_pv19]; rfl

private theorem mk_cons_pv20 (u : List Bool) (b : Bool) (v : List Bool) :
    mk_pv15 (encT_pv11 u ++ encF_pv10 (b :: v)) = encT_pv11 (u ++ [b]) ++ encF_pv10 v := by
  unfold mk_pv15
  rw [mkD_marked_pv19]
  have h : fstRun mkD_pv16 (fun _ => none) (false, false) (encF_pv10 (b :: v)) =
      true :: b :: encF_pv10 v := by
    have h' := mkD_done_pv17 v
    simp [fstRun, mkD_pv16, encF_pv10] at h' ⊢
    exact h'
  rw [h]
  simp [encT_pv11]

private theorem mk_iter_pv21 (k : ℕ) : ∀ u t : List Bool,
    mk_pv15^[k] (encT_pv11 u ++ encF_pv10 t) = encT_pv11 (u ++ t.take k) ++ encF_pv10 (t.drop k) := by
  induction k with
  | zero => intro u t; simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil => rw [mk_nil_pv22, ih]; simp
    | cons b t => rw [mk_cons_pv20, ih]; simp

private def dcD_pv4 : Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none, t => (some t, none)
  | some t, b => (none, some (if t then Sum.inl b else Sum.inr b))

private theorem dcD_F_pv5 (v : List Bool) :
    fstRun dcD_pv4 (fun _ => none) none (encF_pv10 v) = v.map Sum.inr := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [fstRun, dcD_pv4, encF_pv10] at ih ⊢; exact ih

private theorem dcD_T_pv6 (u r : List Bool) :
    fstRun dcD_pv4 (fun _ => none) none (encT_pv11 u ++ r) =
      u.map Sum.inl ++ fstRun dcD_pv4 (fun _ => none) none r := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [fstRun, dcD_pv4, encT_pv11] at ih ⊢; exact ih

private def rawDec_pv23 (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

private theorem rawDec_tagged_pv24 (u v : List Bool) :
    rawDec_pv23 (u.map Sum.inl ++ v.map Sum.inr) = (u, v) := by
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [rawDec_pv23, List.filterMap_append, h1, h2, h3, h4, List.append_nil, List.nil_append]

theorem cpt_unpairB :
    ComputableInPolyTime (fun x : List Bool => x) encodePair unpairB := by
  have hTw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.takeWhile id) :=
    fst_polyTime _ _ _ twD_pv25 (fun _ => none) true (fun s => (twD_run_pv26 s).2.symm)
  have hE0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => encF_pv10 (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D_pv7 (fun _ => none) false (fun s => (e0D_run_false_pv8 s).symm)
  have hMk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mk_pv15 :=
    fst_polyTime _ _ _ mkD_pv16 (fun _ => none) (false, false) (fun _ => rfl)
  obtain ⟨cMk⟩ := hMk
  have hIt := Iter.iter_polyTime mk_pv15 cMk 0 (fun y => by simp [mk_pv15, mkD_length_pv18])
  have hDc : ComputableInPolyTime (fun x : List Bool => x) (fun l : List (Bool ⊕ Bool) => l)
      (fun l : List Bool => fstRun dcD_pv4 (fun _ => none) none l) :=
    fst_polyTime _ _ _ dcD_pv4 (fun _ => none) none (fun _ => rfl)
  have hRaw : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair rawDec_pv23 := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
      (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [rawDec_pv23, encodePair, List.map_filterMap]
  refine cpt_congr_pv3 (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h := mk_iter_pv21 (s.takeWhile id).length [] (s.dropWhile id).tail
  have e : encT_pv11 [] ++ encF_pv10 (s.dropWhile id).tail = encF_pv10 (s.dropWhile id).tail := rfl
  rw [e] at h
  simp only [h, List.nil_append]
  rw [dcD_T_pv6, dcD_F_pv5, rawDec_tagged_pv24]
  rfl

theorem cpt_iterB (g : List Bool → List Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y, m (g y) ≤ m y) (hgl : ∀ y, (g y).length ≤ y.length + m y)
    (ha : ∀ y, m y ≤ a * y.length + a) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => g^[(unpairB s).2.length] (unpairB s).1) := by
  obtain ⟨c⟩ := hg
  exact cpt_comp cpt_unpairB (Iter.iter_polyTime_measure g c m a hm hgl ha)

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Machines

open Turing

inductive MulK
  | I | A | B | C | O
  deriving DecidableEq

instance : Fintype MulK :=
  Fintype.ofList [.I, .A, .B, .C, .O] (fun x => by cases x <;> simp)

inductive MulL
  | split | outer | copy | back | clean
  deriving DecidableEq

instance : Fintype MulL :=
  Fintype.ofList [.split, .outer, .copy, .back, .clean] (fun x => by cases x <;> simp)

abbrev MulΓ : MulK → Type
  | .I => Bool ⊕ Bool
  | .A => Bool
  | .B => Bool
  | .C => Bool
  | .O => Bool

def mulProg : MulL → TM2.Stmt MulΓ MulL (Option Bool)
  | .split =>
    .pop .I (fun _ o => o.map Sum.isLeft)
      (.branch (fun s => s.isSome)
        (.branch (fun s => s == some true)
          (.push .A (fun _ => true) (.goto fun _ => .split))
          (.push .B (fun _ => true) (.goto fun _ => .split)))
        (.goto fun _ => .outer))
  | .outer =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .copy)
        (.goto fun _ => .clean))
  | .copy =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .C (fun _ => true) (.push .O (fun _ => true) (.goto fun _ => .copy)))
        (.goto fun _ => .back))
  | .back =>
    .pop .C (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))
  | .clean =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .clean)
        .halt)

def mulTM : FinTM2 where
  K := MulK
  k₀ := .I
  k₁ := .O
  Γ := MulΓ
  Λ := MulL
  main := .split
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := mulProg

def mstk (i : List (Bool ⊕ Bool)) (a b c o : List Bool) : ∀ k, List (MulΓ k)
  | .I => i
  | .A => a
  | .B => b
  | .C => c
  | .O => o

@[simp] theorem mstk_I (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .I = i := rfl
@[simp] theorem mstk_A (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .A = a := rfl
@[simp] theorem mstk_B (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .B = b := rfl
@[simp] theorem mstk_C (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .C = c := rfl
@[simp] theorem mstk_O (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .O = o := rfl

@[simp] theorem mstk_set_I (i i' : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    Function.update (mstk i a b c o) .I i' = mstk i' a b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_A (i : List (Bool ⊕ Bool)) (a a' b c o : List Bool) :
    Function.update (mstk i a b c o) .A a' = mstk i a' b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_B (i : List (Bool ⊕ Bool)) (a b b' c o : List Bool) :
    Function.update (mstk i a b c o) .B b' = mstk i a b' c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_C (i : List (Bool ⊕ Bool)) (a b c c' o : List Bool) :
    Function.update (mstk i a b c o) .C c' = mstk i a b c' o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_O (i : List (Bool ⊕ Bool)) (a b c o o' : List Bool) :
    Function.update (mstk i a b c o) .O o' = mstk i a b c o' := by
  funext k; cases k <;> simp [mstk]

theorem mstk_start (i : List (Bool ⊕ Bool)) :
    mstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .I i := by
  funext k; cases k <;> simp [mstk]

theorem mstk_end (o : List Bool) :
    mstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .O o := by
  funext k; cases k <;> simp [mstk]

abbrev MulCfg : Type := TM2.Cfg MulΓ MulL (Option Bool)

abbrev mulStep : Option MulCfg → Option MulCfg := flip bind (TM2.step mulProg)

theorem split_inl (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inl y :: i) a b c o⟩) =
      some ⟨some .split, some true, mstk i (true :: a) b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_inr (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inr y :: i) a b c o⟩) =
      some ⟨some .split, some false, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_nil (s : Option Bool) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk [] a b c o⟩) =
      some ⟨some .outer, none, mstk [] a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i (y :: a) b c o⟩) =
      some ⟨some .copy, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i [] b c o⟩) =
      some ⟨some .clean, none, mstk i [] b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .copy, some y, mstk i a b (true :: c) (true :: o)⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a [] c o⟩) =
      some ⟨some .back, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b (y :: c) o⟩) =
      some ⟨some .back, some y, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a b o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b [] o⟩) =
      some ⟨some .outer, none, mstk i a b [] o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .clean, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a [] c o⟩) =
      some ⟨none, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

theorem splitLoopW (a : List Bool) :
    ∀ (w : List Bool) (b : ℕ) (s : Option Bool),
      mulStep^[w.length + 1] (some ⟨some .split, s, mstk (w.map Sum.inr) a (rep b) [] []⟩) =
        some ⟨some .outer, none, mstk [] a (rep (w.length + b)) [] []⟩ := by
  intro w
  induction w with
  | nil => intro b s; simpa using split_nil s a (rep b) [] []
  | cons y w ih =>
    intro b s
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, split_inr, rep_succ, ih]
    rw [show w.length + (b + 1) = w.length + 1 + b from by omega]

theorem splitLoopX (w : List Bool) :
    ∀ (x : List Bool) (a : ℕ) (s : Option Bool),
      mulStep^[x.length + (w.length + 1)]
          (some ⟨some .split, s, mstk (x.map Sum.inl ++ w.map Sum.inr) (rep a) [] [] []⟩) =
        some ⟨some .outer, none, mstk [] (rep (x.length + a)) (rep w.length) [] []⟩ := by
  intro x
  induction x with
  | nil =>
    intro a s
    simpa using splitLoopW (rep a) w 0 s
  | cons y x ih =>
    intro a s
    rw [List.length_cons, show x.length + 1 + (w.length + 1) = (x.length + (w.length + 1)) + 1
      from by omega, Function.iterate_succ_apply, List.map_cons, List.cons_append, split_inl,
      rep_succ, ih]
    rw [show x.length + (a + 1) = x.length + 1 + a from by omega]

theorem copyLoop (a : List Bool) :
    ∀ (b c o : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .copy, s, mstk [] a (rep b) (rep c) (rep o)⟩) =
        some ⟨some .back, none, mstk [] a [] (rep (b + c)) (rep (b + o))⟩ := by
  intro b
  induction b with
  | zero => intro c o s; simpa using copy_nil s [] a (rep c) (rep o)
  | succ b ih =>
    intro c o s
    rw [Function.iterate_succ_apply, ← rep_succ b, copy_cons, rep_succ, rep_succ, ih]
    rw [show b + (c + 1) = b + 1 + c from by omega, show b + (o + 1) = b + 1 + o from by omega]

theorem backLoop (a o : List Bool) :
    ∀ (c b : ℕ) (s : Option Bool),
      mulStep^[c + 1] (some ⟨some .back, s, mstk [] a (rep b) (rep c) o⟩) =
        some ⟨some .outer, none, mstk [] a (rep (c + b)) [] o⟩ := by
  intro c
  induction c with
  | zero => intro b s; simpa using back_nil s [] a (rep b) o
  | succ c ih =>
    intro b s
    rw [Function.iterate_succ_apply, ← rep_succ c, back_cons, rep_succ, ih]
    rw [show c + (b + 1) = c + 1 + b from by omega]

theorem outerLoop (b : ℕ) :
    ∀ (a o : ℕ) (s : Option Bool),
      mulStep^[a * (2 * b + 3) + 1] (some ⟨some .outer, s, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .clean, none, mstk [] [] (rep b) [] (rep (a * b + o))⟩ := by
  intro a
  induction a with
  | zero => intro o s; simpa using outer_nil s [] (rep b) [] (rep o)
  | succ a ih =>
    intro o s
    rw [show (a + 1) * (2 * b + 3) + 1 = (a * (2 * b + 3) + 1) + ((b + 1) + ((b + 1) + 1))
      from by ring, Function.iterate_add_apply mulStep (a * (2 * b + 3) + 1),
      Function.iterate_add_apply mulStep (b + 1) ((b + 1) + 1),
      Function.iterate_succ_apply mulStep (b + 1), ← rep_succ a, outer_cons]
    have h1 : mulStep^[b + 1]
        (some ⟨some .copy, some true, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩ :=
      copyLoop (rep a) b 0 o (some true)
    rw [h1]
    have h2 : mulStep^[b + 1]
        (some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩) =
        some ⟨some .outer, none, mstk [] (rep a) (rep b) [] (rep (b + o))⟩ :=
      backLoop (rep a) (rep (b + o)) b 0 none
    rw [h2, ih]
    rw [show a * b + (b + o) = (a + 1) * b + o from by ring]

theorem cleanLoop (o : List Bool) :
    ∀ (b : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .clean, s, mstk [] [] (rep b) [] o⟩) =
        some ⟨none, none, mstk [] [] [] [] o⟩ := by
  intro b
  induction b with
  | zero => intro s; simpa using clean_nil s [] [] [] o
  | succ b ih =>
    intro s
    rw [Function.iterate_succ_apply, ← rep_succ b, clean_cons, ih]

def mulSteps (x w : ℕ) : ℕ := (w + 1) + ((x * (2 * w + 3) + 1) + (x + (w + 1)))

theorem mul_run (x w : List Bool) :
    (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
        (some (initList mulTM (x.map Sum.inl ++ w.map Sum.inr))) =
      some (haltList mulTM (rep (x.length * w.length))) := by
  refine (congrArg (fun c => (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
    (some c)) (initList_eq mulTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq mulTM _)).symm)
  show mulStep^[mulSteps x.length w.length]
    (some (⟨some .split, none, Function.update (fun _ => []) .I
      (x.map Sum.inl ++ w.map Sum.inr)⟩ : MulCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (rep (x.length * w.length))⟩ : MulCfg)
  rw [← mstk_start, ← mstk_end, mulSteps, Function.iterate_add_apply mulStep (w.length + 1),
    Function.iterate_add_apply mulStep (x.length * (2 * w.length + 3) + 1)]
  have h1 : mulStep^[x.length + (w.length + 1)]
      (some ⟨some .split, none, mstk (x.map Sum.inl ++ w.map Sum.inr) [] [] [] []⟩) =
      some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩ :=
    splitLoopX w x 0 none
  rw [h1]
  have h2 : mulStep^[x.length * (2 * w.length + 3) + 1]
      (some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩) =
      some ⟨some .clean, none, mstk [] [] (rep w.length) [] (rep (x.length * w.length))⟩ :=
    outerLoop w.length x.length 0 none
  rw [h2, cleanLoop]

theorem mul_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)) := by
  exact ⟨{
    tm := mulTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := mulSteps p.1.length p.2.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_pow, encodePair, List.length_append,
            List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } }⟩

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem cptc_pv30 {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private def hdD_pv37 : Bool → Bool → Bool × Option Bool
  | true, true => (true, some true)
  | _, _ => (false, none)

private theorem hdD_run_pv38 (l : List Bool) :
    fstRun hdD_pv37 (fun _ => none) false l = [] ∧
      fstRun hdD_pv37 (fun _ => none) true l = l.takeWhile id := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b l ih => cases b <;> simp [fstRun, hdD_pv37, ih.1, ih.2]

theorem cpt_hd :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) hd :=
  fst_polyTime _ _ _ hdD_pv37 (fun _ => none) true (fun s => (hdD_run_pv38 s).2.symm)

private def dnD_pv31 : Bool → Bool → Bool × Option Bool
  | false, true => (false, none)
  | false, false => (true, none)
  | true, b => (true, some b)

private theorem dnD_true_pv33 (l : List Bool) : fstRun dnD_pv31 (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, dnD_pv31, ih]

private theorem dnD_false_pv32 (l : List Bool) :
    fstRun dnD_pv31 (fun _ => none) false l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, dnD_pv31, ih, dnD_true_pv33]

theorem cpt_dropN :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropN :=
  fst_polyTime _ _ _ dnD_pv31 (fun _ => none) false (fun s => (dnD_false_pv32 s).symm)

private def tlD_pv51 : Bool → Bool → Bool × Option Bool
  | false, _ => (true, none)
  | true, b => (true, some b)

private theorem tlD_true_pv53 (l : List Bool) : fstRun tlD_pv51 (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tlD_pv51, ih]

private theorem tlD_false_pv52 (l : List Bool) : fstRun tlD_pv51 (fun _ => none) false l = l.tail := by
  cases l with
  | nil => rfl
  | cons b l => simp [fstRun, tlD_pv51, tlD_true_pv53]

theorem cpt_tail :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.tail) :=
  fst_polyTime _ _ _ tlD_pv51 (fun _ => none) false (fun s => (tlD_false_pv52 s).symm)

private def tkD_pv48 : Option Bool → Bool → Option Bool × Option Bool
  | none, _ => (none, none)
  | some _, true => (some true, some true)
  | some true, false => (some false, some false)
  | some false, false => (none, none)

private theorem tkD_none_pv49 (l : List Bool) : fstRun tkD_pv48 (fun _ => none) none l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tkD_pv48, ih]

private theorem tkD_some_pv50 (b : Bool) (l : List Bool) :
    fstRun tkD_pv48 (fun _ => none) (some b) l = takeLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, tkD_pv48, takeLA, ih, tkD_none_pv49]

theorem cpt_takeL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) takeL :=
  fst_polyTime _ _ _ tkD_pv48 (fun _ => none) (some false) (fun s => (tkD_some_pv50 false s).symm)

private def drD_pv34 : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (none, some b)
  | some _, true => (some true, none)
  | some true, false => (some false, none)
  | some false, false => (none, none)

private theorem drD_none_pv35 (l : List Bool) : fstRun drD_pv34 (fun _ => none) none l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, drD_pv34, ih]

private theorem drD_some_pv36 (b : Bool) (l : List Bool) :
    fstRun drD_pv34 (fun _ => none) (some b) l = dropLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, drD_pv34, dropLA, ih, drD_none_pv35]

theorem cpt_dropL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) dropL :=
  fst_polyTime _ _ _ drD_pv34 (fun _ => none) (some false) (fun s => (drD_some_pv36 false s).symm)

private def hlD_pv39 : Option Bool → Bool → Option Bool × Option Bool
  | none, _ => (none, none)
  | some _, true => (some true, some true)
  | some true, false => (some false, some false)
  | some false, false => (none, some false)

private theorem hlD_none_pv40 (l : List Bool) : fstRun hlD_pv39 (fun _ => none) none l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, hlD_pv39, ih]

private theorem hlD_some_pv41 (b : Bool) (l : List Bool) :
    fstRun hlD_pv39 (fun _ => none) (some b) l = headLA b l := by
  induction l generalizing b with
  | nil => cases b <;> rfl
  | cons a l ih => cases a <;> cases b <;> simp [fstRun, hlD_pv39, headLA, ih, hlD_none_pv40]

theorem cpt_headL :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headL :=
  fst_polyTime _ _ _ hlD_pv39 (fun _ => none) (some false) (fun s => (hlD_some_pv41 false s).symm)

private def ppD_pv42 : Option Bool → Bool → Option Bool × Option Bool
  | none, true => (some false, none)
  | none, false => (some true, some false)
  | some false, true => (some false, none)
  | some false, false => (some true, none)
  | some true, b => (some true, some b)

private theorem ppD_true_pv45 (l : List Bool) : fstRun ppD_pv42 (fun _ => none) (some true) l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ppD_pv42, ih]

private theorem ppD_false_pv43 (l : List Bool) :
    fstRun ppD_pv42 (fun _ => none) (some false) l = (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun, ppD_pv42, ih, ppD_true_pv45]

private theorem ppD_none_pv44 (l : List Bool) : fstRun ppD_pv42 (fun _ => none) none l = popT l := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp [fstRun, ppD_pv42, popT, dropN, ppD_true_pv45, ppD_false_pv43]

theorem cpt_popT :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) popT :=
  fst_polyTime _ _ _ ppD_pv42 (fun _ => none) none (fun s => (ppD_none_pv44 s).symm)

private theorem blank_run_pv27 (l : List Bool) :
    fstRun (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) () l = blank l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, blank] at ih ⊢; exact ih

theorem cpt_blank :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) blank :=
  fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some false)) (fun _ => none) ()
    (fun s => (blank_run_pv27 s).symm)

private def spD_pv46 : Unit → Bool → Unit × Option Bool × Option Bool
  | _, true => ((), some true, some false)
  | _, false => ((), some false, none)

private theorem spD_run_pv47 (l : List Bool) : fstRun2 spD_pv46 (fun _ => none) () l = spread l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, spD_pv46, spread] at ih ⊢ <;> exact ih

theorem cpt_spread :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) spread :=
  fst2_polyTime _ _ _ spD_pv46 (fun _ => none) () (fun s => (spD_run_pv47 s).symm)

private def buD_pv28 : Unit → Bool → Unit × Option Bool × Option Bool
  | _, true => ((), some true, none)
  | _, false => ((), some true, some false)

private theorem buD_run_pv29 (l : List Bool) : fstRun2 buD_pv28 (fun _ => none) () l = bump l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [fstRun2, buD_pv28, bump] at ih ⊢ <;> exact ih

theorem cpt_bump :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bump :=
  fst2_polyTime _ _ _ buD_pv28 (fun _ => none) () (fun s => (buD_run_pv29 s).symm)

theorem cpt_const (l : List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => l) :=
  constList_polyTime l

theorem cpt_mulU :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => mulU p.1 p.2) :=
  cptc_pv30 mul_polyTime (fun _ => rfl)

theorem cpt_unpairB1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).1) :=
  cptc_pv30 (cpt_comp cpt_unpairB cpt_fst) (fun _ => rfl)

theorem cpt_unpairB2 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) :=
  cptc_pv30 (cpt_comp cpt_unpairB cpt_snd) (fun _ => rfl)

theorem cpt_app2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => u s ++ v s) :=
  cptc_pv30 (cpt_comp (cpt_pair hu hv) cpt_append) (fun _ => rfl)

theorem cpt_pairB2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (u s) (v s)) :=
  cptc_pv30 (cpt_comp (cpt_pair hu hv) cpt_pairB) (fun _ => rfl)

theorem cpt_mulU2 {u v : List Bool → List Bool}
    (hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u)
    (hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (u s) (v s)) :=
  cptc_pv30 (cpt_comp (cpt_pair hu hv) cpt_mulU) (fun _ => rfl)

theorem cpt_sel {f a b : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) a)
    (hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) b) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => sel (f s) (a s) (b s)) := by
  have h1 := cpt_comp (cpt_pair hf ha) cpt_ifEmpty
  have h2 := cpt_comp (cpt_pair hf hb) cpt_ifNonempty
  refine cptc_pv30 (cpt_app2 h1 h2) ?_
  intro s
  by_cases h : f s = [] <;> simp [sel, h]

theorem cpt_iterLen {g cnt arg : List Bool → List Bool}
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (hgl : ∀ s, (g s).length ≤ s.length)
    (hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt)
    (harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 0 (fun y => by simpa using hgl y)
  exact cptc_pv30 (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

theorem cpt_move :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) move :=
  cptc_pv30 (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropL)
    (cpt_app2 cpt_unpairB2 (cpt_comp cpt_unpairB1 cpt_headL))) (fun _ => rfl)

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private theorem cptE_pv54 {f f' : List Bool → List Bool} (h : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) (e : ∀ a, f a = f' a) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem cpt_hd1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => hd (f y)) :=
  cpt_comp hf cpt_hd

theorem cpt_dropN1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => dropN (f y)) :=
  cpt_comp hf cpt_dropN

theorem cpt_tail1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (f y).tail) :=
  cpt_comp hf cpt_tail

theorem cpt_takeL1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => takeL (f y)) :=
  cpt_comp hf cpt_takeL

theorem cpt_popT1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => popT (f y)) :=
  cpt_comp hf cpt_popT

theorem cpt_unpairB1_1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB (f y)).1) :=
  cptE_pv54 (cpt_comp hf cpt_unpairB1) (fun _ => rfl)

theorem cpt_unpairB2_1 {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB (f y)).2) :=
  cptE_pv54 (cpt_comp hf cpt_unpairB2) (fun _ => rfl)

theorem cpt_cons1 (b : Bool) {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => b :: f y) :=
  cptE_pv54 (cpt_app2 (cpt_const [b]) hf) (fun _ => rfl)

theorem cpt_iterGrow {g cnt arg : List Bool → List Bool} (hg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) g) (k : ℕ)
    (hgl : ∀ s, (g s).length ≤ s.length + k) (hcnt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cnt) (harg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) arg) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c k hgl
  exact cptE_pv54 (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

theorem cpt_fetch {ps pc : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fetch (ps y) (pc y)) := by
  unfold fetch
  exact cpt_takeL1 (cpt_iterLen cpt_dropL dropL_length (cpt_tail1 hpc) hps)

theorem cpt_fOp {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fOp (I y)) := by
  unfold fOp
  exact cpt_hd1 hI

theorem cpt_fK {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fK (I y)) := by
  unfold fK
  exact cpt_tail1 (cpt_hd1 (cpt_dropN1 hI))

theorem cpt_fW {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fW (I y)) := by
  unfold fW
  exact cpt_tail1 (cpt_hd1 (cpt_dropN1 (cpt_dropN1 hI)))

theorem cpt_fN1 {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fN1 (I y)) := by
  unfold fN1
  exact cpt_hd1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI)))

theorem cpt_fN2 {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fN2 (I y)) := by
  unfold fN2
  exact cpt_hd1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI))))

theorem cpt_fTb {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => fTb (I y)) := by
  unfold fTb
  exact cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI))))

theorem cpt_lookup {tb idx : List Bool → List Bool} (htb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) tb) (hidx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) idx) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => lookup (tb y) (idx y)) := by
  unfold lookup
  exact cpt_tail1 (cpt_hd1 (cpt_iterLen cpt_dropN dropN_length hidx htb))

theorem cpt_splitK {kf sk : List Bool → List Bool} (hkf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) kf) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => splitK (kf y) (sk y)) := by
  unfold splitK
  exact cpt_iterGrow cpt_move 1 move_length hkf (cpt_pairB2 hsk (cpt_const []))

theorem cpt_pcSel {pc o n1 n2 valS : List Bool → List Bool} (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) (ho : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) o)
    (hn1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) n1) (hn2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) n2) (hv : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) valS) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => pcSel (pc y) (o y) (n1 y) (n2 y) (valS y)) := by
  unfold pcSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  have h3 := cpt_tail1 h2
  have h4 := cpt_tail1 h3
  have h5 := cpt_tail1 h4
  have h6 := cpt_tail1 h5
  exact cpt_sel hpc hpc (cpt_sel ho (cpt_const []) (cpt_sel h1 hn1 (cpt_sel h2 hn1
    (cpt_sel h3 hn1 (cpt_sel h4 hn1 (cpt_sel h5 (cpt_sel hv hn2 hn1)
      (cpt_sel h6 (cpt_cons1 true hv) (cpt_const []))))))))

theorem cpt_stSel {pc o st valS valT : List Bool → List Bool} (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) (ho : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) o)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hvS : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) valS) (hvT : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) valT) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => stSel (pc y) (o y) (st y) (valS y) (valT y)) := by
  unfold stSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  have h3 := cpt_tail1 h2
  have h4 := cpt_tail1 h3
  exact cpt_sel hpc hst (cpt_sel ho hst (cpt_sel h1 hst (cpt_sel h2 hvT (cpt_sel h3 hvT
    (cpt_sel h4 hvS hst)))))

theorem cpt_skSel {pc o sk r d pushed : List Bool → List Bool} (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc) (ho : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) o)
    (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) (hr : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) r) (hd' : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) d) (hp : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pushed) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => skSel (pc y) (o y) (sk y) (r y) (d y) (pushed y)) := by
  unfold skSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  exact cpt_sel hpc hsk (cpt_sel ho hsk (cpt_sel h1
    (cpt_sel hr hd' (cpt_app2 hd' (cpt_app2 hp hr)))
    (cpt_sel h2 (cpt_app2 hd' (cpt_popT1 hr)) hsk)))

theorem cpt_pcOut {ps pc st : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => pcOut (ps y) (pc y) (st y)) := by
  unfold pcOut
  have hI := cpt_fetch hps hpc
  exact cpt_pcSel hpc (cpt_fOp hI) (cpt_fN1 hI) (cpt_fN2 hI) (cpt_lookup (cpt_fTb hI) hst)

theorem cpt_stOut {ps pc st sk : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => stOut (ps y) (pc y) (st y) (sk y)) := by
  unfold stOut
  have hI := cpt_fetch hps hpc
  have hT := cpt_fTb hI
  exact cpt_stSel hpc (cpt_fOp hI) hst (cpt_lookup hT hst)
    (cpt_lookup hT (cpt_app2 (cpt_mulU2 hst (cpt_fW hI))
      (cpt_hd1 (cpt_unpairB1_1 (cpt_splitK (cpt_fK hI) hsk)))))

theorem cpt_skOut {ps pc st sk : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => skOut (ps y) (pc y) (st y) (sk y)) := by
  unfold skOut
  have hI := cpt_fetch hps hpc
  have hS := cpt_splitK (cpt_fK hI) hsk
  exact cpt_skSel hpc (cpt_fOp hI) hsk (cpt_unpairB1_1 hS) (cpt_unpairB2_1 hS)
    (cpt_app2 (cpt_cons1 true (cpt_lookup (cpt_fTb hI) hst)) (cpt_const [false]))

theorem cpt_sstepParts {ps pc st sk : List Bool → List Bool} (hps : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) ps) (hpc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) pc)
    (hst : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) st) (hsk : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sk) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => sstepParts (ps y) (pc y) (st y) (sk y)) := by
  unfold sstepParts
  exact cpt_pairB2 hps (cpt_pairB2 (cpt_pcOut hps hpc hst)
    (cpt_pairB2 (cpt_stOut hps hpc hst hsk) (cpt_skOut hps hpc hst hsk)))

theorem cpt_sstep : PEqualNP.Library.ComputableInPolyTime
    (fun x : List Bool => x) (fun x : List Bool => x) sstep := by
  have h2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB y).2) := cpt_unpairB2
  have h22 := cpt_unpairB2_1 h2
  have h : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => sstepParts (unpairB y).1 (unpairB (unpairB y).2).1
      (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2) :=
    cpt_sstepParts cpt_unpairB1 (cpt_unpairB1_1 h2) (cpt_unpairB1_1 h22) (cpt_unpairB2_1 h22)
  exact h

end PEqualNP.Library.Universal

end

section

namespace PEqualNP.Library.Machines
open Turing PEqualNP.Library

theorem output_length_poly (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ∃ q : Polynomial ℕ, ∀ x : List Bool, (f x).length ≤ q.eval x.length := by
  obtain ⟨c⟩ := hf
  refine ⟨Polynomial.X + Polynomial.C (maxPush c.tm) * c.time, fun x => ?_⟩
  obtain ⟨⟨steps, hev⟩, hle⟩ := c.outputsFun x
  have hev' : (flip bind (TM2.step c.tm.m))^[steps]
      (some (⟨some c.tm.main, c.tm.initialState, Function.update (fun _ => []) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none, c.tm.initialState, Function.update (fun _ => []) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ) := by
    rw [← initList_eq, ← haltList_eq]; exact hev
  have key := run_length c.tm c.tm.k₁ steps _ _ hev'
  simp only [Function.update_self, List.length_map] at key
  have hin : ((Function.update (fun _ => ([] : List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x) : ∀ k, List (c.tm.Γ k)) c.tm.k₁).length ≤ x.length := by
    by_cases hk : c.tm.k₁ = c.tm.k₀
    · rw [hk]; simp
    · rw [Function.update_of_ne hk]; simp
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  calc (f x).length ≤ x.length + maxPush c.tm * steps := key.trans (by omega)
    _ ≤ x.length + maxPush c.tm * c.time.eval x.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _

end PEqualNP.Library.Machines

end

section

namespace PEqualNP.Library.Machines

open PEqualNP.Library

private theorem cpt_mul_pv55 {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate ((f x).length * (g x).length) true) :=
  cpt_comp (cpt_pair hf hg) mul_polyTime

private theorem pow_polyTime_pv56
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (n : ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ n) true) := by
  induction n with
  | zero => simpa using hconst [true]
  | succ n ih =>
    have h := cpt_mul_pv55 cpt_id ih
    have e : (fun x : List Bool =>
        List.replicate (x.length * (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool => List.replicate (x.length ^ (n + 1)) true) := by
      funext x
      rw [List.length_replicate, pow_succ, Nat.mul_comm]
    rw [← e]
    exact h

theorem clock_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (p : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h := cpt_comp (cpt_pair hp hq) cpt_append
    have e : (fun x : List Bool => List.replicate (p.eval x.length) true ++
        List.replicate (q.eval x.length) true) =
        (fun x : List Bool => List.replicate ((p + q).eval x.length) true) := by
      funext x
      rw [Polynomial.eval_add, List.replicate_add]
    rw [← e]
    exact h
  | monomial n a =>
    have h := cpt_mul_pv55 (hconst (List.replicate a true)) (pow_polyTime_pv56 hconst n)
    have e : (fun x : List Bool => List.replicate ((List.replicate a true).length *
        (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool =>
          List.replicate ((Polynomial.monomial n a).eval x.length) true) := by
      funext x
      rw [List.length_replicate, List.length_replicate, Polynomial.eval_monomial]
    rw [← e]
    exact h

end PEqualNP.Library.Machines

end

section

theorem PEqualNP.Library.L055 : ∀ p : Polynomial ℕ,
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) :=
  fun p => PEqualNP.Library.Machines.clock_polyTime
    (fun l => PEqualNP.Library.Machines.constList_polyTime l) p

end

section

namespace PEqualNP.Library.SearchHelpers.Tab.StepW

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

theorem cptE {f f' : List Bool → List Bool} (h : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) (e : ∀ a, f a = f' a) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem cpt_iterMeasure {g cnt arg : List Bool → List Bool} (hg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) g)
    (m : List Bool → ℕ) (a : ℕ) (hm : ∀ y, m (g y) ≤ m y)
    (hgl : ∀ y, (g y).length ≤ y.length + m y) (ha : ∀ y, m y ≤ a * y.length + a)
    (hcnt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cnt) (harg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) arg) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  exact cptE (cpt_comp (cpt_pair harg hcnt) (Iter.iter_polyTime_measure g c m a hm hgl ha))
    (fun _ => rfl)

def tk (p w : List Bool) : List Bool := (unpairB (mulU p [true] ++ false :: w)).1

theorem tk_eq (p w : List Bool) : tk p w = w.take p.length := by
  have h1 : (mulU p [true] ++ false :: w).takeWhile id = un p.length := by
    simp [mulU, un]
  have h2 : (mulU p [true] ++ false :: w).dropWhile id = false :: w := by
    simp [mulU, un]
  simp [tk, unpairB, h1, h2, un]

theorem tk_length (p w : List Bool) : (tk p w).length ≤ p.length := by
  rw [tk_eq, List.length_take]
  exact Nat.min_le_left _ _

theorem cpt_tk {p w : List Bool → List Bool} (hp : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) p) (hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) w) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => tk (p s) (w s)) :=
  cpt_unpairB1_1 (cpt_app2 (cpt_mulU2 hp (cpt_const [true])) (cpt_cons1 false hw))

def lstep (f : List Bool → List Bool) (y : List Bool) : List Bool :=
  pairB (unpairB y).1 (pairB (unpairB (unpairB y).2).1.tail
    (pairB (unpairB (unpairB (unpairB y).2).2).1
      (tk (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
        (unpairB (unpairB (unpairB y).2).2).1)) ++ (unpairB (unpairB (unpairB y).2).2).2)))

theorem cpt_lstep {f : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (lstep f) := by
  have h1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB y).1) := cpt_unpairB1
  have h2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun y => (unpairB y).2) := cpt_unpairB2
  have hr := cpt_tail1 (cpt_unpairB1_1 h2)
  have h3 := cpt_unpairB2_1 h2
  have harg := cpt_unpairB1_1 h3
  have hacc := cpt_unpairB2_1 h3
  exact cpt_pairB2 h1 (cpt_pairB2 hr (cpt_pairB2 harg
    (cpt_app2 (cpt_tk h1 (cpt_comp (cpt_pairB2 hr harg) hf)) hacc)))

theorem lstep_pairB (f : List Bool → List Bool) (pad r arg acc : List Bool) :
    lstep f (pairB pad (pairB r (pairB arg acc))) =
      pairB pad (pairB r.tail (pairB arg (tk pad (f (pairB r.tail arg)) ++ acc))) := by
  simp only [lstep, unpairB_pairB]

theorem lstep_measure (f : List Bool → List Bool) (y : List Bool) :
    (unpairB (lstep f y)).1.length + 3 ≤ (unpairB y).1.length + 3 := by
  simp only [lstep, unpairB_pairB]
  exact le_rfl

theorem lstep_length (f : List Bool → List Bool) (y : List Bool) :
    (lstep f y).length ≤ y.length + ((unpairB y).1.length + 3) := by
  have h1 := unpairB_length y
  have h2 := unpairB_length (unpairB y).2
  have h3 := unpairB_length (unpairB (unpairB y).2).2
  have h4 := tk_length (unpairB y).1 (f (pairB (unpairB (unpairB y).2).1.tail
        (unpairB (unpairB (unpairB y).2).2).1))
  have h5 : (unpairB (unpairB y).2).1.tail.length ≤ (unpairB (unpairB y).2).1.length := by
    simp
  simp only [lstep, pairB_length, List.length_append]
  omega

theorem lstep_iter (f : List Bool → List Bool) (pad arg : List Bool) (n : ℕ)
    (hpad : ∀ i < n, (f (pairB (un i) arg)).length ≤ pad.length) (acc : List Bool) :
    (lstep f)^[n] (pairB pad (pairB (un n) (pairB arg acc))) =
      pairB pad (pairB [] (pairB arg
        ((List.range n).flatMap (fun i => f (pairB (un i) arg)) ++ acc))) := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, lstep_pairB, un_succ, List.tail_cons, tk_eq,
      List.take_of_length_le (hpad n (by omega)), ih (fun i hi => hpad i (by omega)),
      List.range_succ, List.flatMap_append]
    simp

theorem cpt_flatMapRange {f cnt arg : List Bool → List Bool} (hf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f) (hcnt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cnt)
    (harg : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) arg) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (List.range (cnt s).length).flatMap fun i => f (pairB (un i) (arg s))) := by
  obtain ⟨P, hP⟩ := output_length_poly f hf
  have hpad : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => List.replicate (P.eval (pairB (cnt s) (arg s)).length) true) :=
    cpt_comp (cpt_pairB2 hcnt harg) (PEqualNP.Library.L055 P)
  have hun : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => mulU (cnt s) [true]) := cpt_mulU2 hcnt (cpt_const [true])
  have hinit := cpt_pairB2 hpad (cpt_pairB2 hun (cpt_pairB2 harg (cpt_const [])))
  have hit := cpt_iterMeasure (cpt_lstep hf) (fun y => (unpairB y).1.length + 3) 3
    (lstep_measure f) (lstep_length f)
    (fun y => by have := unpairB_length y; omega) hcnt hinit
  have hout := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hit))
  refine cptE hout (fun s => ?_)
  have e : mulU (cnt s) [true] = un (cnt s).length := by simp [mulU]
  have hb : ∀ i < (cnt s).length, (f (pairB (un i) (arg s))).length ≤
      (List.replicate (P.eval (pairB (cnt s) (arg s)).length) true).length := by
    intro i hi
    rw [List.length_replicate]
    refine (hP _).trans (eval_mono P ?_)
    rw [pairB_length, pairB_length, un_length]
    omega
  show (unpairB (unpairB (unpairB ((lstep f)^[(cnt s).length]
    (pairB _ (pairB (mulU (cnt s) [true]) (pairB (arg s) []))))).2).2).2 = _
  rw [e, lstep_iter f _ (arg s) (cnt s).length hb, unpairB_pairB, unpairB_pairB, unpairB_pairB]
  simp

end PEqualNP.Library.SearchHelpers.Tab.StepW

end

section

namespace PEqualNP.Library.SearchHelpers.KSat.Hard

open PEqualNP.Search PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
  PEqualNP.Library.SearchHelpers.Tab.StepW

theorem bits_two_pow (a : ℕ) : (2 ^ a).bits = List.replicate a false ++ [true] := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, Nat.mul_comm, Nat.bit0_bits _ (pow_ne_zero _ two_ne_zero), ih]
    rfl

theorem spread_un (a : ℕ) :
    spread (un a) = (List.replicate a false).flatMap fun d => [true, d] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [un_succ, List.replicate_succ, List.flatMap_cons, ← ih]
    rfl

def litY (pol : Bool) (i : List Bool) : List Bool :=
  true :: pol :: (spread (true :: i) ++ [true, true, false, true])

theorem litY_un (pol : Bool) (m : ℕ) : litY pol (un m) = encodeLiteral (Y m, pol) := by
  rw [litY, ← un_succ, spread_un]
  simp only [encodeLiteral, Y, bits_two_pow, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.append_assoc]

def litX (it : List Bool) : List Bool :=
  tk [true, true] it ++ true :: true :: it.tail.tail

theorem litX_lit (l : Literal) : litX (encodeLiteral l) = encodeLiteral (X l.1, l.2) := by
  have e : X l.1 = Nat.bit true l.1 := by simp [X, Nat.bit_val]
  have h1 : encodeLiteral (X l.1, l.2) = true :: l.2 :: true :: true :: vcode l.1 := by
    rw [encodeLiteral_eq]
    show true :: l.2 :: vcode (X l.1) = _
    rw [e, vcode_bit true _ (fun _ => rfl)]
  rw [h1, litX, tk_eq, encodeLiteral_eq]
  rfl

def outI (i r : List Bool) : List Bool :=
  sel r [] (sel (bflag (isEnd r))
    (litY false i ++ (litX (headI r) ++ (litY true (true :: i) ++ [false, false])))
    (litY false i ++ ([false, false] ++ (litY true (true :: i) ++ [false, false]))))

theorem outI_nil (i : List Bool) : outI i [] = [] := by simp [outI, sel]

theorem outI_lit (m : ℕ) (l : Literal) (rest : List Bool) :
    outI (un m) (encodeLiteral l ++ rest) =
      encodeClause [(Y m, false), (X l.1, l.2), (Y (m + 1), true)] := by
  have hne : encodeLiteral l ++ rest ≠ [] := by simp [encodeLiteral_eq]
  unfold outI
  rw [← un_succ, litY_un, litY_un, isEnd_lit, headI_lit, litX_lit]
  simp [sel, bflag, encodeClause, hne]

theorem outI_end (m : ℕ) (rest : List Bool) :
    outI (un m) (false :: false :: rest) =
      encodeCNF [[(Y m, false)], [(Y (m + 1), true)]] := by
  unfold outI
  rw [← un_succ, litY_un, litY_un]
  simp [sel, bflag, isEnd, encodeCNF, encodeClause]

def walk : ℕ → ℕ → List Bool → List Bool
  | 0, _, _ => []
  | n + 1, m, r => outI (un m) r ++ walk n (m + 1) (dropI r)

theorem walk_nil (n : ℕ) : ∀ m : ℕ, walk n m [] = [] := by
  induction n with
  | zero => intro m; rfl
  | succ n ih => intro m; simp [walk, outI_nil, dropI, ih]

theorem walk_range (n : ℕ) : ∀ (m : ℕ) (r : List Bool),
    (List.range n).flatMap (fun i => outI (un (m + i)) (dropI^[i] r)) = walk n m r := by
  induction n with
  | zero => intro m r; rfl
  | succ n ih =>
    intro m r
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, walk, ← ih]
    congr 1
    refine List.flatMap_congr ?_
    intro i _
    rw [show m + (i + 1) = m + 1 + i by omega, Function.iterate_succ_apply]

theorem enc_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by
  simp [encodeCNF]

theorem enc_append (φ ψ : CNF) : encodeCNF (φ ++ ψ) = encodeCNF φ ++ encodeCNF ψ := by
  simp [encodeCNF]

theorem walk_clause (c : Clause) : ∀ (k m : ℕ) (rest : List Bool),
    walk (k + (c.length + 1)) m (encodeClause c ++ rest) =
      encodeCNF (chain m c) ++ walk k (m + c.length + 1) rest := by
  induction c with
  | nil =>
    intro k m rest
    have e : encodeClause [] ++ rest = false :: false :: rest := by simp [encodeClause]
    rw [e]
    show outI (un m) (false :: false :: rest) ++ walk k (m + 1) rest = _
    rw [outI_end]
    rfl
  | cons l c ih =>
    intro k m rest
    have e : encodeClause (l :: c) ++ rest = encodeLiteral l ++ (encodeClause c ++ rest) := by
      simp [encodeClause]
    rw [e]
    show outI (un m) (encodeLiteral l ++ (encodeClause c ++ rest)) ++
      walk (k + (c.length + 1)) (m + 1) (dropI (encodeLiteral l ++ (encodeClause c ++ rest))) = _
    rw [outI_lit, dropI_lit, ih, chain, enc_cons, List.append_assoc,
      show m + 1 + c.length + 1 = m + (l :: c).length + 1 by
        simp only [List.length_cons]; omega]

theorem walk_cnf (φ : CNF) : ∀ k m : ℕ,
    walk (k + nIt φ) m (encodeCNF φ) = encodeCNF (splitFrom m φ) := by
  induction φ with
  | nil => intro k m; exact walk_nil _ _
  | cons c φ ih =>
    intro k m
    rw [nIt, ← Nat.add_assoc, enc_cons, walk_clause, ih, splitFrom, enc_append]

def G (x : List Bool) : List Bool :=
  (List.range x.length).flatMap fun i => outI (un i) (dropI^[i] x)

theorem G_enc (φ : CNF) : G (encodeCNF φ) = encodeCNF (splitFrom 0 φ) := by
  have h := walk_range (encodeCNF φ).length 0 (encodeCNF φ)
  simp only [Nat.zero_add] at h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (nIt_le φ)
  rw [G, h, hk, Nat.add_comm, walk_cnf]

def g (x : List Bool) : List Bool :=
  sel (bflag (wfB x)) [false] (encodeClause [(Y 0, true)] ++ G x)

theorem g_enc (φ : CNF) : g (encodeCNF φ) = encodeCNF (split φ) := by
  have h : wfB (encodeCNF φ) = true := (wfB_iff _).2 ⟨φ, rfl⟩
  rw [g, h, G_enc, split, enc_cons]
  simp [sel, bflag]

theorem g_not (x : List Bool) (h : wfB x = false) : g x = [false] := by
  rw [g, h]
  simp [sel, bflag]

theorem not_enc_false (φ : CNF) : encodeCNF φ ≠ [false] := by
  intro h
  have h1 : wfB [false] = true := (wfB_iff _).2 ⟨φ, h⟩
  exact absurd h1 (by decide)

end PEqualNP.Library.SearchHelpers.KSat.Hard

end

section

namespace PEqualNP.Library.SearchHelpers.KSat.Hard

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.Tab.StepW

inductive IS : Type
  | b | t | f | e
  deriving DecidableEq

instance : Fintype IS :=
  ⟨{.b, .t, .f, .e}, fun q => by cases q <;> simp⟩

def hiD : IS → Bool → IS × Option Bool
  | .b, true => (.t, some true)
  | .b, false => (.f, some false)
  | .t, d => (.b, some d)
  | .f, d => (.e, some d)
  | .e, _ => (.e, none)

theorem hiD_e (l : List Bool) : fstRun hiD (fun _ => none) IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, hiD, ih]

theorem hiD_run : ∀ s : List Bool, fstRun hiD (fun _ => none) IS.b s = headI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, hiD, headI, hiD_run r]
  | false :: d :: r => by simp [fstRun, hiD, headI, hiD_e]

theorem cpt_headI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) headI :=
  fst_polyTime _ _ _ hiD (fun _ => none) IS.b (fun s => (hiD_run s).symm)

def diD : IS → Bool → IS × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, _ => (.e, none)
  | .e, a => (.e, some a)

theorem diD_e (l : List Bool) : fstRun diD (fun _ => none) IS.e l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, diD, ih]

theorem diD_run : ∀ s : List Bool, fstRun diD (fun _ => none) IS.b s = dropI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, diD, dropI, diD_run r]
  | false :: d :: r => by simp [fstRun, diD, dropI, diD_e]

theorem cpt_dropI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) dropI :=
  fst_polyTime _ _ _ diD (fun _ => none) IS.b (fun s => (diD_run s).symm)

def ieD : IS → Bool → IS × Option Bool
  | .b, false => (.f, none)
  | .f, false => (.t, none)
  | .t, _ => (.t, none)
  | _, _ => (.e, none)

def ieF : IS → Option Bool
  | .t => some true
  | _ => none

theorem ieD_e (l : List Bool) : fstRun ieD ieF IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

theorem ieD_t (l : List Bool) : fstRun ieD ieF IS.t l = [true] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

theorem ieD_run (s : List Bool) : fstRun ieD ieF IS.b s = bflag (isEnd s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp [fstRun, ieD, ieD_e, ieD_t, isEnd, bflag]

theorem cpt_isEndF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => bflag (isEnd s)) :=
  fst_polyTime _ _ _ ieD ieF IS.b (fun s => (ieD_run s).symm)

theorem cpt_wfF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => bflag (wfB s)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

theorem cpt_litY (pol : Bool) {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => litY pol (I s)) :=
  cptE (cpt_cons1 true (cpt_cons1 pol (cpt_app2 (cpt_comp (cpt_cons1 true hI) cpt_spread)
    (cpt_const [true, true, false, true])))) (fun _ => rfl)

theorem cpt_litX {I : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => litX (I s)) :=
  cptE (cpt_app2 (cpt_tk (cpt_const [true, true]) hI)
    (cpt_cons1 true (cpt_cons1 true (cpt_tail1 (cpt_tail1 hI))))) (fun _ => rfl)

theorem cpt_outI {I R : List Bool → List Bool} (hI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) I) (hR : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) R) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => outI (I s) (R s)) := by
  have hEnd : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => bflag (isEnd (R s))) :=
    cptE (cpt_comp hR cpt_isEndF) (fun _ => rfl)
  have hH : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => headI (R s)) := cpt_comp hR cpt_headI
  have hI1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => true :: I s) := cpt_cons1 true hI
  have hT : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => litY true (true :: I s) ++ [false, false]) :=
    cpt_app2 (cpt_litY true hI1) (cpt_const [false, false])
  exact cptE (cpt_sel hR (cpt_const []) (cpt_sel hEnd
    (cpt_app2 (cpt_litY false hI) (cpt_app2 (cpt_litX hH) hT))
    (cpt_app2 (cpt_litY false hI) (cpt_app2 (cpt_const [false, false]) hT))))
    (fun _ => rfl)

def rnd (y : List Bool) : List Bool :=
  outI (unpairB y).1 (dropI^[(unpairB y).1.length] (unpairB y).2)

theorem cpt_rnd : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) rnd :=
  cpt_outI cpt_unpairB1 (cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 cpt_unpairB2)

theorem cpt_G : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) G :=
  cptE (cpt_flatMapRange cpt_rnd cpt_id cpt_id) (fun x => by
    simp only [rnd, unpairB_pairB, un_length]
    rfl)

theorem cpt_g : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) g :=
  cptE (cpt_sel cpt_wfF (cpt_const [false])
    (cpt_app2 (cpt_const (encodeClause [(Y 0, true)])) cpt_G)) (fun _ => rfl)

end PEqualNP.Library.SearchHelpers.KSat.Hard

namespace PEqualNP.Library.SearchHelpers.KSat

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV Hard

theorem sat_reduces_ksat3 :
    PEqualNP.Library.PolyTimeReducible PEqualNP.Search.SAT (PEqualNP.Search.KSAT 3) := by
  refine ⟨g, cpt_g, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨φ, rfl, hs⟩
    exact ⟨split φ, isKCNF_split φ, (g_enc φ).symm, (satisfiable_split φ).2 hs⟩
  · rintro ⟨ψ, -, he, hs⟩
    cases hw : wfB x with
    | false =>
      rw [g_not x hw] at he
      exact absurd he (not_enc_false ψ)
    | true =>
      obtain ⟨φ, rfl⟩ := (wfB_iff x).1 hw
      rw [g_enc φ] at he
      obtain rfl := encodeCNF_injective he
      exact ⟨φ, rfl, (satisfiable_split φ).1 hs⟩

end PEqualNP.Library.SearchHelpers.KSat

end

section

namespace PEqualNP.MetaComplexity.Helpers.Machines

open Turing PEqualNP.Library.Machines

namespace StrEq

abbrev SΓ (A : Type) : Bool × Bool → Type
  | (false, false) => A ⊕ A
  | (false, true) => Option A
  | (true, false) => Option A
  | (true, true) => Bool

inductive SL : Type
  | split
  | cmp
  deriving DecidableEq

instance : Fintype SL :=
  Fintype.ofList [SL.split, SL.cmp] (fun x => by cases x <;> simp)

abbrev Sσ (A : Type) : Type := Option A × Option A × Bool

variable {A : Type}

def eqProg [DecidableEq A] : SL → TM2.Stmt (SΓ A) SL (Sσ A)
  | .split =>
    .pop (false, false)
      (fun _ (o : Option (A ⊕ A)) => (o.bind Sum.getLeft?, o.bind Sum.getRight?, true))
      (.branch (fun s => s.1.isSome)
        (.push (false, true) (fun s => s.1) (.goto fun _ => .split))
        (.branch (fun s => s.2.1.isSome)
          (.push (true, false) (fun s => s.2.1) (.goto fun _ => .split))
          (.goto fun _ => .cmp)))
  | .cmp =>
    .pop (false, true) (fun s (o : Option (Option A)) => (o.join, s.2.1, s.2.2))
      (.pop (true, false) (fun s (o : Option (Option A)) => (s.1, o.join, s.2.2))
        (.branch (fun s => s.1.isSome || s.2.1.isSome)
          (.load (fun s => (none, none, s.2.2 && decide (s.1 = s.2.1))) (.goto fun _ => .cmp))
          (.push (true, true) (fun s => s.2.2) (.load (fun _ => (none, none, false)) .halt))))

def eqM (A : Type) [Fintype A] [DecidableEq A] : FinTM2 where
  K := Bool × Bool
  k₀ := (false, false)
  k₁ := (true, true)
  Γ := SΓ A
  Λ := SL
  main := .split
  σ := Sσ A
  initialState := (none, none, false)
  Γk₀Fin := inferInstanceAs (Fintype (A ⊕ A))
  m := eqProg

def lst (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) : ∀ k, List (SΓ A k)
  | (false, false) => l
  | (false, true) => u
  | (true, false) => v
  | (true, true) => o

theorem lst_in (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (false, false) = l := rfl

theorem lst_a (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (false, true) = u := rfl

theorem lst_b (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (true, false) = v := rfl

theorem lst_out (l : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    lst l u v o (true, true) = o := rfl

theorem lst_set_in (l l' : List (A ⊕ A)) (u v : List (Option A)) (o : List Bool) :
    Function.update (lst l u v o) (false, false) l' = lst l' u v o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_a (l : List (A ⊕ A)) (u u' v : List (Option A)) (o : List Bool) :
    Function.update (lst l u v o) (false, true) u' = lst l u' v o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b (l : List (A ⊕ A)) (u v v' : List (Option A)) (o : List Bool) :
    Function.update (lst l u v o) (true, false) v' = lst l u v' o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_out (l : List (A ⊕ A)) (u v : List (Option A)) (o o' : List Bool) :
    Function.update (lst l u v o) (true, true) o' = lst l u v o' := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_start (l : List (A ⊕ A)) :
    lst l [] [] [] = Function.update (fun _ => [] : ∀ k, List (SΓ A k)) (false, false) l := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_end (o : List Bool) :
    lst ([] : List (A ⊕ A)) [] [] o =
      Function.update (fun _ => [] : ∀ k, List (SΓ A k)) (true, true) o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

abbrev SCfg (A : Type) : Type := TM2.Cfg (SΓ A) SL (Sσ A)

variable [DecidableEq A]

abbrev eqStep : Option (SCfg A) → Option (SCfg A) := flip bind (TM2.step eqProg)

theorem split_inl (s : Sσ A) (a : A) (l : List (A ⊕ A)) (u v : List (Option A))
    (o : List Bool) :
    TM2.step eqProg (⟨some .split, s, lst (Sum.inl a :: l) u v o⟩ : SCfg A) =
      some ⟨some .split, (some a, none, true), lst l (some a :: u) v o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.bind_some, Sum.getLeft?_inl,
    Sum.getRight?_inl, Option.isSome_some, Bool.cond_true]
  rw [lst_set_in, lst_a, lst_set_a]

theorem split_inr (s : Sσ A) (a : A) (l : List (A ⊕ A)) (u v : List (Option A))
    (o : List Bool) :
    TM2.step eqProg (⟨some .split, s, lst (Sum.inr a :: l) u v o⟩ : SCfg A) =
      some ⟨some .split, (none, some a, true), lst l u (some a :: v) o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.bind_some, Sum.getLeft?_inr,
    Sum.getRight?_inr, Option.isSome_some, Option.isSome_none, Bool.cond_true, Bool.cond_false]
  rw [lst_set_in, lst_b, lst_set_b]

theorem split_nil (s : Sσ A) (u v : List (Option A)) (o : List Bool) :
    TM2.step eqProg (⟨some .split, s, lst [] u v o⟩ : SCfg A) =
      some ⟨some .cmp, (none, none, true), lst [] u v o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_nil, List.tail_nil, Option.bind_none, Option.isSome_none, Bool.cond_false]
  rw [lst_set_in]

theorem cmp_step (s : Sσ A) (x y : List A) (o : List Bool) (h : x ≠ [] ∨ y ≠ []) :
    TM2.step eqProg (⟨some .cmp, s, lst [] (x.map some) (y.map some) o⟩ : SCfg A) =
      some ⟨some .cmp, (none, none, s.2.2 && decide (x.head? = y.head?)),
        lst [] (x.tail.map some) (y.tail.map some) o⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_a, lst_set_a, lst_b, lst_set_b]
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp at h ⊢

theorem cmp_nil (s : Sσ A) (o : List Bool) :
    TM2.step eqProg (⟨some .cmp, s, lst [] [] [] o⟩ : SCfg A) =
      some ⟨none, (none, none, false), lst [] [] [] (s.2.2 :: o)⟩ := by
  simp only [TM2.step, eqProg, TM2.stepAux]
  rw [lst_a, lst_set_a, lst_b, lst_set_b]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none, Bool.or_self,
    Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem splitLoop :
    ∀ (l : List (A ⊕ A)) (u v : List (Option A)) (s : Sσ A),
      eqStep^[l.length + 1] (some (⟨some .split, s, lst l u v []⟩ : SCfg A)) =
        some ⟨some .cmp, (none, none, true),
          lst [] ((l.filterMap Sum.getLeft?).reverse.map some ++ u)
            ((l.filterMap Sum.getRight?).reverse.map some ++ v) []⟩ := by
  intro l
  induction l with
  | nil => intro u v s; exact split_nil s u v []
  | cons x l ih =>
    intro u v s
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : eqStep (some (⟨some .split, s, lst (Sum.inl a :: l) u v []⟩ : SCfg A)) =
          some ⟨some .split, (some a, none, true), lst l (some a :: u) v []⟩ :=
        split_inl s a l u v []
      rw [e, ih]
      simp [List.filterMap_cons]
    | inr a =>
      have e : eqStep (some (⟨some .split, s, lst (Sum.inr a :: l) u v []⟩ : SCfg A)) =
          some ⟨some .split, (none, some a, true), lst l u (some a :: v) []⟩ :=
        split_inr s a l u v []
      rw [e, ih]
      simp [List.filterMap_cons]

theorem flag_step (f : Bool) (x y : List A) :
    (f && decide (x.head? = y.head?) && decide (x.tail = y.tail)) = (f && decide (x = y)) := by
  rw [Bool.eq_iff_iff]
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨b, y⟩ <;> simp [and_assoc]
  intro _ _
  exact decide_eq_true_iff

theorem cmpLoop :
    ∀ (n : ℕ) (x y : List A) (s : Sσ A), max x.length y.length = n →
      eqStep^[n + 1] (some (⟨some .cmp, s, lst [] (x.map some) (y.map some) []⟩ : SCfg A)) =
        some ⟨none, (none, none, false), lst [] [] [] [s.2.2 && decide (x = y)]⟩ := by
  intro n
  induction n with
  | zero =>
    intro x y s h
    have hx : x = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : y = [] := List.length_eq_zero_iff.mp (by omega)
    subst hx hy
    rw [show (s.2.2 && decide (([] : List A) = [])) = s.2.2 by simp]
    exact cmp_nil s []
  | succ n ih =>
    intro x y s h
    rw [Function.iterate_succ_apply]
    have hne : x ≠ [] ∨ y ≠ [] := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rw [hc.1, hc.2] at h
      simp at h
    have e : eqStep (some (⟨some .cmp, s, lst [] (x.map some) (y.map some) []⟩ : SCfg A)) =
        some ⟨some .cmp, (none, none, s.2.2 && decide (x.head? = y.head?)),
          lst [] (x.tail.map some) (y.tail.map some) []⟩ := cmp_step s x y [] hne
    rw [e, ih x.tail y.tail _ (by simp only [List.length_tail]; omega)]
    exact congrArg (fun b => some (⟨none, (none, none, false), lst [] [] [] [b]⟩ : SCfg A))
      (flag_step s.2.2 x y)

theorem eq_run [Fintype A] (p : List A × List A) :
    ∃ n, n ≤ 2 * (Gen.gpair (p.1, p.2)).length + 2 ∧
      eqStep^[n] (some (initList (eqM A) (Gen.gpair (p.1, p.2)))) =
        some (haltList (eqM A) [decide (p.1 = p.2)]) := by
  have hs := splitLoop (Gen.gpair (p.1, p.2)) [] [] (none, none, false)
  rw [Gen.gpair_left, Gen.gpair_right, List.append_nil, List.append_nil] at hs
  have hc := cmpLoop (max p.1.reverse.length p.2.reverse.length) p.1.reverse p.2.reverse
    (none, none, true) rfl
  have hd : (true && decide (p.1.reverse = p.2.reverse)) = decide (p.1 = p.2) := by simp
  rw [hd] at hc
  refine ⟨(max p.1.reverse.length p.2.reverse.length + 1) +
    ((Gen.gpair (p.1, p.2)).length + 1), ?_, ?_⟩
  · rw [Gen.gpair_length, List.length_reverse, List.length_reverse]
    omega
  · refine (congrArg (fun c => eqStep^[_] (some c)) (initList_eq (eqM A) _)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq (eqM A) [decide (p.1 = p.2)])).symm)
    show eqStep^[_]
      (some (⟨some .split, (none, none, false),
        Function.update (fun _ => []) (false, false) (Gen.gpair (p.1, p.2))⟩ : SCfg A)) =
      some (⟨none, (none, none, false),
        Function.update (fun _ => []) (true, true) [decide (p.1 = p.2)]⟩ : SCfg A)
    rw [← lst_start, ← lst_end, Function.iterate_add_apply, hs, hc]

end StrEq

open StrEq in

theorem strEq_polyTime {A : Type} [Fintype A] [DecidableEq A] :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : List A × List A => PEqualNP.Library.Machines.Gen.gpair (p.1, p.2))
      Computability.encodeBool (fun p : List A × List A => decide (p.1 = p.2))) :=
  ⟨{
    tm := eqM A
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun p =>
      { steps := Classical.choose (eq_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.1 = p.2)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.1 = p.2))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => eqStep^[Classical.choose (eq_run p)]
            (some (initList (eqM A) x))) (hm _ (Gen.gpair (p.1, p.2)))).trans
            ((Classical.choose_spec (eq_run p)).2.trans
              (congrArg (fun x => some (haltList (eqM A) x)) hout))
        steps_le_m := by
          have h := (Classical.choose_spec (eq_run p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

end PEqualNP.MetaComplexity.Helpers.Machines

end

namespace PEqualNP.Outside.M500

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.Tab.StepW
  PEqualNP.Library.SearchHelpers.KSat.Hard

abbrev CP (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

theorem cpE {f f' : List Bool → List Bool} (h : CP f) (e : ∀ a, f a = f' a) : CP f' := by
  obtain rfl : f = f' := funext e
  exact h

theorem findIdx_map' {α β : Type} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).findIdx q = l.findIdx (fun x => q (f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.findIdx_cons, ih]

theorem findIdx_range_succ (q : ℕ → Bool) (n : ℕ) :
    (List.range (n + 1)).findIdx q =
      if q 0 = true then 0 else (List.range n).findIdx (fun j => q (j + 1)) + 1 := by
  rw [List.range_succ_eq_map, List.findIdx_cons, findIdx_map']

theorem hd_un (k : ℕ) (a : List Bool) : hd (un k ++ false :: a) = un k := by
  induction k with
  | zero => simp [hd, un]
  | succ k ih =>
    rw [un_succ]
    simp only [hd] at ih
    simp [hd, ih]

theorem dropN_un (k : ℕ) (a : List Bool) : dropN (un k ++ false :: a) = a := by
  induction k with
  | zero => simp [dropN, un]
  | succ k ih =>
    rw [un_succ]
    simp only [dropN] at ih
    simp [dropN, ih]

theorem first_iter (g : List Bool → List Bool) (a : List Bool) (t : ℕ → Bool)
    (hg : ∀ i, g (un i ++ false :: a) =
      if t i = true then un i ++ false :: a else un (i + 1) ++ false :: a) :
    ∀ (n i : ℕ), g^[n] (un i ++ false :: a) =
      un (i + (List.range n).findIdx (fun j => t (i + j))) ++ false :: a := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [Function.iterate_succ_apply, hg i, findIdx_range_succ]
    by_cases h : t i = true
    · have hfix : g (un i ++ false :: a) = un i ++ false :: a := by
        rw [hg i]
        simp [h]
      simp only [Nat.add_zero, h, ↓reduceIte]
      exact Function.iterate_fixed hfix n
    · have hb : t i = false := by simpa using h
      simp only [Nat.add_zero, hb, Bool.false_eq_true, ↓reduceIte]
      rw [ih (i + 1)]
      have e : (fun j => t (i + 1 + j)) = (fun j => t (i + (j + 1))) := by
        funext j
        congr 1
        omega
      rw [e]
      congr 2
      omega

theorem cpt_first {p cnt arg : List Bool → List Bool} (hp : CP p) (hcnt : CP cnt)
    (harg : CP arg) :
    CP (fun s => un ((List.range (cnt s).length).findIdx
      (fun i => !(p (pairB (un i) (arg s))).isEmpty))) := by
  have hq : CP (fun y => pairB (hd y) (dropN y)) := cpt_pairB2 cpt_hd cpt_dropN
  have hg : CP (fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y) :=
    cpt_sel (cpt_comp hq hp) (cpt_cons1 true cpt_id) cpt_id
  have hit : CP (fun s => (fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y)^[(cnt s).length]
      (false :: arg s)) :=
    cpt_iterGrow hg 1
      (by
        intro y
        simp only [sel]
        split_ifs <;> simp)
      hcnt (cpt_cons1 false harg)
  refine cpE (cpt_comp hit cpt_hd) ?_
  intro s
  have h := first_iter (fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y) (arg s)
    (fun i => !(p (pairB (un i) (arg s))).isEmpty)
    (by
      intro i
      rw [hd_un, dropN_un]
      by_cases h0 : p (pairB (un i) (arg s)) = []
      · simp [sel, h0, un_succ]
      · simp [sel, h0])
    (cnt s).length 0
  simp only [un_zero, List.nil_append, Nat.zero_add] at h
  show hd ((fun y => sel (p (pairB (hd y) (dropN y))) (true :: y) y)^[(cnt s).length]
    (false :: arg s)) = _
  rw [h, hd_un]

def halfU (u : List Bool) : List Bool := un (u.length / 2)

def parU (u : List Bool) : List Bool := [decide (u.length % 2 = 1)]

def hfD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, none)
  | true, _ => (false, some true)

theorem hfD_run (l : List Bool) :
    fstRun hfD (fun _ => none) false l = un (l.length / 2) ∧
      fstRun hfD (fun _ => none) true l = un ((l.length + 1) / 2) := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons a l ih =>
    constructor
    · simp only [fstRun, hfD, Option.toList_none, List.nil_append, ih.2, List.length_cons]
    · simp only [fstRun, hfD, Option.toList_some, ih.1, List.length_cons]
      rw [show (l.length + 1 + 1) / 2 = l.length / 2 + 1 by omega, un_succ]
      rfl

theorem cpt_halfU : CP halfU :=
  fst_polyTime _ _ _ hfD (fun _ => none) false (fun s => (hfD_run s).1.symm)

def paD : Bool → Bool → Bool × Option Bool
  | q, _ => (!q, none)

theorem paD_run (l : List Bool) : ∀ q : Bool,
    fstRun paD (fun q => some q) q l = [xor q (decide (l.length % 2 = 1))] := by
  induction l with
  | nil => intro q; simp [fstRun]
  | cons a l ih =>
    intro q
    simp only [fstRun, paD, Option.toList_none, List.nil_append, ih, List.length_cons]
    by_cases h : l.length % 2 = 1
    · have h2 : ¬ (l.length + 1) % 2 = 1 := by omega
      cases q <;> simp [h, h2]
    · have h2 : (l.length + 1) % 2 = 1 := by omega
      cases q <;> simp [h, h2]

theorem cpt_parU : CP parU :=
  fst_polyTime _ _ _ paD (fun q => some q) false (fun s => by
    rw [paD_run]
    simp [parU])

def binStep (y : List Bool) : List Bool :=
  sel (unpairB y).1 y
    (pairB (halfU (unpairB y).1) ((unpairB y).2 ++ true :: parU (unpairB y).1))

def binU (u : List Bool) : List Bool := (unpairB (binStep^[u.length] (pairB u []))).2

theorem binStep_length (y : List Bool) : (binStep y).length ≤ y.length + 2 := by
  have h := unpairB_length y
  simp only [binStep, sel]
  split_ifs with h0
  · omega
  · have h1 : 1 ≤ (unpairB y).1.length := by
      rcases hl : (unpairB y).1 with _ | ⟨b, t⟩
      · exact absurd hl h0
      · simp
    simp only [pairB, halfU, parU, un, List.length_append, List.length_cons, List.length_replicate,
      List.length_nil]
    omega

theorem cpt_binStep : CP binStep :=
  cpt_sel cpt_unpairB1 cpt_id
    (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_halfU)
      (cpt_app2 cpt_unpairB2 (cpt_cons1 true (cpt_comp cpt_unpairB1 cpt_parU))))

theorem bits_pos (k : ℕ) (hk : 0 < k) :
    k.bits = decide (k % 2 = 1) :: (k / 2).bits := by
  have h := Nat.bits_append_bit (k / 2) (decide (k % 2 = 1))
    (by
      intro h0
      have : k % 2 = 1 := by omega
      simp [this])
  have e : Nat.bit (decide (k % 2 = 1)) (k / 2) = k := by
    rw [Nat.bit_val]
    by_cases h1 : k % 2 = 1
    · simp only [h1, decide_true, Bool.toNat_true]
      omega
    · simp only [h1, decide_false, Bool.toNat_false]
      omega
  rw [e] at h
  exact h

theorem binStep_iter : ∀ (n k : ℕ) (out : List Bool), k ≤ n →
    binStep^[n] (pairB (un k) out) = pairB [] (out ++ k.bits.flatMap (fun d => [true, d])) := by
  intro n
  induction n with
  | zero =>
    intro k out hk
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    intro k out hk
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · have e : binStep (pairB (un 0) out) = pairB (un 0) out := by
        simp [binStep, unpairB_pairB, sel]
      rw [e]
      exact ih 0 out (by omega)
    · have e : binStep (pairB (un k) out) =
          pairB (un (k / 2)) (out ++ [true, decide (k % 2 = 1)]) := by
        have hne : un k ≠ [] := by
          intro h0
          have := congrArg List.length h0
          simp at this
          omega
        simp [binStep, unpairB_pairB, sel, hne, halfU, parU]
      rw [e, ih (k / 2) _ (by omega), bits_pos k hpos]
      simp

theorem binU_un (k : ℕ) : binU (un k) = k.bits.flatMap (fun d => [true, d]) := by
  simp only [binU, un_length]
  rw [binStep_iter k k [] le_rfl, unpairB_pairB]
  rfl

theorem cpt_binU {U : List Bool → List Bool} (hU : CP U) : CP (fun s => binU (U s)) :=
  cpE (cpt_comp (cpt_iterGrow cpt_binStep 2 binStep_length hU (cpt_pairB2 hU (cpt_const [])))
    cpt_unpairB2) (fun _ => rfl)

theorem cpt_eqF {u v : List Bool → List Bool} (hu : CP u) (hv : CP v) :
    CP (fun s => bflag (decide (u s = v s))) := by
  have s : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  exact cpE (cpt_bitFlag (cpt_comp (cpt_pair hu hv) s)) (fun _ => rfl)

def testP (s : List Bool) : List Bool :=
  bflag (decide ((headI (dropI^[(unpairB s).1.length] (unpairB (unpairB s).2).2)).tail.tail =
    ((unpairB (unpairB s).2).1).tail.tail))

theorem cpt_testP : CP testP := by
  have h1 : CP (fun s => (unpairB (unpairB s).2).1) :=
    cpt_comp (f := fun s : List Bool => (unpairB s).2) (g := fun s : List Bool => (unpairB s).1)
      cpt_unpairB2 cpt_unpairB1
  have h2 : CP (fun s => (unpairB (unpairB s).2).2) :=
    cpt_comp (f := fun s : List Bool => (unpairB s).2) (g := fun s : List Bool => (unpairB s).2)
      cpt_unpairB2 cpt_unpairB2
  exact cpt_eqF
    (cpt_tail1 (cpt_tail1 (cpt_comp (cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 h2)
      cpt_headI)))
    (cpt_tail1 (cpt_tail1 h1))

def Kfun (it x : List Bool) : List Bool :=
  un ((List.range x.length).findIdx (fun j => !(testP (pairB (un j) (pairB it x))).isEmpty))

theorem cpt_K {I X : List Bool → List Bool} (hI : CP I) (hX : CP X) :
    CP (fun s => Kfun (I s) (X s)) :=
  cpE (cpt_first cpt_testP hX (cpt_pairB2 hI hX)) (fun _ => rfl)

def litR (it x : List Bool) : List Bool :=
  tk [true, true] it ++ (binU (Kfun it x) ++ [false, true])

theorem cpt_litR {I X : List Bool → List Bool} (hI : CP I) (hX : CP X) :
    CP (fun s => litR (I s) (X s)) :=
  cpE (cpt_app2 (cpt_tk (cpt_const [true, true]) hI)
    (cpt_app2 (cpt_binU (cpt_K hI hX)) (cpt_const [false, true]))) (fun _ => rfl)

def outR (x r : List Bool) : List Bool :=
  sel r [] (sel (bflag (isEnd r)) (litR (headI r) x) [false, false])

theorem cpt_outR {X R : List Bool → List Bool} (hX : CP X) (hR : CP R) :
    CP (fun s => outR (X s) (R s)) := by
  have hEnd : CP (fun s => bflag (isEnd (R s))) := cpE (cpt_comp hR cpt_isEndF) (fun _ => rfl)
  have hH : CP (fun s => headI (R s)) := cpt_comp hR cpt_headI
  exact cpE (cpt_sel hR (cpt_const []) (cpt_sel hEnd (cpt_litR hH hX) (cpt_const [false, false])))
    (fun _ => rfl)

def rndR (y : List Bool) : List Bool :=
  outR (unpairB y).2 (dropI^[(unpairB y).1.length] (unpairB y).2)

theorem cpt_rndR : CP rndR :=
  cpt_outR cpt_unpairB2 (cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 cpt_unpairB2)

def GR (x : List Bool) : List Bool :=
  (List.range x.length).flatMap fun i => outR x (dropI^[i] x)

theorem cpt_GR : CP GR :=
  cpE (cpt_flatMapRange cpt_rndR cpt_id cpt_id) (fun x => by
    simp only [rndR, unpairB_pairB, un_length]
    rfl)

def items (φ : CNF) : List (Option Literal) := φ.flatMap (fun c => c.map some ++ [none])

def encIt : Option Literal → List Bool
  | some l => encodeLiteral l
  | none => [false, false]

def encIts (L : List (Option Literal)) : List Bool := L.flatMap encIt

theorem encIts_cons (o : Option Literal) (L : List (Option Literal)) :
    encIts (o :: L) = encIt o ++ encIts L := rfl

theorem encIts_append (L M : List (Option Literal)) :
    encIts (L ++ M) = encIts L ++ encIts M := by
  simp [encIts]

theorem encIts_clause (c : Clause) :
    encIts (c.map some ++ [none]) = encodeClause c := by
  induction c with
  | nil => simp [encIts, encIt, encodeClause]
  | cons l c ih =>
    simp only [List.map_cons, List.cons_append, encIts_cons, ih, encIt]
    simp [encodeClause]

theorem encIts_items (φ : CNF) : encIts (items φ) = encodeCNF φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e : items (c :: φ) = (c.map some ++ [none]) ++ items φ := by simp [items]
    rw [e, encIts_append, encIts_clause, ih]
    simp [encodeCNF]

theorem headI_it (o : Option Literal) (r : List Bool) : headI (encIt o ++ r) = encIt o := by
  cases o with
  | none => rfl
  | some l => exact headI_lit l r

theorem dropI_it (o : Option Literal) (r : List Bool) : dropI (encIt o ++ r) = r := by
  cases o with
  | none => rfl
  | some l => exact dropI_lit l r

theorem encIt_length (o : Option Literal) : 1 ≤ (encIt o).length := by
  cases o with
  | none => simp [encIt]
  | some l => simp [encIt, encodeLiteral_eq]

theorem encIts_length (L : List (Option Literal)) : L.length ≤ (encIts L).length := by
  induction L with
  | nil => simp
  | cons o L ih =>
    have := encIt_length o
    rw [encIts_cons, List.length_append, List.length_cons]
    omega

theorem tt_it (o : Option Literal) (v : ℕ) :
    decide ((encIt o).tail.tail = vcode v) = o.any (fun l' => l'.1 == v) := by
  cases o with
  | none =>
    have h : ¬ ([] : List Bool) = vcode v := fun h => vcode_ne_nil v h.symm
    simp [encIt, h]
  | some l =>
    simp only [encIt, encodeLiteral_eq, List.tail_cons, Option.any_some]
    by_cases h : l.1 = v
    · simp [h]
    · have h2 : ¬ vcode l.1 = vcode v := fun e => h (vcode_injective e)
      simp [h, h2]

theorem find_spec (v : ℕ) : ∀ (L : List (Option Literal)) (n : ℕ) (rest : List Bool),
    (∃ o ∈ L, o.any (fun l' => l'.1 == v) = true) → L.length ≤ n →
    (List.range n).findIdx (fun j =>
      decide ((headI (dropI^[j] (encIts L ++ rest))).tail.tail = vcode v)) =
      L.findIdx (fun o => o.any (fun l' => l'.1 == v)) := by
  intro L
  induction L with
  | nil =>
    intro n rest h
    obtain ⟨o, ho, -⟩ := h
    simp at ho
  | cons o L ih =>
    intro n rest h hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [findIdx_range_succ, List.findIdx_cons]
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply, encIts_cons,
      List.append_assoc, headI_it, dropI_it, tt_it]
    by_cases h0 : o.any (fun l' => l'.1 == v) = true
    · simp [h0]
    · have hL : ∃ o' ∈ L, o'.any (fun l' => l'.1 == v) = true := by
        obtain ⟨o', ho', h1⟩ := h
        rcases List.mem_cons.1 ho' with rfl | hm
        · exact absurd h1 h0
        · exact ⟨o', hm, h1⟩
      have hb : o.any (fun l' => l'.1 == v) = false := by simpa using h0
      rw [ih n rest hL (by simp at hn; omega)]

theorem Kfun_spec (φ : CNF) (l : Literal) (hl : some l ∈ items φ) :
    Kfun (encodeLiteral l) (encodeCNF φ) =
      un ((items φ).findIdx (fun o => o.any (fun l' => l'.1 == l.1))) := by
  have h := find_spec l.1 (items φ) (encodeCNF φ).length []
    ⟨some l, hl, by simp⟩ (by rw [← encIts_items]; exact encIts_length _)
  rw [List.append_nil, encIts_items] at h
  rw [Kfun, ← h]
  congr 2
  funext j
  simp only [testP, unpairB_pairB, un_length, encodeLiteral_eq, List.tail_cons]
  cases hd : decide ((headI (dropI^[j] (encodeCNF φ))).tail.tail = vcode l.1) <;> simp [bflag]

def ren (φ : CNF) (l : Literal) : Literal :=
  ((items φ).findIdx (fun o => o.any (fun l' => l'.1 == l.1)), l.2)

theorem litR_spec (φ : CNF) (l : Literal) (hl : some l ∈ items φ) :
    litR (encodeLiteral l) (encodeCNF φ) = encodeLiteral (ren φ l) := by
  rw [litR, Kfun_spec φ l hl, binU_un, tk_eq, encodeLiteral_eq, encodeLiteral_eq]
  simp [ren, vcode]

def walkR (x : List Bool) : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, r => outR x r ++ walkR x n (dropI r)

theorem walkR_range (x : List Bool) (n : ℕ) : ∀ r : List Bool,
    (List.range n).flatMap (fun i => outR x (dropI^[i] r)) = walkR x n r := by
  induction n with
  | zero => intro r; rfl
  | succ n ih =>
    intro r
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, walkR, ← ih]
    rfl

theorem walkR_nil (x : List Bool) (n : ℕ) : walkR x n [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walkR, outR, sel, dropI, ih]

theorem walkR_items (φ : CNF) : ∀ (L : List (Option Literal)) (n : ℕ),
    (∀ o ∈ L, o ∈ items φ) → L.length ≤ n →
    walkR (encodeCNF φ) n (encIts L) = encIts (L.map (Option.map (ren φ))) := by
  intro L
  induction L with
  | nil => intro n _ _; exact walkR_nil _ _
  | cons o L ih =>
    intro n hm hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [walkR, encIts_cons, dropI_it, ih n (fun o' ho' => hm o' (List.mem_cons_of_mem _ ho'))
      (by simp at hn; omega), List.map_cons, encIts_cons]
    congr 1
    cases o with
    | none => simp [outR, encIt, sel, bflag, isEnd]
    | some l =>
      have hne : encodeLiteral l ++ encIts L ≠ [] := by simp [encodeLiteral_eq]
      simp only [outR, encIt, Option.map_some, isEnd_lit, headI_lit,
        litR_spec φ l (hm _ List.mem_cons_self), sel, bflag, hne]
      simp

theorem items_map (f : Literal → Literal) (φ : CNF) :
    items (φ.map (fun c => c.map f)) = (items φ).map (Option.map f) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have e1 : items (c :: φ) = (c.map some ++ [none]) ++ items φ := by simp [items]
    have e2 : items ((c :: φ).map (fun c => c.map f)) =
        ((c.map f).map some ++ [none]) ++ items (φ.map (fun c => c.map f)) := by simp [items]
    rw [e1, e2, ih]
    simp

theorem GR_enc (φ : CNF) :
    GR (encodeCNF φ) = encodeCNF (φ.map (fun c => c.map (ren φ))) := by
  rw [GR, walkR_range]
  have h := walkR_items φ (items φ) (encodeCNF φ).length (fun o ho => ho)
    (by rw [← encIts_items]; exact encIts_length _)
  rw [encIts_items] at h
  rw [h, ← items_map, encIts_items]

end PEqualNP.Outside.M500

open PEqualNP.Outside.M500 in
theorem PEqualNP.Outside.L_meta_500 : PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF PEqualNP.Search.encodeCNF (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) := by
  obtain ⟨c⟩ := cpt_GR
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun φ => by
    have h := c.outputsFun (PEqualNP.Search.encodeCNF φ)
    rw [GR_enc φ] at h
    exact h⟩⟩
