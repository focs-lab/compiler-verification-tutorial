/-
  The target language (a stack machine), the compiler, and its correctness
  proofs.

  Lean 4 port of `Compil.v` from the Coq development accompanying
  Xavier Leroy, *Proving the correctness of a compiler*,
  EUTypes 2019 Summer School.

  Original Coq sources: Copyright 2019, 2025 Xavier Leroy.
  This file is a modified work: the definitions and theorem statements follow
  the Coq originals, but all proofs and explanatory text have been rewritten
  for Lean 4.

  Distributed under the GNU Lesser General Public License, version 2.1
  or (at your option) any later version.  See LICENSE.md.
-/
import CompilerVerification.IMP

/-!
# Compiling IMP to a stack machine

The target is a machine in the style of an old RPN pocket calculator: a stack
holds intermediate results, and each instruction pops its arguments off the
stack and pushes its result back.

The plan of this file:

1. the instruction set and its operational semantics;
2. the compilation scheme;
3. correctness for *terminating* source programs, proved against the big-step
   semantics of IMP;
4. correctness for *all* source programs, terminating or diverging, proved as
   a simulation diagram against the continuation semantics of IMP.

Step 4 is the real theorem.  Step 3 is a warm-up that already contains the
essential inductions on expressions.
-/

namespace Compil

open IMP Sequences

/-! ## The machine -/

/-- The instruction set. -/
inductive instr where
  /-- push the integer `n` -/
  | const (n : Int)
  /-- push the current value of variable `x` -/
  | var (x : Ident)
  /-- pop an integer, assign it to variable `x` -/
  | setvar (x : Ident)
  /-- pop two integers, push their sum -/
  | add
  /-- pop one integer, push its opposite -/
  | opp
  /-- skip `d` instructions forward (or backward if `d < 0`) -/
  | branch (d : Int)
  /-- pop two integers; skip `d₁` instructions if equal, `d₀` if not -/
  | beq (d₁ d₀ : Int)
  /-- pop two integers; skip `d₁` instructions if `≤`, `d₀` if `>` -/
  | ble (d₁ d₀ : Int)
  /-- stop execution -/
  | halt
  deriving Repr, DecidableEq

/-- A piece of machine code is a list of instructions. -/
abbrev Code := List instr

/-- The number of instructions in a piece of code, as an integer — program
counters are integers, since branches may go backwards. -/
def codelen (c : Code) : Int := (c.length : Int)

@[simp] theorem codelen_nil : codelen [] = 0 := rfl

@[simp] theorem codelen_cons (i : instr) (c : Code) : codelen (i :: c) = codelen c + 1 := by
  simp [codelen]

@[simp] theorem codelen_app (c₁ c₂ : Code) :
    codelen (c₁ ++ c₂) = codelen c₁ + codelen c₂ := by
  simp [codelen]

theorem codelen_nonneg (c : Code) : 0 ≤ codelen c := by
  simp [codelen]

/-- The machine's evaluation stack. -/
abbrev Stack := List Int

/-- A machine configuration: program counter, stack, store.  The code itself
is fixed throughout an execution and is carried separately. -/
abbrev Config := Int × Stack × Store

/-- `instrAt C pc` is the instruction at position `pc` in `C`, if any. -/
def instrAt : Code → Int → Option instr
  | [], _ => none
  | i :: C', pc => if pc = 0 then some i else instrAt C' (pc - 1)

/-- The semantics of the machine, in small-step style: one transition per
instruction executed.  `halt` has no transition — that is what makes it stop
the machine rather than get it stuck. -/
inductive transition (C : Code) : Config → Config → Prop where
  | const {pc stk s n} :
      instrAt C pc = some (.const n) →
      transition C (pc, stk, s) (pc + 1, n :: stk, s)
  | var {pc stk s x} :
      instrAt C pc = some (.var x) →
      transition C (pc, stk, s) (pc + 1, s x :: stk, s)
  | setvar {pc stk s x n} :
      instrAt C pc = some (.setvar x) →
      transition C (pc, n :: stk, s) (pc + 1, stk, update x n s)
  | add {pc stk s n₁ n₂} :
      instrAt C pc = some .add →
      transition C (pc, n₂ :: n₁ :: stk, s) (pc + 1, (n₁ + n₂) :: stk, s)
  | opp {pc stk s n} :
      instrAt C pc = some .opp →
      transition C (pc, n :: stk, s) (pc + 1, (-n) :: stk, s)
  | branch {pc stk s d pc'} :
      instrAt C pc = some (.branch d) → pc' = pc + 1 + d →
      transition C (pc, stk, s) (pc', stk, s)
  | beq {pc stk s d₁ d₀ n₁ n₂ pc'} :
      instrAt C pc = some (.beq d₁ d₀) →
      pc' = pc + 1 + (if n₁ = n₂ then d₁ else d₀) →
      transition C (pc, n₂ :: n₁ :: stk, s) (pc', stk, s)
  | ble {pc stk s d₁ d₀ n₁ n₂ pc'} :
      instrAt C pc = some (.ble d₁ d₀) →
      pc' = pc + 1 + (if n₁ ≤ n₂ then d₁ else d₀) →
      transition C (pc, n₂ :: n₁ :: stk, s) (pc', stk, s)

/-- Zero, one or several machine transitions. -/
abbrev transitions (C : Code) : Config → Config → Prop := Star (transition C)

/-- Execution starts at `pc = 0` with an empty stack, and succeeds when it
reaches a `halt` with an empty stack. -/
def machineTerminates (C : Code) (sInit sFinal : Store) : Prop :=
  ∃ pc, transitions C (0, [], sInit) (pc, [], sFinal) ∧ instrAt C pc = some .halt

/-- The machine may instead run forever. -/
def machineDiverges (C : Code) (sInit : Store) : Prop :=
  Infseq (transition C) (0, [], sInit)

/-- Or it may get stuck: no transition applies, and it is not sitting at a
`halt` with an empty stack.  Compiled code never does this. -/
def machineGoesWrong (C : Code) (sInit : Store) : Prop :=
  ∃ pc stk s, transitions C (0, [], sInit) (pc, stk, s)
    ∧ Irred (transition C) (pc, stk, s)
    ∧ (instrAt C pc ≠ some .halt ∨ stk ≠ [])

/-- The outcome of running the machine interpreter below. -/
inductive machineResult where
  /-- the interpreter ran out of fuel -/
  | timeout
  /-- the machine got stuck -/
  | stuck
  /-- the machine halted with this store -/
  | terminates (s : Store)

/-- An executable interpreter for the machine, useful for trying out compiled
code.  As with `cexecBounded`, a fuel argument keeps it total. -/
def machInterp (C : Code) : Nat → Int → Stack → Store → machineResult
  | 0, _, _, _ => .timeout
  | fuel + 1, pc, stk, s =>
    match instrAt C pc, stk with
    | some .halt, [] => .terminates s
    | some (.const n), stk => machInterp C fuel (pc + 1) (n :: stk) s
    | some (.var x), stk => machInterp C fuel (pc + 1) (s x :: stk) s
    | some (.setvar x), n :: stk => machInterp C fuel (pc + 1) stk (update x n s)
    | some .add, n₂ :: n₁ :: stk => machInterp C fuel (pc + 1) ((n₁ + n₂) :: stk) s
    | some .opp, n :: stk => machInterp C fuel (pc + 1) ((-n) :: stk) s
    | some (.branch d), stk => machInterp C fuel (pc + 1 + d) stk s
    | some (.beq d₁ d₀), n₂ :: n₁ :: stk =>
        machInterp C fuel (pc + 1 + (if n₁ = n₂ then d₁ else d₀)) stk s
    | some (.ble d₁ d₀), n₂ :: n₁ :: stk =>
        machInterp C fuel (pc + 1 + (if n₁ ≤ n₂ then d₁ else d₀)) stk s
    | _, _ => .stuck

/-! ## The compilation scheme -/

/-- Code for an arithmetic expression: straight-line code that leaves the
value of the expression on top of the stack.  This is the familiar
translation to reverse Polish notation.  The one twist is that the machine has
no subtraction instruction, so `a - b` is compiled as `a + (-b)`. -/
def compileAexp : aexp → Code
  | .const n => [.const n]
  | .var x => [.var x]
  | .plus a₁ a₂ => compileAexp a₁ ++ compileAexp a₂ ++ [.add]
  | .minus a₁ a₂ => compileAexp a₁ ++ compileAexp a₂ ++ [.opp, .add]

/-- Code for a Boolean expression.  Rather than compute `0` or `1` on the
stack, `compileBexp b d₁ d₀` produces code that *branches*: it skips `d₁`
instructions forward if `b` is true and `d₀` if `b` is false, leaving the
stack and the store unchanged.  This is both shorter and faster, since the
Boolean value is never materialised.

The offsets in the `and` case are the delicate part.  `code₁` is compiled
with a "true" offset of `0`, so that when `b₁` holds we fall straight through
into `code₂`; its "false" offset must skip over the whole of `code₂` and then
take `b`'s own false branch, whence `codelen code₂ + d₀`. -/
def compileBexp : bexp → Int → Int → Code
  | .true, d₁, _ => if d₁ = 0 then [] else [.branch d₁]
  | .false, _, d₀ => if d₀ = 0 then [] else [.branch d₀]
  | .equal a₁ a₂, d₁, d₀ => compileAexp a₁ ++ compileAexp a₂ ++ [.beq d₁ d₀]
  | .lessequal a₁ a₂, d₁, d₀ => compileAexp a₁ ++ compileAexp a₂ ++ [.ble d₁ d₀]
  | .not b₁, d₁, d₀ => compileBexp b₁ d₀ d₁
  | .and b₁ b₂, d₁, d₀ =>
      let code₂ := compileBexp b₂ d₁ d₀
      let code₁ := compileBexp b₁ 0 (codelen code₂ + d₀)
      code₁ ++ code₂

/-- Code for a command.  It updates the store as the command prescribes,
leaves the stack unchanged, and falls through to the instruction following the
generated code. -/
def compileCom : com → Code
  | .skip => []
  | .assign x a => compileAexp a ++ [.setvar x]
  | .seq c₁ c₂ => compileCom c₁ ++ compileCom c₂
  | .ifthenelse b ifso ifnot =>
      let codeIfso := compileCom ifso
      let codeIfnot := compileCom ifnot
      compileBexp b 0 (codelen codeIfso + 1)
        ++ codeIfso
        ++ instr.branch (codelen codeIfnot) :: codeIfnot
  | .while b body =>
      let codeBody := compileCom body
      let codeTest := compileBexp b 0 (codelen codeBody + 1)
      codeTest ++ codeBody ++ [.branch (-(codelen codeTest + codelen codeBody + 1))]

/-- A whole program is a command followed by `halt`, so that it stops cleanly. -/
def compileProgram (p : com) : Code := compileCom p ++ [.halt]

/-- `x := x + 1` compiles to four instructions and a halt. -/
example : compileProgram (.assign "x" (.plus (.var "x") (.const 1)))
    = [.var "x", .const 1, .add, .setvar "x", .halt] := by native_decide

/-- `while true do skip` compiles to a tight infinite loop. -/
example : compileProgram (.while .true .skip) = [.branch (-1), .halt] := by native_decide

example :
    compileProgram (.ifthenelse (.equal (.var "x") (.const 1)) (.assign "x" (.const 0)) .skip)
    = [.var "x", .const 1, .beq 0 3, .const 0, .setvar "x", .branch 0, .halt] := by
  native_decide

/-- The last example shows a small inefficiency: `branch 0` does nothing.
This smart constructor avoids emitting it.  (See the exercises.) -/
def smartBranch (d : Int) : Code := if d = 0 then [] else [.branch d]


/-! ## Reasoning about pieces of code

Compiled code for a sub-expression sits *inside* the code for the whole
program, at some offset.  `CodeAt C pc C'` says that `C'` occurs in `C`
starting at position `pc`; every correctness statement below is relative to
such a hypothesis. -/

/-- `CodeAt C pc C'`: the code `C'` occurs at position `pc` inside `C`. -/
def CodeAt (C : Code) (pc : Int) (C' : Code) : Prop :=
  ∃ C₁ C₃, C = C₁ ++ C' ++ C₃ ∧ pc = codelen C₁

theorem instrAt_app (i : instr) (c₂ c₁ : Code) {pc : Int} (h : pc = codelen c₁) :
    instrAt (c₁ ++ i :: c₂) pc = some i := by
  induction c₁ generalizing pc with
  | nil => subst h; rfl
  | cons a c₁ ih =>
      have hne : pc ≠ 0 := by
        have := codelen_nonneg c₁
        simp only [codelen_cons] at h; omega
      simp only [List.cons_append, instrAt, if_neg hne]
      exact ih (by simp only [codelen_cons] at h; omega)

theorem CodeAt.head {C : Code} {pc : Int} {i : instr} {C' : Code}
    (h : CodeAt C pc (i :: C')) : instrAt C pc = some i := by
  obtain ⟨C₁, C₃, rfl, rfl⟩ := h
  rw [List.append_assoc]
  exact instrAt_app i (C' ++ C₃) C₁ rfl

theorem CodeAt.tail' {C : Code} {pc pc' : Int} {i : instr} {C' : Code}
    (h : CodeAt C pc (i :: C')) (e : pc' = pc + 1) : CodeAt C pc' C' := by
  obtain ⟨C₁, C₃, rfl, rfl⟩ := h
  exact ⟨C₁ ++ [i], C₃, by simp, by simp [e]⟩

theorem CodeAt.tail {C : Code} {pc : Int} {i : instr} {C' : Code}
    (h : CodeAt C pc (i :: C')) : CodeAt C (pc + 1) C' := h.tail' rfl

theorem CodeAt.app_left {C : Code} {pc : Int} {D₁ D₂ : Code}
    (h : CodeAt C pc (D₁ ++ D₂)) : CodeAt C pc D₁ := by
  obtain ⟨C₁, C₃, rfl, rfl⟩ := h
  exact ⟨C₁, D₂ ++ C₃, by simp, rfl⟩

theorem CodeAt.app_right' {C : Code} {pc pc' : Int} {D₁ D₂ : Code}
    (h : CodeAt C pc (D₁ ++ D₂)) (e : pc' = pc + codelen D₁) : CodeAt C pc' D₂ := by
  obtain ⟨C₁, C₃, rfl, rfl⟩ := h
  exact ⟨C₁ ++ D₁, C₃, by simp, by simp [e]⟩

theorem CodeAt.app_right {C : Code} {pc : Int} {D₁ D₂ : Code}
    (h : CodeAt C pc (D₁ ++ D₂)) : CodeAt C (pc + codelen D₁) D₂ := h.app_right' rfl

theorem CodeAt.nil {C : Code} {pc : Int} {D : Code} (h : CodeAt C pc D) : CodeAt C pc [] := by
  obtain ⟨C₁, C₃, rfl, rfl⟩ := h
  exact ⟨C₁, D ++ C₃, by simp, rfl⟩

theorem instrAt_codeAt_nil {C : Code} {pc : Int} {i : instr} (h : instrAt C pc = some i) :
    CodeAt C pc [] := by
  induction C generalizing pc with
  | nil => simp [instrAt] at h
  | cons a C ih =>
      by_cases hpc : pc = 0
      · exact ⟨[], a :: C, by simp, by simp [hpc]⟩
      · simp only [instrAt, if_neg hpc] at h
        obtain ⟨C₁, C₃, hC, he⟩ := ih h
        exact ⟨a :: C₁, C₃, by simp [hC], by simp [codelen_cons]; omega⟩

/-! ### Smart transition lemmas

The transition rules above name the successor program counter explicitly as
`pc + 1`.  When we chain many transitions together, we would rather say "the
next state has *some* program counter `pc'`, and here is the arithmetic that
identifies it" — otherwise every composition needs a rewriting step.  The
following variants take that equation as an argument.  `add'` additionally
lets us name the value pushed, which is what makes the `minus` case below go
through smoothly (the machine computes `n₁ + (-n₂)`, the source expression
denotes `n₁ - n₂`). -/

theorem transition.const' {C : Code} {pc pc' : Int} {stk s n}
    (h : instrAt C pc = some (.const n)) (e : pc' = pc + 1) :
    transition C (pc, stk, s) (pc', n :: stk, s) := by subst e; exact .const h

theorem transition.var' {C : Code} {pc pc' : Int} {stk s x v}
    (h : instrAt C pc = some (.var x)) (hv : v = s x) (e : pc' = pc + 1) :
    transition C (pc, stk, s) (pc', v :: stk, s) := by subst e; subst hv; exact .var h

theorem transition.setvar' {C : Code} {pc pc' : Int} {stk s x n s'}
    (h : instrAt C pc = some (.setvar x)) (hs : s' = update x n s) (e : pc' = pc + 1) :
    transition C (pc, n :: stk, s) (pc', stk, s') := by subst e; subst hs; exact .setvar h

theorem transition.add' {C : Code} {pc pc' : Int} {stk s n₁ n₂ n}
    (h : instrAt C pc = some .add) (hn : n = n₁ + n₂) (e : pc' = pc + 1) :
    transition C (pc, n₂ :: n₁ :: stk, s) (pc', n :: stk, s) := by
  subst e; subst hn; exact .add h

theorem transition.opp' {C : Code} {pc pc' : Int} {stk s n m}
    (h : instrAt C pc = some .opp) (hm : m = -n) (e : pc' = pc + 1) :
    transition C (pc, n :: stk, s) (pc', m :: stk, s) := by subst e; subst hm; exact .opp h

/-! ## Correctness for terminating programs

Each of the three lemmas below states that the generated code meets the
informal specification given when it was defined.  In each case the target
program counter is a variable constrained by an equation, so the pieces
compose without arithmetic rewriting at every step. -/


/-- The code for `a` runs straight through, pushes the value of `a`, and
leaves the store alone. -/
theorem compileAexp_correct {C : Code} {s : Store} (a : aexp) :
    ∀ {pc pc' : Int} {stk : Stack}, CodeAt C pc (compileAexp a) →
    pc' = pc + codelen (compileAexp a) →
    transitions C (pc, stk, s) (pc', aeval s a :: stk, s) := by
  induction a with
  | const n =>
      intro pc pc' stk h e
      exact .one (.const' h.head (by simpa [compileAexp] using e))
  | var x =>
      intro pc pc' stk h e
      exact .one (.var' h.head rfl (by simpa [compileAexp] using e))
  | plus a₁ a₂ ih₁ ih₂ =>
      intro pc pc' stk h e
      simp only [compileAexp] at h e
      have h₃ : instrAt C (pc + codelen (compileAexp a₁) + codelen (compileAexp a₂))
          = some .add :=
        (h.app_right' (by simp only [codelen_app]; omega)).head
      refine (ih₁ h.app_left.app_left rfl).trans
        ((ih₂ (h.app_left.app_right' rfl) rfl).trans (.one (.add' h₃ rfl ?_)))
      simp only [codelen_app, codelen_cons, codelen_nil] at e; omega
  | minus a₁ a₂ ih₁ ih₂ =>
      intro pc pc' stk h e
      simp only [compileAexp] at h e
      have h₃ : CodeAt C (pc + codelen (compileAexp a₁) + codelen (compileAexp a₂))
          [instr.opp, instr.add] := h.app_right' (by simp only [codelen_app]; omega)
      refine (ih₁ h.app_left.app_left rfl).trans
        ((ih₂ (h.app_left.app_right' rfl) rfl).trans
          (.step (.opp' h₃.head rfl rfl) (.one (.add' h₃.tail.head ?_ ?_))))
      · simp only [aeval]; omega
      · simp only [codelen_app, codelen_cons, codelen_nil] at e; omega

/-- The code for `b` leaves the stack and the store unchanged, and branches
`d₁` instructions forward if `b` is true, `d₀` if `b` is false. -/
theorem compileBexp_correct {C : Code} {s : Store} (b : bexp) :
    ∀ (d₁ d₀ : Int) {pc pc' : Int} {stk : Stack}, CodeAt C pc (compileBexp b d₁ d₀) →
    pc' = pc + codelen (compileBexp b d₁ d₀) + (if beval s b then d₁ else d₀) →
    transitions C (pc, stk, s) (pc', stk, s) := by
  induction b with
  | «true» =>
      intro d₁ d₀ pc pc' stk h e
      by_cases hd : d₁ = 0
      · subst hd
        have hpc : pc' = pc := by simp [compileBexp, beval] at e; omega
        subst hpc; exact .refl _
      · simp only [compileBexp, if_neg hd] at h e
        exact .one (.branch h.head (by simp [beval] at e; omega))
  | «false» =>
      intro d₁ d₀ pc pc' stk h e
      by_cases hd : d₀ = 0
      · subst hd
        have hpc : pc' = pc := by simp [compileBexp, beval] at e; omega
        subst hpc; exact .refl _
      · simp only [compileBexp, if_neg hd] at h e
        exact .one (.branch h.head (by simp [beval] at e; omega))
  | equal a₁ a₂ =>
      intro d₁ d₀ pc pc' stk h e
      simp only [compileBexp] at h e
      have h₃ : instrAt C (pc + codelen (compileAexp a₁) + codelen (compileAexp a₂))
          = some (.beq d₁ d₀) := (h.app_right' (by simp only [codelen_app]; omega)).head
      refine (compileAexp_correct a₁ h.app_left.app_left rfl).trans
        ((compileAexp_correct a₂ (h.app_left.app_right' rfl) rfl).trans (.one (.beq h₃ ?_)))
      by_cases hq : aeval s a₁ = aeval s a₂ <;>
        simp only [beval, hq, beq_self_eq_true, if_true, if_false, beq_iff_eq,
          codelen_app, codelen_cons, codelen_nil] at e ⊢ <;>
        simp at e ⊢ <;> omega
  | lessequal a₁ a₂ =>
      intro d₁ d₀ pc pc' stk h e
      simp only [compileBexp] at h e
      have h₃ : instrAt C (pc + codelen (compileAexp a₁) + codelen (compileAexp a₂))
          = some (.ble d₁ d₀) := (h.app_right' (by simp only [codelen_app]; omega)).head
      refine (compileAexp_correct a₁ h.app_left.app_left rfl).trans
        ((compileAexp_correct a₂ (h.app_left.app_right' rfl) rfl).trans (.one (.ble h₃ ?_)))
      by_cases hq : aeval s a₁ ≤ aeval s a₂ <;>
        simp only [beval, hq, decide_true, decide_false, if_true, if_false,
          codelen_app, codelen_cons, codelen_nil] at e ⊢ <;>
        simp at e ⊢ <;> omega
  | not b₁ ih =>
      intro d₁ d₀ pc pc' stk h e
      simp only [compileBexp] at h e
      refine ih d₀ d₁ h ?_
      cases hb : beval s b₁ <;> simp only [beval, hb] at e ⊢ <;> simpa using e
  | and b₁ b₂ ih₁ ih₂ =>
      intro d₁ d₀ pc pc' stk h e
      simp only [compileBexp] at h e
      cases hb₁ : beval s b₁
      · -- `b₁` is false: skip over the code for `b₂`, then take `b`'s false branch
        refine ih₁ 0 (codelen (compileBexp b₂ d₁ d₀) + d₀) h.app_left ?_
        simp only [beval, hb₁, Bool.false_and, Bool.false_eq_true, if_false,
          codelen_app] at e ⊢
        omega
      · -- `b₁` is true: fall through into the code for `b₂`
        refine (ih₁ 0 (codelen (compileBexp b₂ d₁ d₀) + d₀) h.app_left
          (pc' := pc + codelen (compileBexp b₁ 0 (codelen (compileBexp b₂ d₁ d₀) + d₀)))
          (by simp [hb₁])).trans ?_
        refine ih₂ d₁ d₀ (h.app_right' rfl) ?_
        cases hb₂ : beval s b₂ <;>
          simp only [beval, hb₁, hb₂, Bool.true_and, Bool.false_eq_true, if_true, if_false,
            codelen_app] at e ⊢ <;> omega

/-- If the source command terminates, then the compiled code runs from the
start of the generated code to its end, updating the store the same way. -/
theorem compileCom_correct_terminating {C : Code} {s c s'} (h : cexec s c s') :
    ∀ {pc pc' : Int} {stk : Stack}, CodeAt C pc (compileCom c) →
    pc' = pc + codelen (compileCom c) →
    transitions C (pc, stk, s) (pc', stk, s') := by
  induction h with
  | skip s =>
      intro pc pc' stk _ e
      simp only [compileCom, codelen_nil] at e
      have : pc' = pc := by omega
      subst this; exact .refl _
  | assign s x a =>
      intro pc pc' stk h e
      simp only [compileCom] at h e
      have h₂ : instrAt C (pc + codelen (compileAexp a)) = some (.setvar x) :=
        (h.app_right' rfl).head
      refine (compileAexp_correct a h.app_left rfl).trans (.one (.setvar' h₂ rfl ?_))
      simp only [codelen_app, codelen_cons, codelen_nil] at e; omega
  | @seq c₁ c₂ s s' s'' _ _ ih₁ ih₂ =>
      intro pc pc' stk h e
      simp only [compileCom] at h e
      exact (ih₁ h.app_left rfl).trans
        (ih₂ (h.app_right' rfl) (by simp only [codelen_app] at e; omega))
  | @ifthenelse b c₁ c₂ s s' _ ih =>
      intro pc pc' stk h e
      simp only [compileCom] at h e
      cases hbv : beval s b
      · -- the "else" branch is taken: jump over the code for `c₁`
        simp only [hbv, Bool.false_eq_true, if_false] at ih
        have hcode₂ : CodeAt C (pc + codelen (compileBexp b 0 (codelen (compileCom c₁) + 1))
            + codelen (compileCom c₁) + 1) (compileCom c₂) :=
          (h.app_right' (by simp only [codelen_app]; omega)).tail' rfl
        refine (compileBexp_correct b 0 (codelen (compileCom c₁) + 1)
          h.app_left.app_left
          (by simp only [hbv, Bool.false_eq_true, if_false]; omega)).trans (ih hcode₂ ?_)
        simp only [codelen_app, codelen_cons] at e; omega
      · -- the "then" branch is taken, then jump over the code for `c₂`
        simp only [hbv, if_true] at ih
        have hcode₁ : CodeAt C (pc + codelen (compileBexp b 0 (codelen (compileCom c₁) + 1)))
            (compileCom c₁) := h.app_left.app_right' rfl
        have hbranch : instrAt C (pc + codelen (compileBexp b 0 (codelen (compileCom c₁) + 1))
            + codelen (compileCom c₁)) = some (.branch (codelen (compileCom c₂))) :=
          (h.app_right' (by simp only [codelen_app]; omega)).head
        refine (compileBexp_correct b 0 (codelen (compileCom c₁) + 1)
          h.app_left.app_left (by simp [hbv])).trans
          ((ih hcode₁ rfl).trans (.one (.branch hbranch ?_)))
        simp only [codelen_app, codelen_cons] at e; omega
  | @while_done b c s hb =>
      intro pc pc' stk h e
      simp only [compileCom] at h e
      refine compileBexp_correct b 0 (codelen (compileCom c) + 1) h.app_left.app_left ?_
      simp only [hb, Bool.false_eq_true, if_false, codelen_app, codelen_cons,
        codelen_nil] at e ⊢
      omega
  | @while_loop b c s s' s'' hb _ _ ih₁ ih₂ =>
      intro pc pc' stk h e
      have hfull := h
      simp only [compileCom] at h
      have hcodeBody : CodeAt C (pc + codelen (compileBexp b 0 (codelen (compileCom c) + 1)))
          (compileCom c) := h.app_left.app_right' rfl
      have hbranch : instrAt C (pc + codelen (compileBexp b 0 (codelen (compileCom c) + 1))
          + codelen (compileCom c))
          = some (.branch (-(codelen (compileBexp b 0 (codelen (compileCom c) + 1))
              + codelen (compileCom c) + 1))) :=
        (h.app_right' (by simp only [codelen_app]; omega)).head
      exact (compileBexp_correct b 0 (codelen (compileCom c) + 1)
        h.app_left.app_left (by simp [hb])).trans
        ((ih₁ hcodeBody rfl).trans
          (.step (.branch hbranch (pc' := pc) (by omega)) (ih₂ hfull e)))

/-- Semantic preservation for terminating programs: if the source terminates
in `s'`, the compiled program halts in `s'`. -/
theorem compileProgram_correct_terminating {s c s'} (h : cexec s c s') :
    machineTerminates (compileProgram c) s s' := by
  have hcode : CodeAt (compileProgram c) 0 (compileCom c ++ [instr.halt]) :=
    ⟨[], [], by simp [compileProgram], by simp⟩
  exact ⟨0 + codelen (compileCom c),
    compileCom_correct_terminating h hcode.app_left rfl,
    (hcode.app_right' rfl).head⟩


/-! ## Full correctness: a simulation argument

The theorem above says nothing about source programs that loop forever.  To
cover those we abandon the big-step semantics and switch to the continuation
semantics of IMP, then prove a *simulation diagram*: every source step is
matched by zero, one or several machine transitions.  Divergence then
transfers from source to target, because an infinite sequence of source steps
produces an infinite sequence of machine transitions.

First we must say what it means for a machine configuration to *match* a
source configuration `(c, k, s)`.  Relating `c` to the code is what `CodeAt`
already does.  What is new is relating the continuation `k` to the code: when
the machine finishes the code for `c`, the instructions it meets next should
carry out the pending computations recorded in `k` and then halt. -/

/-- `compileCont C k pc`: starting at `pc`, the code `C` performs the pending
computations described by `k` and then reaches a `halt`. -/
inductive compileCont (C : Code) : cont → Int → Prop where
  | stop {pc} : instrAt C pc = some .halt → compileCont C .stop pc
  | seq {c k pc pc'} :
      CodeAt C pc (compileCom c) → pc' = pc + codelen (compileCom c) →
      compileCont C k pc' → compileCont C (.seq c k) pc
  | «while» {b c k pc d pc' pc''} :
      instrAt C pc = some (.branch d) → pc' = pc + 1 + d →
      CodeAt C pc' (compileCom (.while b c)) →
      pc'' = pc' + codelen (compileCom (.while b c)) →
      compileCont C k pc'' → compileCont C (.while b c k) pc
  /-- A continuation may also be reached through a chain of branches. -/
  | branch {d k pc pc'} :
      instrAt C pc = some (.branch d) → pc' = pc + 1 + d →
      compileCont C k pc' → compileCont C k pc

theorem compileCont_pc {C : Code} {k : cont} {pc pc' : Int}
    (h : compileCont C k pc) (e : pc' = pc) : compileCont C k pc' := by subst e; exact h

/-- A source configuration `(c, k, s)` matches a machine configuration when
the stores agree, the machine stack is empty, the code at `pc` is the code for
`c`, and the code after it carries out `k`. -/
inductive matchConfig (C : Code) : com × cont × Store → Config → Prop where
  | intro {c k st pc} :
      CodeAt C pc (compileCom c) →
      compileCont C k (pc + codelen (compileCom c)) →
      matchConfig C (c, k, st) (pc, [], st)

/-! ### The anti-stuttering measure

Some source steps — entering a sequence, testing a loop — correspond to *no*
machine transition at all.  A simulation with such stuttering steps does not
by itself transfer divergence: the machine could stutter forever while the
source makes progress.  We rule that out with a measure on source
configurations that strictly decreases at every stuttering step.  Finding one
is a small black art; the sum of the sizes of the command in focus and of the
commands recorded in the continuation works. -/

def comSize : com → Nat
  | .skip => 1
  | .assign _ _ => 1
  | .seq c₁ c₂ => comSize c₁ + comSize c₂ + 1
  | .ifthenelse _ c₁ c₂ => comSize c₁ + comSize c₂ + 1
  | .while _ c₁ => comSize c₁ + 1

theorem comSize_pos (c : com) : 0 < comSize c := by
  cases c <;> simp [comSize] <;> omega

def contSize : cont → Nat
  | .stop => 0
  | .seq c k => comSize c + contSize k
  | .while _ _ k => contSize k

def measure : com × cont × Store → Nat
  | (c, k, _) => comSize c + contSize k

/-! ### Inverting `compileCont`

Because of the `branch` rule, a continuation may sit behind a chain of
unconditional jumps.  These three lemmas run down such a chain and expose the
instruction the continuation really starts with. -/

theorem compileCont_codeAt_nil {C : Code} {k : cont} {pc : Int}
    (h : compileCont C k pc) : CodeAt C pc [] := by
  cases h with
  | stop hh => exact instrAt_codeAt_nil hh
  | seq hc _ _ => exact hc.nil
  | «while» hb _ _ _ _ => exact instrAt_codeAt_nil hb
  | branch hb _ _ => exact instrAt_codeAt_nil hb

theorem matchConfig_skip {C : Code} {k : cont} {s : Store} {pc : Int}
    (h : compileCont C k pc) : matchConfig C (.skip, k, s) (pc, [], s) :=
  .intro (compileCont_codeAt_nil h) (compileCont_pc h (by simp [compileCom]))

theorem compileCont_stop_inv {C : Code} {k : cont} {pc : Int} {s : Store}
    (h : compileCont C k pc) (hk : k = .stop) :
    ∃ pc', transitions C (pc, [], s) (pc', [], s) ∧ instrAt C pc' = some .halt := by
  induction h with
  | stop hh => exact ⟨_, .refl _, hh⟩
  | seq _ _ _ => cases hk
  | «while» _ _ _ _ _ => cases hk
  | branch hb he _ ih =>
      obtain ⟨pc'', hstar, hhalt⟩ := ih hk
      exact ⟨pc'', .step (.branch hb he) hstar, hhalt⟩

theorem compileCont_seq_inv {C : Code} {k : cont} {pc : Int} {s : Store} {c : com} {k' : cont}
    (h : compileCont C k pc) (hk : k = .seq c k') :
    ∃ pc', transitions C (pc, [], s) (pc', [], s) ∧ CodeAt C pc' (compileCom c)
      ∧ compileCont C k' (pc' + codelen (compileCom c)) := by
  induction h with
  | stop _ => cases hk
  | seq hc he hcont =>
      cases hk
      exact ⟨_, .refl _, hc, compileCont_pc hcont he.symm⟩
  | «while» _ _ _ _ _ => cases hk
  | branch hb he _ ih =>
      obtain ⟨pc'', hstar, hrest⟩ := ih hk
      exact ⟨pc'', .step (.branch hb he) hstar, hrest⟩

theorem compileCont_while_inv {C : Code} {k : cont} {pc : Int} {s : Store}
    {b : bexp} {c : com} {k' : cont}
    (h : compileCont C k pc) (hk : k = .while b c k') :
    ∃ pc', Plus (transition C) (pc, [], s) (pc', [], s)
      ∧ CodeAt C pc' (compileCom (.while b c))
      ∧ compileCont C k' (pc' + codelen (compileCom (.while b c))) := by
  induction h with
  | stop _ => cases hk
  | seq _ _ _ => cases hk
  | «while» hb he hc he' hcont =>
      cases hk
      exact ⟨_, .one (.branch hb he), hc, compileCont_pc hcont he'.symm⟩
  | branch hb he _ ih =>
      obtain ⟨pc'', hplus, hrest⟩ := ih hk
      exact ⟨pc'', .left (.branch hb he) hplus.star, hrest⟩

/-! ### The simulation diagram

Each source step is matched either by at least one machine transition, or by
zero or more machine transitions together with a strict decrease of the
measure.  The second alternative is what allows source steps that generate no
code. -/

-- The `simp only` calls below list lemmas that are needed on some branches
-- of the case analysis but not others; the unused-argument linter is off here.
set_option linter.unusedSimpArgs false in
theorem simulation_step {C : Code} {ic₁ ic₂ : com × cont × Store} {mc₁ : Config}
    (hstep : step ic₁ ic₂) (hmatch : matchConfig C ic₁ mc₁) :
    ∃ mc₂, (Plus (transition C) mc₁ mc₂
            ∨ (transitions C mc₁ mc₂ ∧ measure ic₂ < measure ic₁))
      ∧ matchConfig C ic₂ mc₂ := by
  cases hstep with
  | assign x a k s =>
      cases hmatch with
      | intro hcode hcont =>
          rename_i pc
          simp only [compileCom] at hcode hcont
          refine ⟨_, .inl (Plus.right (compileAexp_correct a hcode.app_left rfl)
            (.setvar' (h := (hcode.app_right' rfl).head) rfl (pc' := pc + codelen (compileCom
              (com.assign x a))) ?_)), matchConfig_skip hcont⟩
          simp only [compileCom, codelen_app, codelen_cons, codelen_nil]; omega
  | seq c₁ c₂ s k =>
      cases hmatch with
      | intro hcode hcont =>
          simp only [compileCom] at hcode hcont
          refine ⟨_, .inr ⟨.refl _, ?_⟩,
            .intro hcode.app_left (.seq (hcode.app_right' rfl) rfl
              (compileCont_pc hcont (by simp only [codelen_app]; omega)))⟩
          simp only [measure, comSize, contSize]; omega
  | ifthenelse b c₁ c₂ k s =>
      cases hmatch with
      | intro hcode hcont =>
          rename_i pc
          simp only [compileCom] at hcode hcont
          cases hbv : beval s b
          · -- the "else" branch: the test jumps over the code for `c₁`
            refine ⟨_, .inr ⟨compileBexp_correct b 0 (codelen (compileCom c₁) + 1)
              hcode.app_left.app_left
              (pc' := pc + codelen (compileBexp b 0 (codelen (compileCom c₁) + 1))
                + codelen (compileCom c₁) + 1)
              (by simp only [hbv, Bool.false_eq_true, if_false]; omega), ?_⟩, ?_⟩
            · simp only [measure, comSize, contSize, hbv, Bool.false_eq_true, if_false]
              have := comSize_pos c₁; omega
            · simp only [hbv, Bool.false_eq_true, if_false]
              exact .intro ((hcode.app_right' (by simp only [codelen_app]; omega)).tail' rfl)
                (compileCont_pc hcont (by simp only [codelen_app, codelen_cons]; omega))
          · -- the "then" branch: fall through into the code for `c₁`
            refine ⟨_, .inr ⟨compileBexp_correct b 0 (codelen (compileCom c₁) + 1)
              hcode.app_left.app_left
              (pc' := pc + codelen (compileBexp b 0 (codelen (compileCom c₁) + 1)))
              (by simp [hbv]), ?_⟩, ?_⟩
            · simp only [measure, comSize, contSize, hbv, if_true]
              have := comSize_pos c₂; omega
            · simp only [hbv, if_true]
              refine .intro (hcode.app_left.app_right' rfl) ?_
              -- the code for `c₁` is followed by a jump over the code for `c₂`
              exact .branch (d := codelen (compileCom c₂))
                (hcode.app_right' (by simp only [codelen_app]; omega)).head rfl
                (compileCont_pc hcont (by simp only [codelen_app, codelen_cons]; omega))
  | @while_done b c k s hb =>
      cases hmatch with
      | intro hcode hcont =>
          rename_i pc
          simp only [compileCom] at hcode hcont
          refine ⟨_, .inr ⟨compileBexp_correct b 0 (codelen (compileCom c) + 1)
            hcode.app_left.app_left
            (pc' := pc + codelen (compileCom (com.while b c)))
            (by simp only [hb, Bool.false_eq_true, if_false, compileCom, codelen_app,
              codelen_cons, codelen_nil]; omega), ?_⟩,
            matchConfig_skip hcont⟩
          simp only [measure, comSize, contSize]
          have := comSize_pos c; omega
  | @while_true b c k s hb =>
      cases hmatch with
      | intro hcode hcont =>
          rename_i pc
          have hfull := hcode
          simp only [compileCom] at hcode hcont
          refine ⟨_, .inr ⟨compileBexp_correct b 0 (codelen (compileCom c) + 1)
            hcode.app_left.app_left
            (pc' := pc + codelen (compileBexp b 0 (codelen (compileCom c) + 1)))
            (by simp [hb]), ?_⟩, ?_⟩
          · simp only [measure, comSize, contSize]; omega
          · refine .intro (hcode.app_left.app_right' rfl) ?_
            -- after the loop body comes the jump back to the top of the loop
            exact .«while» (d := -(codelen (compileBexp b 0 (codelen (compileCom c) + 1))
                + codelen (compileCom c) + 1))
              (hcode.app_right' (by simp only [codelen_app]; omega)).head (by omega)
              hfull rfl hcont
  | skip_seq c k s =>
      cases hmatch with
      | intro hcode hcont =>
          rename_i pc
          obtain ⟨pc', hstar, hcode', hcont'⟩ :=
            compileCont_seq_inv (s := s) hcont rfl
          refine ⟨_, .inr ⟨?_, ?_⟩, .intro hcode' hcont'⟩
          · simpa [compileCom] using hstar
          · simp only [measure, comSize, contSize]
            have := comSize_pos c; omega
  | skip_while b c k s =>
      cases hmatch with
      | intro hcode hcont =>
          obtain ⟨pc', hplus, hcode', hcont'⟩ :=
            compileCont_while_inv (s := s) hcont rfl
          exact ⟨_, .inl (by simpa [compileCom] using hplus), .intro hcode' hcont'⟩

/-- Lifting the simulation from one step to a finite sequence of steps. -/
theorem simulation_steps {C : Code} {ic₁ ic₂ : com × cont × Store}
    (h : Star step ic₁ ic₂) : ∀ {mc₁ : Config}, matchConfig C ic₁ mc₁ →
    ∃ mc₂, transitions C mc₁ mc₂ ∧ matchConfig C ic₂ mc₂ := by
  induction h with
  | refl a => exact fun hm => ⟨_, .refl _, hm⟩
  | step hstep _ ih =>
      intro mc₁ hm
      obtain ⟨mc₂, hsteps, hm₂⟩ := simulation_step hstep hm
      obtain ⟨mc₃, hsteps₃, hm₃⟩ := ih hm₂
      refine ⟨mc₃, ?_, hm₃⟩
      rcases hsteps with hplus | ⟨hstar, _⟩
      · exact hplus.star.trans hsteps₃
      · exact hstar.trans hsteps₃

theorem matchInitialConfigs (c : com) (s : Store) :
    matchConfig (compileProgram c) (c, .stop, s) (0, [], s) := by
  have hcode : CodeAt (compileProgram c) 0 (compileCom c ++ [instr.halt]) :=
    ⟨[], [], by simp [compileProgram], by simp⟩
  exact .intro hcode.app_left (.stop (hcode.app_right' rfl).head)

/-- The terminating case again, this time from the continuation semantics. -/
theorem compileProgram_correct_terminating_2 {c : com} {s s' : Store}
    (h : Star step (c, .stop, s) (.skip, .stop, s')) :
    machineTerminates (compileProgram c) s s' := by
  obtain ⟨mc, hsteps, hm⟩ := simulation_steps h (matchInitialConfigs c s)
  cases hm with
  | intro hcode hcont =>
      obtain ⟨pc', hstar, hhalt⟩ := compileCont_stop_inv (s := s') hcont rfl
      exact ⟨pc', hsteps.trans (by simpa [compileCom] using hstar), hhalt⟩

/-- The key step for divergence: from a diverging source configuration, the
machine can always make *at least one* transition and land in a configuration
that again matches a diverging source configuration.  The bound `n` on the
measure is what makes this an ordinary induction: consecutive stuttering
steps must run out. -/
theorem simulation_infseq_inv {C : Code} :
    ∀ (n : Nat) {ic₁ : com × cont × Store} {mc₁ : Config},
    Infseq step ic₁ → matchConfig C ic₁ mc₁ → measure ic₁ < n →
    ∃ ic₂ mc₂, Infseq step ic₂ ∧ Plus (transition C) mc₁ mc₂ ∧ matchConfig C ic₂ mc₂ := by
  intro n
  induction n with
  | zero => intro ic₁ mc₁ _ _ hm; omega
  | succ n ih =>
      intro ic₁ mc₁ hinf hmatch hmeas
      obtain ⟨ic', hstep, hinf'⟩ := hinf.inv
      obtain ⟨mc₂, hcase, hmatch₂⟩ := simulation_step hstep hmatch
      rcases hcase with hplus | ⟨hstar, hless⟩
      · exact ⟨ic', mc₂, hinf', hplus, hmatch₂⟩
      · obtain ⟨ic₃, mc₃, hinf₃, hplus₃, hmatch₃⟩ := ih hinf' hmatch₂ (by omega)
        exact ⟨ic₃, mc₃, hinf₃, hstar.plusTrans hplus₃, hmatch₃⟩

/-- Semantic preservation for diverging programs: if the source makes
infinitely many steps, so does the compiled code. -/
theorem compileProgram_correct_diverging {c : com} {s : Store}
    (h : Infseq step (c, .stop, s)) : machineDiverges (compileProgram c) s := by
  refine Infseq.coinduction_plus
    (X := fun mc => ∃ ic, Infseq step ic ∧ matchConfig (compileProgram c) ic mc) ?_
    ⟨(c, .stop, s), h, matchInitialConfigs c s⟩
  rintro mc ⟨ic, hinf, hmatch⟩
  obtain ⟨ic₂, mc₂, hinf₂, hplus, hmatch₂⟩ :=
    simulation_infseq_inv (measure ic + 1) hinf hmatch (by omega)
  exact ⟨mc₂, hplus, ic₂, hinf₂, hmatch₂⟩

end Compil
