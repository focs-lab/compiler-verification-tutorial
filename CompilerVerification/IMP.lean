/-
  The source language IMP: syntax and semantics.

  Lean 4 port of `IMP.v` from the Coq development accompanying
  Xavier Leroy, *Proving the correctness of a compiler*,
  EUTypes 2019 Summer School.

  Original Coq sources: Copyright 2019, 2025 Xavier Leroy.
  This file is a modified work: the definitions and theorem statements follow
  the Coq originals, but all proofs and explanatory text have been rewritten
  for Lean 4.

  Distributed under the GNU Lesser General Public License, version 2.1
  or (at your option) any later version.  See LICENSE.md.
-/
import CompilerVerification.Sequences

/-!
# IMP: a small imperative language

IMP has integer variables, arithmetic and Boolean expressions, assignment,
sequencing, conditionals and `while` loops.  It is Turing-complete: the loops
are unbounded and the integers are unbounded.

We give it three semantics and relate them:

* a **denotational** semantics for expressions — evaluation *functions*
  `aeval` and `beval`;
* a **big-step** (natural) semantics for commands — the relation `cexec`,
  which describes only terminating executions;
* two **small-step** semantics for commands — the reduction relation `red`,
  and the continuation-based relation `step`.  Small-step semantics can
  describe diverging executions, which is exactly what we need in order to
  state that the compiler preserves the behaviour of programs that loop
  forever.
-/

namespace IMP

open Sequences

/-- Variables are named by strings. -/
abbrev Ident := String

/-! ## Arithmetic expressions -/

/-- Abstract syntax of arithmetic expressions. -/
inductive aexp where
  | const (n : Int)
  | var (x : Ident)
  | plus (a₁ a₂ : aexp)
  | minus (a₁ a₂ : aexp)
  deriving Repr, DecidableEq

/-- A store maps each variable to its current value. -/
def Store : Type := Ident → Int

/-- The value denoted by an arithmetic expression in a given store. -/
def aeval (s : Store) : aexp → Int
  | .const n => n
  | .var x => s x
  | .plus a₁ a₂ => aeval s a₁ + aeval s a₂
  | .minus a₁ a₂ => aeval s a₁ - aeval s a₂

/-- `update x v s` maps `x` to `v` and agrees with `s` elsewhere. -/
def update (x : Ident) (v : Int) (s : Store) : Store :=
  fun y => if y = x then v else s y

@[simp] theorem update_same (x : Ident) (v : Int) (s : Store) : update x v s x = v := by
  simp [update]

@[simp] theorem update_other {x y : Ident} (h : y ≠ x) (v : Int) (s : Store) :
    update x v s y = s y := by
  simp [update, h]

/-- An evaluation function can be *run*: `x + (x - 1)` in a store where every
variable holds `2`. -/
example : aeval (fun _ => 2) (.plus (.var "x") (.minus (.var "x") (.const 1))) = 3 := by
  native_decide

/-- We can also prove properties of a *given* expression, for every store. -/
theorem aeval_xplus1 (s : Store) (x : Ident) :
    aeval s (.plus (.var x) (.const 1)) > aeval s (.var x) := by
  simp [aeval]
  omega

/-- Which variables occur in an expression. -/
def freeInAexp (x : Ident) : aexp → Prop
  | .const _ => False
  | .var y => y = x
  | .plus a₁ a₂ | .minus a₁ a₂ => freeInAexp x a₁ ∨ freeInAexp x a₂

/-- And we can prove *meta*-properties, holding for all expressions at once:
the value of an expression depends only on its free variables. -/
theorem aeval_free {s₁ s₂ : Store} :
    ∀ a : aexp, (∀ x, freeInAexp x a → s₁ x = s₂ x) → aeval s₁ a = aeval s₂ a
  | .const _, _ => rfl
  | .var x, h => h x rfl
  | .plus a₁ a₂, h => by
      simp only [aeval, aeval_free a₁ fun x hx => h x (.inl hx),
        aeval_free a₂ fun x hx => h x (.inr hx)]
  | .minus a₁ a₂, h => by
      simp only [aeval, aeval_free a₁ fun x hx => h x (.inl hx),
        aeval_free a₂ fun x hx => h x (.inr hx)]

/-! ### Machine integers

The exercises ask for a version of `aeval` that detects overflow.  These are
the bounds of a 64-bit signed integer. -/

def minInt : Int := -(2 ^ 63)
def maxInt : Int := 2 ^ 63 - 1

def checkForOverflow (n : Int) : Option Int :=
  if n < minInt then none else if n > maxInt then none else some n

/-! ## Boolean expressions -/

/-- Abstract syntax of Boolean expressions. -/
inductive bexp where
  | true
  | false
  | equal (a₁ a₂ : aexp)
  | lessequal (a₁ a₂ : aexp)
  | not (b₁ : bexp)
  | and (b₁ b₂ : bexp)
  deriving Repr, DecidableEq

/-- The truth value denoted by a Boolean expression in a given store. -/
def beval (s : Store) : bexp → Bool
  | .true => Bool.true
  | .false => Bool.false
  | .equal a₁ a₂ => aeval s a₁ == aeval s a₂
  | .lessequal a₁ a₂ => decide (aeval s a₁ ≤ aeval s a₂)
  | .not b₁ => !beval s b₁
  | .and b₁ b₂ => beval s b₁ && beval s b₂

/-! ### Derived forms

The other comparisons and connectives need no new syntax; they are
abbreviations. -/

def bexp.notequal (a₁ a₂ : aexp) : bexp := .not (.equal a₁ a₂)
def bexp.greaterequal (a₁ a₂ : aexp) : bexp := .lessequal a₂ a₁
def bexp.greater (a₁ a₂ : aexp) : bexp := .not (.lessequal a₁ a₂)
def bexp.less (a₁ a₂ : aexp) : bexp := bexp.greater a₂ a₁
def bexp.or (b₁ b₂ : bexp) : bexp := .not (.and (.not b₁) (.not b₂))

/-- The derived `or` really does denote disjunction — de Morgan, mechanised. -/
theorem beval_or (s : Store) (b₁ b₂ : bexp) :
    beval s (bexp.or b₁ b₂) = (beval s b₁ || beval s b₂) := by
  simp [bexp.or, beval]

/-! ## Commands -/

/-- Abstract syntax of commands (statements). -/
inductive com where
  | skip
  | assign (x : Ident) (a : aexp)
  | seq (c₁ c₂ : com)
  | ifthenelse (b : bexp) (c₁ c₂ : com)
  | while (b : bexp) (c₁ : com)
  deriving Repr, DecidableEq

infixr:80 " ;; " => com.seq

/-- Euclidean division by repeated subtraction.  On exit `"q"` holds the
quotient of `"a"` by `"b"` and `"r"` holds the remainder:

    r := a; q := 0;
    while b <= r do r := r - b; q := q + 1 done
-/
def euclideanDivision : com :=
  .assign "r" (.var "a") ;;
  .assign "q" (.const 0) ;;
  .while (.lessequal (.var "b") (.var "r"))
    (.assign "r" (.minus (.var "r") (.var "b")) ;;
     .assign "q" (.plus (.var "q") (.const 1)))

/-! ## Big-step semantics

The obvious idea — an evaluation function `cexec : Store → com → Store` — is
not definable: every Lean function is total, but `while true do skip` does not
terminate.  Worse, no computable function can decide termination of an IMP
program.

The standard answer is to define a *relation* instead: `cexec s c s'` holds
exactly when running `c` from `s` terminates in `s'`.  A derivation of
`cexec s c s'` is a finite tree, and finiteness is precisely what rules out
non-terminating executions. -/

/-- `cexec s c s'`: started in store `s`, the command `c` terminates in store
`s'`. -/
inductive cexec : Store → com → Store → Prop where
  | skip (s : Store) : cexec s .skip s
  | assign (s : Store) (x : Ident) (a : aexp) :
      cexec s (.assign x a) (update x (aeval s a) s)
  | seq {c₁ c₂ : com} {s s' s'' : Store} :
      cexec s c₁ s' → cexec s' c₂ s'' → cexec s (c₁ ;; c₂) s''
  | ifthenelse {b : bexp} {c₁ c₂ : com} {s s' : Store} :
      cexec s (if beval s b then c₁ else c₂) s' → cexec s (.ifthenelse b c₁ c₂) s'
  | while_done {b : bexp} {c : com} {s : Store} :
      beval s b = false → cexec s (.while b c) s
  | while_loop {b : bexp} {c : com} {s s' s'' : Store} :
      beval s b = true → cexec s c s' → cexec s' (.while b c) s'' →
      cexec s (.while b c) s''

/-- Nothing diverging satisfies `cexec`: `while true do skip` has no final
store. -/
theorem cexec_infinite_loop (s : Store) :
    ¬ ∃ s', cexec s (.while .true .skip) s' := by
  have key : ∀ {s c s'}, cexec s c s' → c = .while .true .skip → False := by
    intro s c s' h
    induction h with
    | while_done hb => intro heq; cases heq; simp [beval] at hb
    | while_loop _ _ _ _ ih₂ => intro heq; exact ih₂ heq
    | _ => intro heq; cases heq
  rintro ⟨s', h⟩
  exact key h rfl

/-! ### An interpreter with a fuel supply

Our first idea was not entirely wrong.  Bounding the recursion depth by a
`fuel` argument does give a total function, which returns `none` when the fuel
runs out.  It is useless as a semantics — but it is exactly what we want for
*testing* programs. -/

/-- Run `c` from `s`, taking at most `fuel` recursive steps. -/
def cexecBounded : Nat → Store → com → Option Store
  | 0, _, _ => none
  | fuel + 1, s, c =>
    match c with
    | .skip => some s
    | .assign x a => some (update x (aeval s a) s)
    | .seq c₁ c₂ =>
        match cexecBounded fuel s c₁ with
        | none => none
        | some s' => cexecBounded fuel s' c₂
    | .ifthenelse b c₁ c₂ =>
        if beval s b then cexecBounded fuel s c₁ else cexecBounded fuel s c₂
    | .while b c₁ =>
        if beval s b then
          match cexecBounded fuel s c₁ with
          | none => none
          | some s' => cexecBounded fuel s' (.while b c₁)
        else some s

/-- 14 divided by 3 is 4, remainder 2. -/
example :
    (let s := update "a" 14 (update "b" 3 (fun _ => 0))
     (cexecBounded 100 s euclideanDivision).map (fun s' => (s' "q", s' "r")))
    = some (4, 2) := by
  native_decide

/-! ## Small-step semantics: reduction

A big-step semantics says nothing about diverging programs — they simply have
no derivation, and "no derivation" cannot distinguish an infinite loop from a
program that crashes.  A small-step semantics does distinguish them: it
describes one elementary computation step at a time, so a diverging program
is one with an infinite sequence of steps.

`red (c, s) (c', s')` performs one step of `c` in store `s`, leaving the
residual command `c'` still to be run in the updated store `s'`. -/

/-- One step of reduction. -/
inductive red : com × Store → com × Store → Prop where
  | assign (x : Ident) (a : aexp) (s : Store) :
      red (.assign x a, s) (.skip, update x (aeval s a) s)
  | seq_done (c : com) (s : Store) : red (.skip ;; c, s) (c, s)
  | seq_step {c₁ c₂ : com} {s₁ s₂ : Store} (c : com) :
      red (c₁, s₁) (c₂, s₂) → red (c₁ ;; c, s₁) (c₂ ;; c, s₂)
  | ifthenelse (b : bexp) (c₁ c₂ : com) (s : Store) :
      red (.ifthenelse b c₁ c₂, s) ((if beval s b then c₁ else c₂), s)
  | while_done {b : bexp} {c : com} {s : Store} :
      beval s b = false → red (.while b c, s) (.skip, s)
  | while_loop {b : bexp} {c : com} {s : Store} :
      beval s b = true → red (.while b c, s) (c ;; .while b c, s)

/-- IMP programs never get stuck: a command that is not `skip` can always
take a step. -/
theorem red_progress (c : com) (s : Store) :
    c = .skip ∨ ∃ c' s', red (c, s) (c', s') := by
  induction c with
  | skip => exact .inl rfl
  | assign x a => exact .inr ⟨_, _, .assign x a s⟩
  | seq c₁ c₂ ih₁ _ =>
      refine .inr ?_
      rcases ih₁ with rfl | ⟨c', s', h⟩
      · exact ⟨c₂, s, .seq_done c₂ s⟩
      · exact ⟨c' ;; c₂, s', .seq_step c₂ h⟩
  | ifthenelse b c₁ c₂ _ _ => exact .inr ⟨_, _, .ifthenelse b c₁ c₂ s⟩
  | «while» b c₁ _ =>
      refine .inr ?_
      cases hb : beval s b
      · exact ⟨.skip, s, .while_done hb⟩
      · exact ⟨c₁ ;; .while b c₁, s, .while_loop hb⟩

/-- A program "goes wrong" if it reaches an irreducible state other than
`skip`. -/
def goesWrong (c : com) (s : Store) : Prop :=
  ∃ c' s', Star red (c, s) (c', s') ∧ Irred red (c', s') ∧ c' ≠ .skip

theorem not_goesWrong (c : com) (s : Store) : ¬ goesWrong c s := by
  rintro ⟨c', s', _, hirred, hne⟩
  rcases red_progress c' s' with rfl | ⟨c'', s'', h⟩
  · exact hne rfl
  · exact hirred _ h

/-- Reduction under a sequence context, generalising `red.seq_step` from one
step to a sequence of steps. -/
theorem red_seq_steps (c₂ : com) {p q : com × Store} (h : Star red p q) :
    Star red (p.1 ;; c₂, p.2) (q.1 ;; c₂, q.2) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih =>
      rename_i x y _ _
      obtain ⟨cx, sx⟩ := x
      obtain ⟨cy, sy⟩ := y
      exact .step (.seq_step c₂ h) ih

/-! ### Big-step and small-step agree

Termination in the big-step sense coincides with reaching `skip` in the
small-step sense.  One direction is a routine induction on the big-step
derivation. -/

theorem cexec_to_reds {s c s'} (h : cexec s c s') : Star red (c, s) (.skip, s') := by
  induction h with
  | skip => exact .refl _
  | assign s x a => exact .one (.assign x a s)
  | seq _ _ ih₁ ih₂ =>
      exact (red_seq_steps _ ih₁).trans (.step (.seq_done _ _) ih₂)
  | ifthenelse _ ih => exact .step (.ifthenelse _ _ _ _) ih
  | while_done hb => exact .one (.while_done hb)
  | while_loop hb _ _ ih₁ ih₂ =>
      exact .step (.while_loop hb) ((red_seq_steps _ ih₁).trans (.step (.seq_done _ _) ih₂))

/-- The converse needs this key lemma: one reduction step followed by a
big-step execution collapses into a single big-step execution. -/
theorem red_append_cexec {p q : com × Store} (h : red p q) :
    ∀ {s'}, cexec q.2 q.1 s' → cexec p.2 p.1 s' := by
  induction h with
  | assign x a s => intro s' h; cases h; exact .assign s x a
  | seq_done c s => intro s' h; exact .seq (.skip s) h
  | seq_step c _ ih =>
      intro s' h
      cases h with
      | seq h₁ h₂ => exact .seq (ih h₁) h₂
  | ifthenelse b c₁ c₂ s => intro s' h; exact .ifthenelse h
  | while_done hb => intro s' h; cases h; exact .while_done hb
  | while_loop hb =>
      intro s' h
      cases h with
      | seq h₁ h₂ => exact .while_loop hb h₁ h₂

theorem reds_to_cexec {s c s'} (h : Star red (c, s) (.skip, s')) : cexec s c s' := by
  generalize hp : (c, s) = p at h
  generalize hq : ((.skip : com), s') = q at h
  induction h generalizing c s with
  | refl a => cases hp; cases hq; exact .skip _
  | step h _ ih =>
      rename_i x y _ _
      obtain ⟨cy, sy⟩ := y
      cases hp
      exact red_append_cexec h (ih rfl hq)

/-! ## Small-step semantics with continuations

The reduction relation rebuilds a whole command at every step, which makes it
awkward to relate to a machine that just moves a program counter.  The
continuation semantics separates the two halves of a configuration:

* the **sub-command under focus**, where computation happens;
* the **continuation**, describing what remains to be done once the
  sub-command finishes.

This is much closer to the machine, and it extends painlessly to other control
structures — see the exercises on `break` and `continue`. -/

/-- What remains to be executed after the command under focus terminates. -/
inductive cont where
  /-- Nothing remains; execution stops. -/
  | stop
  /-- Run `c`, then continue with `k`. -/
  | seq (c : com) (k : cont)
  /-- Re-enter the loop `while b do c`, then continue with `k`. -/
  | while (b : bexp) (c : com) (k : cont)
  deriving Repr, DecidableEq

/-- Rebuilding the whole command from a focus and a continuation: `c` is
placed leftmost in the nest of sequences described by `k`. -/
def applyCont : cont → com → com
  | .stop, c => c
  | .seq c₁ k₁, c => applyCont k₁ (c ;; c₁)
  | .while b₁ c₁ k₁, c => applyCont k₁ (c ;; .while b₁ c₁)

/-- Transitions between triples (focus, continuation, store).  The rules split
into three kinds: *computation* (evaluate an expression and act on the
result), *focusing* (descend into a sub-command, pushing onto the
continuation), and *resumption* (the focus is `skip`, so pop the
continuation). -/
inductive step : com × cont × Store → com × cont × Store → Prop where
  /-- computation -/
  | assign (x : Ident) (a : aexp) (k : cont) (s : Store) :
      step (.assign x a, k, s) (.skip, k, update x (aeval s a) s)
  /-- focusing -/
  | seq (c₁ c₂ : com) (s : Store) (k : cont) :
      step (c₁ ;; c₂, k, s) (c₁, .seq c₂ k, s)
  /-- computation -/
  | ifthenelse (b : bexp) (c₁ c₂ : com) (k : cont) (s : Store) :
      step (.ifthenelse b c₁ c₂, k, s) ((if beval s b then c₁ else c₂), k, s)
  /-- computation -/
  | while_done {b : bexp} {c : com} {k : cont} {s : Store} :
      beval s b = false → step (.while b c, k, s) (.skip, k, s)
  /-- computation and focusing -/
  | while_true {b : bexp} {c : com} {k : cont} {s : Store} :
      beval s b = true → step (.while b c, k, s) (c, .while b c k, s)
  /-- resumption -/
  | skip_seq (c : com) (k : cont) (s : Store) :
      step (.skip, .seq c k, s) (c, k, s)
  /-- resumption -/
  | skip_while (b : bexp) (c : com) (k : cont) (s : Store) :
      step (.skip, .while b c k, s) (.while b c, k, s)

/-- A big-step execution gives rise to a sequence of continuation steps that
leaves the continuation untouched. -/
theorem cexec_to_steps {s c s'} (h : cexec s c s') (k : cont) :
    Star step (c, k, s) (.skip, k, s') := by
  induction h generalizing k with
  | skip => exact .refl _
  | assign s x a => exact .one (.assign x a k s)
  | seq _ _ ih₁ ih₂ =>
      exact .step (.seq _ _ _ _) ((ih₁ _).trans (.step (.skip_seq _ _ _) (ih₂ _)))
  | ifthenelse _ ih => exact .step (.ifthenelse _ _ _ _ _) (ih _)
  | while_done hb => exact .one (.while_done hb)
  | while_loop hb _ _ ih₁ ih₂ =>
      exact .step (.while_true hb)
        ((ih₁ _).trans (.step (.skip_while _ _ _ _) (ih₂ _)))

end IMP
