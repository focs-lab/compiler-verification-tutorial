/-
  Exercises accompanying the Lean 4 port of Xavier Leroy's
  *Proving the correctness of a compiler* (EUTypes 2019 Summer School).

  The exercises are those of the original Coq development.
  Original Coq sources: Copyright 2019, 2025 Xavier Leroy.
  This file is a modified work: the exercise statements have been restated
  for Lean 4.

  Distributed under the GNU Lesser General Public License, version 2.1
  or (at your option) any later version.  See LICENSE.md.

  Every `sorry` below is a hole for you to fill.  Building this file therefore
  reports "declaration uses 'sorry'" for each unsolved exercise — that is
  expected, and is how you track your progress.  The main library
  (`CompilerVerification`) builds with no warnings and contains no `sorry`.
-/
import CompilerVerification

/-!
# Exercises

Difficulty is marked in stars, following the original.  Exercises marked
*(recommended)* are the ones to do first.
-/

namespace Exercises

open IMP Compil Constprop Deadcode Sequences

/-! ## IMP

### Exercise (1 star, recommended)

Add multiplication to arithmetic expressions: extend `IMP.aexp` with a
constructor `times`, and extend `IMP.aeval` accordingly.  You will also need
to extend `freeInAexp`, and re-check `aeval_free`.

### Exercise (2 stars, recommended)

Add division, and detect arithmetic overflow.  Evaluation can now fail — by
division by zero, or by producing a result outside `[minInt, maxInt]` — so
either change `aeval` to return `Option Int`, using `IMP.checkForOverflow`, or
define the semantics relationally:

```
inductive aevalRel : Store → aexp → Int → Prop
```

Which of the two is easier to prove the compiler correct against?

### Exercise (3 stars, optional)

Relate the fuel-bounded interpreter to the big-step semantics. -/

theorem cexecBounded_sound : ∀ (fuel : Nat) (s : Store) (c : com) (s' : Store),
    cexecBounded fuel s c = some s' → cexec s c s' := by
  sorry

theorem cexecBounded_complete {s : Store} {c : com} {s' : Store} (h : cexec s c s') :
    ∃ fuel₁, ∀ fuel, fuel ≥ fuel₁ → cexecBounded fuel s c = some s' := by
  sorry

/-! ### Exercise (2 stars, recommended)

Extend the continuation semantics with C's `continue` statement, which ends
the current iteration of the enclosing loop and starts the next one.  Assume
`com` gains a constructor `continue`.  `break` needs just two resumption
rules:

```
| break_seq   : step (.break, .seq c k, s)       (.break, k, s)
| break_while : step (.break, .while b c k, s)   (.skip, k, s)
```

Write the analogous rules for `continue`, and explain in a sentence why no
other rule has to change.

### Exercise (3 stars, optional)

In Java, loops and `break`/`continue` may carry a label: `break lbl` exits the
nearest enclosing loop labelled `lbl`.  Give the transition rules for
`break lbl` and `continue lbl`.

### Exercise (3 stars, optional)

The converse of `IMP.cexec_to_steps`.  You will need a notion of big-step
execution *of a continuation*, and a lemma in the style of
`IMP.red_append_cexec`. -/

theorem steps_to_cexec {c : com} {s s' : Store}
    (h : Star step (c, .stop, s) (.skip, .stop, s')) : cexec s c s' := by
  sorry

/-! ## The compiler

### Exercise (2 stars, recommended)

`Compil.compileProgram` of `if x = 1 then x := 0 else skip` ends the "then"
branch with `branch 0`, which does nothing.  Rewrite `compileCom` to use
`Compil.smartBranch` instead of `instr.branch`, then adapt the statement and
proof of `compileCom_correct_terminating`.  Prove this lemma first — it is the
only place where the difference shows. -/

theorem transitions_smartBranch {C : Code} {pc pc' d : Int} {stk : Stack} {s : Store}
    (h : CodeAt C pc (smartBranch d)) (e : pc' = pc + 1 + d) :
    transitions C (pc, stk, s) (pc', stk, s) := by
  sorry

/-! ### Exercise (4 stars, optional)

The compiled code for a loop executes two branches per iteration: the
conditional branch that tests `b`, and the unconditional branch back to the
top.  One of them can be removed by putting the body *before* the test,

```
compileCom c ++ compileBexp b delta₁ 0
```

with `delta₁` branching back to the start of `compileCom c`.  On its own this
compiles a `while` loop as a `do…while` loop, which is wrong; the fix is to
jump over the body on entry:

```
instr.branch (codelen (compileCom c)) :: compileCom c ++ compileBexp b delta₁ 0
```

Modify `compileCom` accordingly and prove it correct.  The difficulty — and
the four stars — is that `CodeAt C pc (compileCom c)` no longer holds on the
second iteration of a loop, so you need a more flexible way of relating a
command to the program counter.

## Constant propagation

### Exercise (2 stars, recommended)

Write a bottom-up simplifier for Boolean expressions using the smart
constructors, and prove it sound. -/

def simplifBexp : bexp → bexp :=
  sorry

theorem simplifBexp_sound (s : Store) (b : bexp) : beval s (simplifBexp b) = beval s b := by
  sorry

/-! ### Exercise (2–3 stars, optional)

What other algebraic simplifications would be worth doing — meaning: after
which ones does `compileCom` emit strictly shorter code?  Add them to the
smart constructors and update their soundness proofs.

### Exercise (3 stars, optional)

Exploit equality tests.  In

```
if x = 0 then y := x + 1 else y := 1
```

both branches end with `y = 1`, but the analysis of `Constprop.lean` does not
see it.  Write

```
def Binvert (S : AStore) (b : bexp) : AStore × AStore
```

returning `(S₁, S₀)`, where `S₁` is `S` enriched with the equalities implied
by `b` being true and `S₀` with those implied by `b` being false.  Then use it
to sharpen the `ifthenelse` and `while` cases of `Constprop.Cexec`.

### Exercise (4 stars, optional)

Replace constant propagation by *interval* analysis: an abstract store maps
each variable to a pair `(lo, hi)` meaning `lo ≤ s x ≤ hi`, so that

```
def Matches (s : Store) (S : AStore) : Prop :=
  ∀ x lo hi, S.find x = some (lo, hi) → lo ≤ s x ∧ s x ≤ hi
```

(optionally with infinities for `lo` and `hi`).  Adapt the lattice
operations, the abstract interpreters for expressions, and `Cexec`.

## Dead code elimination

### Exercise (3 stars, optional)

`Deadcode.dce_correct_terminating` covers only terminating programs.  Prove
semantic preservation for diverging ones too, by completing the simulation
below against the small-step semantics `IMP.red`.  As in `Compil.lean`, some
source steps correspond to no step of the optimised program, so the diagram
needs an anti-stuttering measure. -/

def dceMeasure : com → Nat
  | .assign _ _ => 1
  | .seq c₁ _ => dceMeasure c₁
  | _ => 0

theorem dce_simulation {c : com} {s : Store} {c' : com} {s' : Store}
    (h : red (c, s) (c', s')) (L : IdentSet) (s₁ : Store) (ha : agree (live c L) s s₁) :
    (∃ s₁', red (dce c L, s₁) (dce c' L, s₁') ∧ agree (live c' L) s' s₁')
    ∨ (dceMeasure c' < dceMeasure c ∧ dce c L = dce c' L ∧ agree (live c' L) s' s₁) := by
  sorry

end Exercises
