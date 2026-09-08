/-
  Liveness analysis and dead code elimination.

  Lean 4 port of `Deadcode.v` from the Coq development accompanying
  Xavier Leroy, *Proving the correctness of a compiler*,
  EUTypes 2019 Summer School.

  Original Coq sources: Copyright 2019, 2025 Xavier Leroy.
  This file is a modified work: the definitions and theorem statements follow
  the Coq originals, but all proofs and explanatory text have been rewritten
  for Lean 4.  Coq's `FSets` library has no counterpart in Lean's core
  library, so sets of variables are implemented here as lists.

  Distributed under the GNU Lesser General Public License, version 2.1
  or (at your option) any later version.  See LICENSE.md.
-/
import CompilerVerification.IMP

/-!
# Liveness analysis and dead code elimination

A variable is *live* at a program point if some later instruction may read it
before it is overwritten.  An assignment to a variable that is not live is
dead: its value is never observed, so the assignment can be deleted.

Liveness is a *backward* dataflow analysis — `live c L` computes the variables
live before `c`, given the set `L` of variables live after it.  Contrast this
with constant propagation, which runs forwards.  Loops again require a
fixpoint, computed here with the same fuel-bounded iteration.

Sets of variables are represented as lists.  Duplicates are harmless: every
statement below is about membership, never about the representation.
-/

namespace Deadcode

open IMP

/-! ## Sets of variables -/

abbrev IdentSet := List Ident

namespace IdentSet

def remove (x : Ident) (L : IdentSet) : IdentSet := L.filter (fun y => !(y == x))

@[simp] theorem mem_remove {x y : Ident} {L : IdentSet} :
    x ∈ remove y L ↔ x ∈ L ∧ x ≠ y := by
  simp [remove, List.mem_filter]

/-- `Incl L₁ L₂`: every variable of `L₁` is a variable of `L₂`. -/
def Incl (L₁ L₂ : IdentSet) : Prop := ∀ x, x ∈ L₁ → x ∈ L₂

theorem Incl.refl (L : IdentSet) : Incl L L := fun _ h => h

theorem Incl.trans {L₁ L₂ L₃ : IdentSet} (h₁ : Incl L₁ L₂) (h₂ : Incl L₂ L₃) :
    Incl L₁ L₃ := fun x hx => h₂ x (h₁ x hx)

/-- A decidable inclusion test, used to detect that the fixpoint iteration has
stabilised. -/
def inclb (L₁ L₂ : IdentSet) : Bool := L₁.all (fun x => L₂.contains x)

theorem inclb_sound {L₁ L₂ : IdentSet} (h : inclb L₁ L₂ = true) : Incl L₁ L₂ := by
  intro x hx
  simp only [inclb, List.all_eq_true] at h
  simpa using h x hx

end IdentSet

open IdentSet

/-! ## Free variables -/

def fvAexp : aexp → IdentSet
  | .const _ => []
  | .var x => [x]
  | .plus a₁ a₂ => fvAexp a₁ ++ fvAexp a₂
  | .minus a₁ a₂ => fvAexp a₁ ++ fvAexp a₂

def fvBexp : bexp → IdentSet
  | .true => []
  | .false => []
  | .equal a₁ a₂ => fvAexp a₁ ++ fvAexp a₂
  | .lessequal a₁ a₂ => fvAexp a₁ ++ fvAexp a₂
  | .not b₁ => fvBexp b₁
  | .and b₁ b₂ => fvBexp b₁ ++ fvBexp b₂

def fvCom : com → IdentSet
  | .skip => []
  | .assign _ a => fvAexp a
  | .seq c₁ c₂ => fvCom c₁ ++ fvCom c₂
  | .ifthenelse b c₁ c₂ => fvBexp b ++ (fvCom c₁ ++ fvCom c₂)
  | .while b c => fvBexp b ++ fvCom c

/-! ## Fixpoints over sets of variables

The same engineer's fixpoint as in `Constprop.lean`: iterate at most twenty
times, and fall back on a `default` set — one that is certainly big enough —
if no fixpoint has appeared.  Falling back loses precision, never soundness. -/

def fixpointRec (F : IdentSet → IdentSet) (default : IdentSet) :
    Nat → IdentSet → IdentSet
  | 0, _ => default
  | fuel + 1, x => if inclb (F x) x then x else fixpointRec F default fuel (F x)

def fixpoint (F : IdentSet → IdentSet) (default : IdentSet) : IdentSet :=
  fixpointRec F default 20 []

/-- Either the result really is a post-fixpoint, or it is the fallback. -/
theorem fixpoint_charact (F : IdentSet → IdentSet) (default : IdentSet) :
    Incl (F (fixpoint F default)) (fixpoint F default) ∨ fixpoint F default = default := by
  have key : ∀ (n : Nat) (x : IdentSet),
      Incl (F (fixpointRec F default n x)) (fixpointRec F default n x)
      ∨ fixpointRec F default n x = default := by
    intro n
    induction n with
    | zero => intro x; exact .inr rfl
    | succ n ih =>
        intro x
        by_cases h : inclb (F x) x = true
        · simp only [fixpointRec, if_pos h]; exact .inl (inclb_sound h)
        · simp only [fixpointRec, if_neg h]; exact ih (F x)
  exact key 20 []

/-- If `default` is stable under `F`, the fixpoint stays inside it. -/
theorem fixpoint_upper_bound {F : IdentSet → IdentSet} {default : IdentSet}
    (hF : ∀ x, Incl x default → Incl (F x) default) :
    Incl (fixpoint F default) default := by
  have key : ∀ (n : Nat) (x : IdentSet), Incl x default →
      Incl (fixpointRec F default n x) default := by
    intro n
    induction n with
    | zero => intro x _; exact Incl.refl _
    | succ n ih =>
        intro x hx
        by_cases h : inclb (F x) x = true
        · simp only [fixpointRec, if_pos h]; exact hx
        · simp only [fixpointRec, if_neg h]; exact ih (F x) (hF x hx)
  exact key 20 [] (by intro x hx; simp at hx)

/-! ## The analysis

`live c L` is the set of variables live *before* `c`, given that `L` are the
variables live *after* it.  The interesting case is assignment: if `x` is live
afterwards, then the assignment is useful, `x` itself is no longer live before
it, and everything `a` reads becomes live; if `x` is dead afterwards, the
assignment changes nothing. -/

def live (c : com) (L : IdentSet) : IdentSet :=
  match c with
  | .skip => L
  | .assign x a => if x ∈ L then remove x L ++ fvAexp a else L
  | .seq c₁ c₂ => live c₁ (live c₂ L)
  | .ifthenelse b c₁ c₂ => fvBexp b ++ (live c₁ L ++ live c₂ L)
  | .while b c =>
      fixpoint (fun x => (fvBexp b ++ L) ++ live c x) (fvCom (.while b c) ++ L)
  termination_by c

@[simp] theorem live_skip (L : IdentSet) : live .skip L = L := by rw [live]

@[simp] theorem live_assign (x : Ident) (a : aexp) (L : IdentSet) :
    live (.assign x a) L = if x ∈ L then remove x L ++ fvAexp a else L := by rw [live]

@[simp] theorem live_seq (c₁ c₂ : com) (L : IdentSet) :
    live (c₁ ;; c₂) L = live c₁ (live c₂ L) := by rw [live]

@[simp] theorem live_ifthenelse (b : bexp) (c₁ c₂ : com) (L : IdentSet) :
    live (.ifthenelse b c₁ c₂) L = fvBexp b ++ (live c₁ L ++ live c₂ L) := by rw [live]

theorem live_while (b : bexp) (c : com) (L : IdentSet) :
    live (.while b c) L
      = fixpoint (fun x => (fvBexp b ++ L) ++ live c x) (fvCom (.while b c) ++ L) := by
  rw [live]

theorem live_upper_bound : ∀ (c : com) (L : IdentSet),
    Incl (live c L) (fvCom c ++ L)
  | .skip, L => by intro x hx; simpa [fvCom] using hx
  | .assign y a, L => by
      intro x hx
      simp only [live_assign] at hx
      by_cases hy : y ∈ L <;> simp_all [fvCom] <;> grind
  | .seq c₁ c₂, L => by
      intro x hx
      simp only [live_seq] at hx
      have h₁ := live_upper_bound c₁ (live c₂ L) x hx
      have h₂ := fun h => live_upper_bound c₂ L x h
      simp only [fvCom, List.mem_append] at h₁ h₂ ⊢
      grind
  | .ifthenelse b c₁ c₂, L => by
      intro x hx
      have h₁ := fun h => live_upper_bound c₁ L x h
      have h₂ := fun h => live_upper_bound c₂ L x h
      simp only [live_ifthenelse, fvCom, List.mem_append] at hx h₁ h₂ ⊢
      grind
  | .while b c, L => by
      rw [live_while]
      refine fixpoint_upper_bound ?_
      intro y hy z hz
      have h := fun h => live_upper_bound c y z h
      have hy' := fun h => hy z h
      simp only [fvCom, List.mem_append] at hz h hy' ⊢
      grind

/-- The three properties of the loop's fixpoint that the correctness proof
uses: the test's variables are live before the loop, the variables live after
it are live before it, and one more pass round the body adds nothing. -/
theorem live_while_charact (b : bexp) (c : com) (L : IdentSet) :
    Incl (fvBexp b) (live (.while b c) L)
    ∧ Incl L (live (.while b c) L)
    ∧ Incl (live c (live (.while b c) L)) (live (.while b c) L) := by
  have hc := fixpoint_charact (fun x => (fvBexp b ++ L) ++ live c x)
    (fvCom (.while b c) ++ L)
  rw [live_while]
  rcases hc with hc | hc
  · exact ⟨fun x hx => hc x (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hx)))),
      fun x hx => hc x (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))),
      fun x hx => hc x (List.mem_append.mpr (.inr hx))⟩
  · rw [hc]
    refine ⟨fun x hx => by simp [fvCom, hx], fun x hx => by simp [hx], ?_⟩
    intro x hx
    have := live_upper_bound c (fvCom (.while b c) ++ L) x hx
    simp only [fvCom, List.mem_append] at this ⊢
    grind

/-! ## The optimisation

Dead code elimination replaces an assignment to a dead variable by `skip`. -/

def dce (c : com) (L : IdentSet) : com :=
  match c with
  | .skip => .skip
  | .assign x a => if x ∈ L then .assign x a else .skip
  | .seq c₁ c₂ => .seq (dce c₁ (live c₂ L)) (dce c₂ L)
  | .ifthenelse b c₁ c₂ => .ifthenelse b (dce c₁ L) (dce c₂ L)
  | .while b c => .while b (dce c (live (.while b c) L))
  termination_by c

@[simp] theorem dce_skip (L : IdentSet) : dce .skip L = .skip := by rw [dce]

@[simp] theorem dce_assign (x : Ident) (a : aexp) (L : IdentSet) :
    dce (.assign x a) L = if x ∈ L then .assign x a else .skip := by rw [dce]

@[simp] theorem dce_seq (c₁ c₂ : com) (L : IdentSet) :
    dce (c₁ ;; c₂) L = (dce c₁ (live c₂ L) ;; dce c₂ L) := by rw [dce]

@[simp] theorem dce_ifthenelse (b : bexp) (c₁ c₂ : com) (L : IdentSet) :
    dce (.ifthenelse b c₁ c₂) L = .ifthenelse b (dce c₁ L) (dce c₂ L) := by rw [dce]

@[simp] theorem dce_while (b : bexp) (c : com) (L : IdentSet) :
    dce (.while b c) L = .while b (dce c (live (.while b c) L)) := by rw [dce]

/-- If only `"r"` matters at the end, the updates of `"q"` are dead. -/
example : dce euclideanDivision ["r"]
    = (.assign "r" (.var "a") ;; .skip ;;
       .while (.lessequal (.var "b") (.var "r"))
         (.assign "r" (.minus (.var "r") (.var "b")) ;; .skip)) := by
  native_decide

/-- If `"q"` matters, nothing can be removed. -/
example : dce euclideanDivision ["q"] = euclideanDivision := by native_decide

/-! ## Correctness

Two stores *agree* on a set of variables when they give those variables the
same values.  The optimised program runs in a store that may differ from the
original one on dead variables — that is the whole point — so the invariant
relating the two executions is agreement on the live variables. -/

def agree (L : IdentSet) (s₁ s₂ : Store) : Prop := ∀ x, x ∈ L → s₁ x = s₂ x

theorem agree.mono {L L' : IdentSet} {s₁ s₂ : Store} (h : agree L' s₁ s₂)
    (hsub : Incl L L') : agree L s₁ s₂ := fun x hx => h x (hsub x hx)

theorem aeval_agree {L : IdentSet} {s₁ s₂ : Store} (h : agree L s₁ s₂) :
    ∀ (a : aexp), Incl (fvAexp a) L → aeval s₁ a = aeval s₂ a
  | .const _, _ => rfl
  | .var x, hsub => h x (hsub x (by simp [fvAexp]))
  | .plus a₁ a₂, hsub => by
      simp only [aeval, aeval_agree h a₁ (fun x hx => hsub x (by simp [fvAexp, hx])),
        aeval_agree h a₂ (fun x hx => hsub x (by simp [fvAexp, hx]))]
  | .minus a₁ a₂, hsub => by
      simp only [aeval, aeval_agree h a₁ (fun x hx => hsub x (by simp [fvAexp, hx])),
        aeval_agree h a₂ (fun x hx => hsub x (by simp [fvAexp, hx]))]

theorem beval_agree {L : IdentSet} {s₁ s₂ : Store} (h : agree L s₁ s₂) :
    ∀ (b : bexp), Incl (fvBexp b) L → beval s₁ b = beval s₂ b
  | .true, _ => rfl
  | .false, _ => rfl
  | .equal a₁ a₂, hsub => by
      simp only [beval, aeval_agree h a₁ (fun x hx => hsub x (by simp [fvBexp, hx])),
        aeval_agree h a₂ (fun x hx => hsub x (by simp [fvBexp, hx]))]
  | .lessequal a₁ a₂, hsub => by
      simp only [beval, aeval_agree h a₁ (fun x hx => hsub x (by simp [fvBexp, hx])),
        aeval_agree h a₂ (fun x hx => hsub x (by simp [fvBexp, hx]))]
  | .not b₁, hsub => by
      simp only [beval, beval_agree h b₁ (fun x hx => hsub x (by simpa [fvBexp] using hx))]
  | .and b₁ b₂, hsub => by
      simp only [beval, beval_agree h b₁ (fun x hx => hsub x (by simp [fvBexp, hx])),
        beval_agree h b₂ (fun x hx => hsub x (by simp [fvBexp, hx]))]

/-- Agreement survives assigning the same value to a live variable on both
sides. -/
theorem agree_update_live {s₁ s₂ : Store} {L : IdentSet} {x : Ident} {v : Int}
    (h : agree (remove x L) s₁ s₂) : agree L (update x v s₁) (update x v s₂) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp [update]
  · simp only [update, if_neg hyx]
    exact h y (by simp [hy, hyx])

/-- And it survives assigning to a dead variable on one side only. -/
theorem agree_update_dead {s₁ s₂ : Store} {L : IdentSet} {x : Ident} {v : Int}
    (h : agree L s₁ s₂) (hx : x ∉ L) : agree L (update x v s₁) s₂ := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; exact absurd hy hx
  · simp only [update, if_neg hyx]; exact h y hy

/-- Semantic preservation for terminating programs.  Read the statement as a
diagram: from stores agreeing on `live c L`, running `c` on the left and
`dce c L` on the right lands in stores agreeing on `L`. -/
theorem dce_correct_terminating {s c s'} (h : cexec s c s') :
    ∀ (L : IdentSet) (s₁ : Store), agree (live c L) s s₁ →
    ∃ s₁', cexec s₁ (dce c L) s₁' ∧ agree L s' s₁' := by
  induction h with
  | skip s => exact fun L s₁ ha => ⟨s₁, by simpa using cexec.skip s₁, by simpa using ha⟩
  | assign s x a =>
      intro L s₁ ha
      simp only [live_assign] at ha
      simp only [dce_assign]
      by_cases hx : x ∈ L
      · -- `x` is live afterwards: keep the assignment
        simp only [if_pos hx] at ha ⊢
        have heq : aeval s a = aeval s₁ a :=
          aeval_agree ha a (fun y hy => by simp [hy])
        refine ⟨update x (aeval s₁ a) s₁, .assign _ _ _, ?_⟩
        rw [← heq]
        exact agree_update_live (ha.mono (fun y hy => by simp at hy; simp [hy]))
      · -- `x` is dead afterwards: replace the assignment by `skip`
        simp only [if_neg hx] at ha ⊢
        exact ⟨s₁, .skip _, agree_update_dead ha hx⟩
  | @seq c₁ c₂ s s' s'' _ _ ih₁ ih₂ =>
      intro L s₁ ha
      simp only [live_seq] at ha
      obtain ⟨t₁, he₁, ha₁⟩ := ih₁ (live c₂ L) s₁ ha
      obtain ⟨t₂, he₂, ha₂⟩ := ih₂ L t₁ ha₁
      exact ⟨t₂, by simpa using cexec.seq he₁ he₂, ha₂⟩
  | @ifthenelse b c₁ c₂ s s' _ ih =>
      intro L s₁ ha
      simp only [live_ifthenelse] at ha
      have heq : beval s b = beval s₁ b :=
        beval_agree ha b (fun y hy => by simp [hy])
      obtain ⟨t, he, hat⟩ := ih L s₁ (by
        cases hb : beval s b
        · exact ha.mono (fun y hy => by simp at hy ⊢; grind)
        · exact ha.mono (fun y hy => by simp at hy ⊢; grind))
      refine ⟨t, ?_, hat⟩
      simp only [dce_ifthenelse]
      refine .ifthenelse ?_
      rw [← heq]
      cases hb : beval s b <;> rw [hb] at he <;> simpa using he
  | @while_done b c s hb =>
      intro L s₁ ha
      obtain ⟨hP, hQ, _⟩ := live_while_charact b c L
      have hb₁ : beval s₁ b = false := by rw [← beval_agree ha b hP]; exact hb
      exact ⟨s₁, by simpa using cexec.while_done hb₁, ha.mono hQ⟩
  | @while_loop b c s s' s'' hb _ _ ih₁ ih₂ =>
      intro L s₁ ha
      obtain ⟨hP, hQ, hR⟩ := live_while_charact b c L
      have hb₁ : beval s₁ b = true := by rw [← beval_agree ha b hP]; exact hb
      obtain ⟨t₁, he₁, ha₁⟩ := ih₁ (live (.while b c) L) s₁ (ha.mono hR)
      obtain ⟨t₂, he₂, ha₂⟩ := ih₂ L t₁ ha₁
      refine ⟨t₂, ?_, ha₂⟩
      simp only [dce_while]
      exact .while_loop hb₁ he₁ (by simpa using he₂)

end Deadcode
