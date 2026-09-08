/-
  Sequences of transitions.

  Lean 4 port of `Sequences.v` from the Coq development accompanying
  Xavier Leroy, *Proving the correctness of a compiler*,
  EUTypes 2019 Summer School.

  Original Coq sources: Copyright 2019, 2025 Xavier Leroy.
  This file is a modified work: the statements follow the Coq originals,
  but the treatment of infinite sequences, all proofs, and all explanatory
  text have been rewritten for Lean 4.

  Distributed under the GNU Lesser General Public License, version 2.1
  or (at your option) any later version.  See LICENSE.md.
-/

/-!
# Sequences of transitions

Operational semantics describes a program by a *transition relation*
`R : A → A → Prop` on machine states.  Reasoning about whole executions rather
than single steps means reasoning about the reflexive transitive closure of
`R`, about its transitive closure, and about the *infinite* sequences of
transitions that model divergence.  This file sets those notions up once, so
that the semantics of IMP and the semantics of the stack machine can share
them.
-/

namespace Sequences

universe u
variable {A : Type u} {R : A → A → Prop} {a b c : A}

/-! ## Finite sequences of transitions -/

/-- `Star R a b`: state `b` is reachable from `a` in zero, one or several
`R` transitions — the reflexive transitive closure of `R`. -/
inductive Star (R : A → A → Prop) : A → A → Prop where
  | refl (a : A) : Star R a a
  | step {a b c : A} (h : R a b) (hs : Star R b c) : Star R a c

/-- `Plus R a b`: state `b` is reachable from `a` in *at least one* transition
— the transitive closure of `R`. -/
inductive Plus (R : A → A → Prop) : A → A → Prop where
  | left {a b c : A} (h : R a b) (hs : Star R b c) : Plus R a c

theorem Star.one (h : R a b) : Star R a b :=
  .step h (.refl b)

theorem Star.trans (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem Plus.one (h : R a b) : Plus R a b :=
  .left h (.refl b)

theorem Plus.star (h : Plus R a b) : Star R a b := by
  cases h with
  | left h hs => exact .step h hs

/-- One-or-more steps, then zero-or-more steps, is one-or-more steps. -/
theorem Plus.starTrans (h₁ : Plus R a b) (h₂ : Star R b c) : Plus R a c := by
  cases h₁ with
  | left h hs => exact .left h (hs.trans h₂)

/-- Zero-or-more steps, then one-or-more steps, is one-or-more steps. -/
theorem Star.plusTrans (h₁ : Star R a b) (h₂ : Plus R b c) : Plus R a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .left h (ih h₂).star

/-- Appending a final step to a finite sequence. -/
theorem Plus.right (h₁ : Star R a b) (h₂ : R b c) : Plus R a c :=
  h₁.plusTrans (.one h₂)

/-- A state is *irreducible* when no transition leaves it: the execution is
stuck, or has terminated. -/
def Irred (R : A → A → Prop) (a : A) : Prop := ∀ b, ¬ R a b

/-! ## Infinite sequences of transitions

Divergence is the existence of *one* infinite sequence
`a → a₁ → a₂ → ⋯` starting from `a`.  Two tempting definitions get this
wrong or make it unusable:

* "every finite sequence out of `a` can be extended" is a *different*
  property.  Take `R 0 0` and `R 0 1` on `Nat`: the sequence `0 →* 1` is
  stuck, yet `0 → 0 → 0 → ⋯` diverges.
* "there is an `f : Nat → A` with `f 0 = a` and `R (f i) (f (i+1))`" is
  correct, but such an `f` generally cannot be constructed, so the definition
  is awkward to use.

Coq's answer is a *coinductive* predicate — a greatest fixpoint.  Lean 4 has
no coinductive types, so we take the greatest fixpoint by hand: `Infseq R a`
holds when some set `X` contains `a` and is closed under taking one more
transition.  Such an `X` is an *invariant* witnessing that the execution can
always continue, and it is exactly what a proof by coinduction supplies.  The
constructor and the destructor below recover the coinductive interface, and
`Infseq.coinduction` is the coinduction principle — which here is just the
definition unfolded.
-/

/-- `Infseq R a`: there is an infinite sequence of `R` transitions out of `a`.
Defined as the greatest fixpoint of `a ↦ ∃ b, R a b ∧ ·` — that is, as the
existence of an invariant closed under one transition. -/
def Infseq (R : A → A → Prop) (a : A) : Prop :=
  ∃ X : A → Prop, X a ∧ ∀ x, X x → ∃ y, R x y ∧ X y

/-- The coinduction principle: an invariant closed under one transition
witnesses divergence from each of its members. -/
theorem Infseq.coinduction {X : A → Prop} (hX : ∀ x, X x → ∃ y, R x y ∧ X y)
    (ha : X a) : Infseq R a :=
  ⟨X, ha, hX⟩

/-- Destructor: a diverging state makes a transition to a diverging state. -/
theorem Infseq.inv (h : Infseq R a) : ∃ b, R a b ∧ Infseq R b := by
  obtain ⟨X, ha, hX⟩ := h
  obtain ⟨y, hy, hXy⟩ := hX a ha
  exact ⟨y, hy, X, hXy, hX⟩

/-- Constructor: one transition into a diverging state diverges. -/
theorem Infseq.step (h : R a b) (hb : Infseq R b) : Infseq R a := by
  refine Infseq.coinduction (X := fun x => x = a ∨ Infseq R x) ?_ (.inl rfl)
  rintro x (rfl | hx)
  · exact ⟨b, h, .inr hb⟩
  · obtain ⟨y, hy, hy'⟩ := hx.inv
    exact ⟨y, hy, .inr hy'⟩

/-- The variant of the coinduction principle in which the invariant is closed
under *one or several* transitions.  This is the form used to prove that
compiled code diverges: one source step may compile to several machine steps. -/
theorem Infseq.coinduction_plus {X : A → Prop}
    (hX : ∀ x, X x → ∃ y, Plus R x y ∧ X y) (ha : X a) : Infseq R a := by
  refine Infseq.coinduction (X := fun x => ∃ y, Star R x y ∧ X y) ?_ ⟨a, .refl a, ha⟩
  rintro x ⟨y, hxy, hXy⟩
  cases hxy with
  | refl =>
      obtain ⟨z, hz, hXz⟩ := hX x hXy
      cases hz with
      | left h hs => exact ⟨_, h, _, hs, hXz⟩
  | step h hs => exact ⟨_, h, _, hs, hXy⟩

/-- "Every finite sequence out of `a` can be extended."  As noted above this
is *not* the same as divergence, but it does imply it. -/
def AllSeqInf (R : A → A → Prop) (a : A) : Prop :=
  ∀ b, Star R a b → ∃ c, R b c

theorem Infseq.of_allSeqInf (h : AllSeqInf R a) : Infseq R a := by
  refine Infseq.coinduction (X := AllSeqInf R) ?_ h
  intro x hx
  obtain ⟨y, hy⟩ := hx x (.refl x)
  exact ⟨y, hy, fun z hz => hx z (.step hy hz)⟩

/-- The explicit-function characterisation also implies divergence. -/
theorem Infseq.of_function (f : Nat → A) (h₀ : f 0 = a) (h : ∀ i, R (f i) (f (i + 1))) :
    Infseq R a := by
  refine Infseq.coinduction (X := fun x => ∃ i, x = f i) ?_ ⟨0, h₀.symm⟩
  rintro x ⟨i, rfl⟩
  exact ⟨f (i + 1), h i, i + 1, rfl⟩

/-- A state with a self-loop diverges. -/
theorem Infseq.cycle (h : R a a) : Infseq R a :=
  Infseq.coinduction (X := fun x => x = a) (by intro x hx; subst hx; exact ⟨x, h, rfl⟩) rfl

/-! ## Determinism

A transition relation is *functional*, or deterministic, when every state has
at most one successor.  The semantics of the stack machine is functional, and
that is what lets us conclude that compiled code cannot both terminate and
diverge.
-/

section Deterministic

variable (hfun : ∀ a b c, R a b → R a c → b = c)

include hfun

/-- Two finite sequences out of the same state are prefixes of one another. -/
theorem star_star_inv (h₁ : Star R a b) : ∀ {c}, Star R a c → Star R b c ∨ Star R c b := by
  induction h₁ with
  | refl => exact fun h => .inl h
  | step h _ ih =>
      intro c hc
      cases hc with
      | refl => exact .inr (.step h (by assumption))
      | step h' hs' => exact ih (hfun _ _ _ h h' ▸ hs')

/-- A deterministic program has at most one terminal state. -/
theorem finseq_unique (h₁ : Star R a b) (i₁ : Irred R b) (h₂ : Star R a c)
    (i₂ : Irred R c) : b = c := by
  rcases star_star_inv hfun h₁ h₂ with h | h <;> cases h
  · rfl
  · exact absurd ‹R b _› (i₁ _)
  · rfl
  · exact absurd ‹R c _› (i₂ _)

/-- Divergence is preserved along a finite sequence. -/
theorem infseq_star_inv (h : Star R a b) (hi : Infseq R a) : Infseq R b := by
  induction h with
  | refl => exact hi
  | step h _ ih =>
      obtain ⟨y, hy, hy'⟩ := hi.inv
      exact ih (hfun _ _ _ h hy ▸ hy')

/-- A deterministic program cannot both diverge and reach a stuck state. -/
theorem infseq_finseq_excl (h : Star R a b) (hb : Irred R b) (hi : Infseq R a) : False := by
  obtain ⟨y, hy, _⟩ := (infseq_star_inv hfun h hi).inv
  exact hb y hy

/-- If some sequence out of `a` is infinite, then *every* sequence out of `a`
can be extended. -/
theorem infseq_all_seq_inf (hi : Infseq R a) : AllSeqInf R a := by
  intro b hb
  obtain ⟨y, hy, _⟩ := (infseq_star_inv hfun hb hi).inv
  exact ⟨y, hy⟩

end Deterministic

end Sequences
