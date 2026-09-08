/-
  Fixpoints: from Knaster–Tarski to an algorithm that computes them.

  Lean 4 port of `Fixpoints.v` from the Coq development accompanying
  Xavier Leroy, *Proving the correctness of a compiler*,
  EUTypes 2019 Summer School.

  Original Coq sources: Copyright 2019, 2025 Xavier Leroy.
  This file is a modified work: the definitions and theorem statements follow
  the Coq originals, but all proofs and explanatory text have been rewritten
  for Lean 4.  Since abstract stores are association lists here rather than
  Coq `FMaps`, the well-foundedness argument is carried out over the list of
  distinct keys instead of over a finite map's cardinal.

  Distributed under the GNU Lesser General Public License, version 2.1
  or (at your option) any later version.  See LICENSE.md.
-/
import CompilerVerification.Constprop

/-!
# More about fixpoints

`Constprop.lean` analysed loops with a deliberately crude fixpoint: iterate
twenty times and give up.  That is sound but imprecise.  Here we do the job
properly.

The first half is the general theory.  Knaster–Tarski guarantees that a
monotone function on a suitable ordered set has a fixpoint, and its proof is
already an algorithm — iterate from the bottom until nothing changes — but
extracting that algorithm needs care: an existence proof (`∃ x, …`) gives no
way to *compute* `x`.  In Lean, as in Coq, the way out is to produce a
subtype `{ x // … }` instead, which carries the value along with its
specification.

The second half applies the theory to the abstract stores of constant
propagation.  Two obstacles appear, exactly as in the Coq development: the
strict order has to be shown well founded, and abstract stores have no bottom
element, so the iteration must start somewhere else.
-/

namespace Fixpoints

open IMP Constprop

/-! ## The general theory

We package the requirements on the ordered set as a structure: a decidable
equality, a transitive order, and — the crucial hypothesis — well-foundedness
of the induced strict order, which is what says that every strictly ascending
chain is finite. -/

/-- The data needed to run a fixpoint iteration on a type `A`. -/
structure FixLattice (A : Type u) where
  /-- Equality on `A` (need not be syntactic equality). -/
  eq : A → A → Prop
  /-- A decision procedure for `eq`. -/
  beq : A → A → Bool
  beq_eq : ∀ {x y}, beq x y = true → eq x y
  beq_neq : ∀ {x y}, beq x y = false → ¬ eq x y
  /-- The order. -/
  le : A → A → Prop
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  /-- Every strictly ascending chain is finite. -/
  gt_wf : WellFounded (fun x y => le y x ∧ ¬ eq y x)

namespace FixLattice

variable {A : Type u} (L : FixLattice A) (F : A → A)

/-- The strict order induced by `le`. -/
def Gt (x y : A) : Prop := L.le y x ∧ ¬ L.eq y x

/-- **Knaster–Tarski.**  A monotone function has a fixpoint.  The proof is by
well-founded induction on the strict order: starting from a pre-fixpoint `x`
(one with `x ≤ F x`), either `x` is already a fixpoint, or `F x` is strictly
above `x` and is itself a pre-fixpoint, so we recurse. -/
theorem fixpoint_exists (Fmon : ∀ x y, L.le x y → L.le (F x) (F y))
    (bot : A) (bot_smallest : ∀ x, L.le bot x) : ∃ x, L.eq x (F x) := by
  have key : ∀ x, L.le x (F x) → ∃ y, L.eq y (F y) := by
    intro x
    refine L.gt_wf.induction (C := fun x => L.le x (F x) → ∃ y, L.eq y (F y)) x ?_
    intro x ih hpre
    cases hb : L.beq x (F x)
    · exact ih (F x) ⟨hpre, L.beq_neq hb⟩ (Fmon _ _ hpre)
    · exact ⟨x, L.beq_eq hb⟩
  exact key bot (bot_smallest _)

/-- The same argument, but producing the fixpoint rather than merely asserting
that one exists.  `iterate` takes a pre-fixpoint `x` together with a proof
that `x` is below every post-fixpoint, and returns the fixpoint reached from
`x`, together with proofs that it *is* a fixpoint and that it is still below
every post-fixpoint — that is, that it is the *least* one. -/
def iterate (Fmon : ∀ x y, L.le x y → L.le (F x) (F y)) :
    ∀ (x : A), L.le x (F x) → (∀ z, L.le (F z) z → L.le x z) →
      { y : A // L.eq y (F y) ∧ ∀ z, L.le (F z) z → L.le y z } :=
  L.gt_wf.fix fun x ih hpre hsmall =>
    match hb : L.beq x (F x) with
    | true => ⟨x, L.beq_eq hb, hsmall⟩
    | false =>
        ih (F x) ⟨hpre, L.beq_neq hb⟩ (Fmon _ _ hpre)
          (fun z hz => L.le_trans (Fmon _ _ (hsmall z hz)) hz)

/-- The least fixpoint reached by iterating from a given pre-fixpoint. -/
def fixpointFrom (Fmon : ∀ x y, L.le x y → L.le (F x) (F y))
    (init : A) (hpre : L.le init (F init))
    (hsmall : ∀ z, L.le (F z) z → L.le init z) : A :=
  (L.iterate F Fmon init hpre hsmall).1

theorem fixpointFrom_correct (Fmon : ∀ x y, L.le x y → L.le (F x) (F y))
    (init : A) (hpre : L.le init (F init))
    (hsmall : ∀ z, L.le (F z) z → L.le init z) :
    L.eq (L.fixpointFrom F Fmon init hpre hsmall) (F (L.fixpointFrom F Fmon init hpre hsmall))
    ∧ ∀ z, L.le (F z) z → L.le (L.fixpointFrom F Fmon init hpre hsmall) z :=
  (L.iterate F Fmon init hpre hsmall).2

/-- When the lattice does have a bottom element, iterating from it gives the
least fixpoint outright. -/
def fixpoint (Fmon : ∀ x y, L.le x y → L.le (F x) (F y))
    (bot : A) (bot_smallest : ∀ x, L.le bot x) : A :=
  L.fixpointFrom F Fmon bot (bot_smallest _) (fun z _ => bot_smallest z)

theorem fixpoint_correct (Fmon : ∀ x y, L.le x y → L.le (F x) (F y))
    (bot : A) (bot_smallest : ∀ x, L.le bot x) :
    L.eq (L.fixpoint F Fmon bot bot_smallest) (F (L.fixpoint F Fmon bot bot_smallest))
    ∧ ∀ z, L.le (F z) z → L.le (L.fixpoint F Fmon bot bot_smallest) z :=
  L.fixpointFrom_correct F Fmon bot _ _

end FixLattice

/-! ## Application to constant propagation

To instantiate the theory at abstract stores we must supply the pieces of
`FixLattice`.  Everything is easy except `gt_wf`. -/

/-- Extensional equality of abstract stores. -/
def AEq (S₁ S₂ : AStore) : Prop := ∀ x, S₁.find x = S₂.find x

theorem AEq_symm {S₁ S₂ : AStore} (h : AEq S₁ S₂) : AEq S₂ S₁ := fun x => (h x).symm

theorem AEq_Le {S₁ S₂ : AStore} (h : AEq S₁ S₂) : Le S₁ S₂ := fun x n hf => by
  rw [h x]; exact hf

theorem equal_AEq {S₁ S₂ : AStore} (h : AStore.equal S₁ S₂ = true) : AEq S₁ S₂ :=
  AStore.equal_find h

theorem AEq_equal {S₁ S₂ : AStore} (h : AEq S₁ S₂) : AStore.equal S₁ S₂ = true := by
  simp only [AStore.equal, List.all_eq_true]
  intro x _
  simp [h x]

theorem equal_nAEq {S₁ S₂ : AStore} (h : AStore.equal S₁ S₂ = false) : ¬ AEq S₁ S₂ := by
  intro he
  rw [AEq_equal he] at h
  simp at h

/-! ### Well-foundedness

This is the one genuinely hard proof.  We measure an abstract store by the
number of *distinct* variables it says something about.  Going strictly up in
the order means losing at least one such fact, so the measure strictly
decreases, and `Nat` is well founded. -/

/-- Remove duplicates from a list of variables. -/
def dedup : List Ident → List Ident
  | [] => []
  | a :: l => if a ∈ dedup l then dedup l else a :: dedup l

@[simp] theorem mem_dedup (x : Ident) (l : List Ident) : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons a l ih =>
      by_cases h : a ∈ dedup l
      · have hd : dedup (a :: l) = dedup l := by simp [dedup, h]
        rw [hd, ih]
        refine ⟨fun hx => List.mem_cons_of_mem _ hx, fun hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ih.mp h
        · exact hx
      · have hd : dedup (a :: l) = a :: dedup l := by simp [dedup, h]
        rw [hd]; simp [ih]

theorem nodup_dedup : ∀ (l : List Ident), (dedup l).Nodup
  | [] => by simp [dedup]
  | a :: l => by
      by_cases h : a ∈ dedup l
      · simpa [dedup, h] using nodup_dedup l
      · simp only [dedup, if_neg h]
        exact List.nodup_cons.mpr ⟨h, nodup_dedup l⟩

/-- A list with no duplicates is no longer than any list containing it. -/
theorem nodup_length_le : ∀ {l₁ l₂ : List Ident}, l₁.Nodup → l₁ ⊆ l₂ →
    l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l₁, l₂, hnd, hsub => by
      obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
      have ha : a ∈ l₂ := hsub (by simp)
      have hsub' : l₁ ⊆ l₂.erase a := by
        intro x hx
        exact (List.mem_erase_of_ne (by rintro rfl; exact hna hx)).mpr (hsub (by simp [hx]))
      have hle := nodup_length_le hnd' hsub'
      rw [List.length_erase_of_mem ha] at hle
      have : 0 < l₂.length := List.length_pos_of_mem ha
      simpa using by omega

/-- Two duplicate-free lists of the same length, one contained in the other,
contain each other. -/
theorem subset_of_length_le {l₁ l₂ : List Ident} (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂)
    (hlen : l₂.length ≤ l₁.length) : l₂ ⊆ l₁ := by
  intro b hb
  by_cases hnb : b ∈ l₁
  · exact hnb
  · exfalso
    have hsub' : l₁ ⊆ l₂.erase b := by
      intro x hx
      exact (List.mem_erase_of_ne (by rintro rfl; exact hnb hx)).mpr (hsub hx)
    have hle := nodup_length_le hnd hsub'
    rw [List.length_erase_of_mem hb] at hle
    have : 0 < l₂.length := List.length_pos_of_mem hb
    omega

/-- The variables an abstract store knows something about, without
duplicates. -/
def dom (S : AStore) : List Ident := dedup S.keys

theorem mem_dom {S : AStore} {x : Ident} : x ∈ dom S ↔ (S.find x).isSome = true := by
  rw [dom, mem_dedup, AStore.find_isSome_iff]

/-- The measure: how many variables the store pins down. -/
def card (S : AStore) : Nat := (dom S).length

theorem Le_card {S T : AStore} (h : Le T S) :
    card S ≤ card T ∧ (card S = card T → AEq T S) := by
  have hsub : dom S ⊆ dom T := by
    intro x hx
    rw [mem_dom] at hx ⊢
    cases hf : S.find x with
    | none => rw [hf] at hx; simp at hx
    | some n => rw [h x n hf]; rfl
  have hle : card S ≤ card T := nodup_length_le (nodup_dedup _) hsub
  refine ⟨hle, fun heq => ?_⟩
  have hsup : dom T ⊆ dom S :=
    subset_of_length_le (nodup_dedup _) hsub (by simp only [card] at heq; omega)
  intro x
  cases hf : S.find x with
  | some n => exact h x n hf
  | none =>
      cases hg : T.find x with
      | none => rfl
      | some m =>
          exfalso
          have : x ∈ dom T := mem_dom.mpr (by rw [hg]; rfl)
          have := mem_dom.mp (hsup this)
          rw [hf] at this; simp at this

theorem Gt_card {S S' : AStore} (h : Le S' S ∧ ¬ AEq S' S) : card S < card S' := by
  obtain ⟨hle, hne⟩ := h
  obtain ⟨hcard, heq⟩ := Le_card hle
  have : card S ≠ card S' := fun e => hne (heq e)
  omega

theorem Gt_wf : WellFounded (fun S S' : AStore => Le S' S ∧ ¬ AEq S' S) :=
  Subrelation.wf Gt_card (invImage card Nat.lt_wfRel).wf

/-- Abstract stores as a lattice for the fixpoint machinery. -/
def storeLattice : FixLattice AStore where
  eq := AEq
  beq := AStore.equal
  beq_eq := equal_AEq
  beq_neq := fun {x y} h => equal_nAEq (by
    cases hv : AStore.equal x y with
    | false => rfl
    | true => rw [hv] at h; simp at h)
  le := Le
  le_trans := fun h₁ h₂ => Le.trans h₁ h₂
  gt_wf := Gt_wf

/-! ### Iterating from a starting point

Abstract stores have no bottom element, so we cannot iterate from one.  But
for the functions we care about there is a natural pre-fixpoint to start from:
the abstract store `init` describing what is known on entry to the loop.  We
iterate `X ↦ init ⊔ F X`, which is above `init` by construction. -/

/-- A function on abstract stores is *increasing* when it preserves the
order.  Only increasing functions have fixpoints, which is exactly what makes
the definition of the analyser below delicate. -/
def Increasing (F : AStore → AStore) : Prop := ∀ x y, Le x y → Le (F x) (F y)

theorem join_increasing {S₁ S₂ S₃ S₄ : AStore} (h₁ : Le S₁ S₂) (h₂ : Le S₃ S₄) :
    Le (AStore.join S₁ S₃) (AStore.join S₂ S₄) := by
  intro x n hf
  obtain ⟨ha, hb⟩ := (AStore.find_join S₂ S₄ x n).mp hf
  exact (AStore.find_join S₁ S₃ x n).mpr ⟨h₁ x n ha, h₂ x n hb⟩

/-- The least fixpoint of `X ↦ init ⊔ F X`. -/
def fixpointJoin (init : AStore) (F : AStore → AStore) (hF : Increasing F) : AStore :=
  storeLattice.fixpointFrom (fun X => AStore.join init (F X))
    (fun x y h => join_increasing (fun _ _ hf => hf) (hF x y h))
    init (Le_join_left _ _)
    (fun z hz => Le.trans (Le_join_left init (F z)) hz)

theorem fixpointJoin_eq (init : AStore) (F : AStore → AStore) (hF : Increasing F) :
    AEq (AStore.join init (F (fixpointJoin init F hF))) (fixpointJoin init F hF) :=
  AEq_symm (storeLattice.fixpointFrom_correct _ _ _ _ _).1

theorem fixpointJoin_sound (init : AStore) (F : AStore → AStore) (hF : Increasing F) :
    Le init (fixpointJoin init F hF) ∧ Le (F (fixpointJoin init F hF)) (fixpointJoin init F hF) := by
  have hle : Le (AStore.join init (F (fixpointJoin init F hF))) (fixpointJoin init F hF) :=
    AEq_Le (fixpointJoin_eq init F hF)
  exact ⟨Le.trans (Le_join_left _ _) hle, Le.trans (Le_join_right _ _) hle⟩

theorem fixpointJoin_smallest (init : AStore) (F : AStore → AStore) (hF : Increasing F)
    (S : AStore) (h : Le (AStore.join init (F S)) S) : Le (fixpointJoin init F hF) S :=
  (storeLattice.fixpointFrom_correct _ _ _ _ _).2 S h

theorem fixpointJoin_increasing (F : AStore → AStore) (hF : Increasing F)
    {S₁ S₂ : AStore} (h : Le S₁ S₂) :
    Le (fixpointJoin S₁ F hF) (fixpointJoin S₂ F hF) := by
  refine fixpointJoin_smallest _ _ _ _ ?_
  refine Le.trans (join_increasing h (fun _ _ hf => hf)) ?_
  exact AEq_Le (fixpointJoin_eq S₂ F hF)

/-! ### Defining the analyser and proving it increasing, simultaneously

We cannot define the abstract interpreter first and prove it increasing
afterwards: the loop case *needs* the increasing-ness of the body in order to
take a fixpoint at all.  So the function must return its own correctness
proof, as a subtype. -/

theorem Aeval_increasing {S₁ S₂ : AStore} (h : Le S₁ S₂) :
    ∀ (a : aexp) {n : Int}, Aeval S₂ a = some n → Aeval S₁ a = some n
  | .const _, _, hf => hf
  | .var x, n, hf => h x n hf
  | .plus a₁ a₂, n, hf => by
      simp only [Aeval] at hf ⊢
      cases h₁ : Aeval S₂ a₁ with
      | none => rw [h₁] at hf; simp at hf
      | some n₁ =>
          cases h₂ : Aeval S₂ a₂ with
          | none => rw [h₁, h₂] at hf; simp at hf
          | some n₂ =>
              rw [h₁, h₂] at hf
              rw [Aeval_increasing h a₁ h₁, Aeval_increasing h a₂ h₂]; exact hf
  | .minus a₁ a₂, n, hf => by
      simp only [Aeval] at hf ⊢
      cases h₁ : Aeval S₂ a₁ with
      | none => rw [h₁] at hf; simp at hf
      | some n₁ =>
          cases h₂ : Aeval S₂ a₂ with
          | none => rw [h₁, h₂] at hf; simp at hf
          | some n₂ =>
              rw [h₁, h₂] at hf
              rw [Aeval_increasing h a₁ h₁, Aeval_increasing h a₂ h₂]; exact hf

theorem Beval_increasing {S₁ S₂ : AStore} (h : Le S₁ S₂) :
    ∀ (b : bexp) {v : Bool}, Beval S₂ b = some v → Beval S₁ b = some v
  | .true, _, hf => hf
  | .false, _, hf => hf
  | .equal a₁ a₂, v, hf => by
      simp only [Beval] at hf ⊢
      cases h₁ : Aeval S₂ a₁ with
      | none => rw [h₁] at hf; simp at hf
      | some n₁ =>
          cases h₂ : Aeval S₂ a₂ with
          | none => rw [h₁, h₂] at hf; simp at hf
          | some n₂ =>
              rw [h₁, h₂] at hf
              rw [Aeval_increasing h a₁ h₁, Aeval_increasing h a₂ h₂]; exact hf
  | .lessequal a₁ a₂, v, hf => by
      simp only [Beval] at hf ⊢
      cases h₁ : Aeval S₂ a₁ with
      | none => rw [h₁] at hf; simp at hf
      | some n₁ =>
          cases h₂ : Aeval S₂ a₂ with
          | none => rw [h₁, h₂] at hf; simp at hf
          | some n₂ =>
              rw [h₁, h₂] at hf
              rw [Aeval_increasing h a₁ h₁, Aeval_increasing h a₂ h₂]; exact hf
  | .not b₁, v, hf => by
      simp only [Beval] at hf ⊢
      cases h₁ : Beval S₂ b₁ with
      | none => rw [h₁] at hf; simp at hf
      | some v₁ => rw [h₁] at hf; rw [Beval_increasing h b₁ h₁]; exact hf
  | .and b₁ b₂, v, hf => by
      simp only [Beval] at hf ⊢
      cases h₁ : Beval S₂ b₁ with
      | none => rw [h₁] at hf; simp at hf
      | some v₁ =>
          cases h₂ : Beval S₂ b₂ with
          | none => rw [h₁, h₂] at hf; simp at hf
          | some v₂ =>
              rw [h₁, h₂] at hf
              rw [Beval_increasing h b₁ h₁, Beval_increasing h b₂ h₂]; exact hf

theorem update_increasing {S₁ S₂ : AStore} (x : Ident) (a : aexp) (h : Le S₁ S₂) :
    Le (AStore.update x (Aeval S₁ a) S₁) (AStore.update x (Aeval S₂ a) S₂) := by
  intro y n hf
  rw [AStore.find_update] at hf ⊢
  by_cases hyx : y = x
  · simp only [hyx, if_true] at hf ⊢
    exact Aeval_increasing h a hf
  · simp only [hyx, if_false] at hf ⊢
    exact h y n hf

/-- The abstract interpreter, packaged with a proof that it is increasing.
Compare the crude `Constprop.Cexec`: the difference is entirely in the loop
case, which here takes a genuine least fixpoint. -/
def CexecM : com → { F : AStore → AStore // Increasing F }
  | .skip => ⟨id, fun _ _ h => h⟩
  | .assign x a =>
      ⟨fun S => AStore.update x (Aeval S a) S, fun _ _ h => update_increasing x a h⟩
  | .seq c₁ c₂ =>
      ⟨fun S => (CexecM c₂).1 ((CexecM c₁).1 S),
       fun _ _ h => (CexecM c₂).2 _ _ ((CexecM c₁).2 _ _ h)⟩
  | .ifthenelse b c₁ c₂ =>
      ⟨fun S =>
          match Beval S b with
          | some Bool.true => (CexecM c₁).1 S
          | some Bool.false => (CexecM c₂).1 S
          | none => AStore.join ((CexecM c₁).1 S) ((CexecM c₂).1 S),
       by
         intro y z h
         cases hz : Beval z b with
         | some v =>
             have hy : Beval y b = some v := Beval_increasing h b hz
             cases v
             · simp only [hy, hz]; exact (CexecM c₂).2 _ _ h
             · simp only [hy, hz]; exact (CexecM c₁).2 _ _ h
         | none =>
             cases hy : Beval y b with
             | some v =>
                 cases v
                 · simp only [hy, hz]
                   exact Le.trans ((CexecM c₂).2 _ _ h) (Le_join_right _ _)
                 · simp only [hy, hz]
                   exact Le.trans ((CexecM c₁).2 _ _ h) (Le_join_left _ _)
             | none =>
                 simp only [hy, hz]
                 exact join_increasing ((CexecM c₁).2 _ _ h) ((CexecM c₂).2 _ _ h)⟩
  | .while _ c₁ =>
      ⟨fun S => fixpointJoin S (CexecM c₁).1 (CexecM c₁).2,
       fun _ _ h => fixpointJoin_increasing _ _ h⟩

end Fixpoints
