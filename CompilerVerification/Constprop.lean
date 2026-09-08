/-
  Constant propagation: a forward dataflow analysis and the optimisation
  built on it.

  Lean 4 port of `Constprop.v` from the Coq development accompanying
  Xavier Leroy, *Proving the correctness of a compiler*,
  EUTypes 2019 Summer School.

  Original Coq sources: Copyright 2019, 2025 Xavier Leroy.
  This file is a modified work: the definitions and theorem statements follow
  the Coq originals, but all proofs and explanatory text have been rewritten
  for Lean 4.  Coq's `FMaps` library has no counterpart in Lean's core
  library, so abstract stores are implemented here as association lists.

  Distributed under the GNU Lesser General Public License, version 2.1
  or (at your option) any later version.  See LICENSE.md.
-/
import CompilerVerification.IMP

/-!
# Constant propagation

Two ingredients:

* **smart constructors** — functions that build an expression equivalent to
  the one asked for, but simplified on the fly, so that `PLUS a (CONST 0)`
  never gets built in the first place;
* a **static analysis** that computes, for each program point, which variables
  are known to hold which constants.

Combining them gives the optimisation `cpCom`, and we prove that it preserves
the behaviour of terminating programs.

The analysis is an instance of abstract interpretation.  We follow the usual
notational convention: capitalised names (`AStore`, `Aeval`, `Cexec`) denote
compile-time approximations, lower-case names (`Store`, `aeval`, `cexec`)
denote the run-time objects they approximate.
-/

namespace Constprop

open IMP

/-! ## Smart constructors for expressions -/

/-- Build an expression equivalent to `a + n`, simplified. -/
def mkPlusConst (a : aexp) (n : Int) : aexp :=
  if n = 0 then a else
    match a with
    | .const m => .const (m + n)
    | .plus a (.const m) => .plus a (.const (m + n))
    | _ => .plus a (.const n)

/-- Build an expression equivalent to `a₁ + a₂`, simplified.  Associativity
and commutativity are used to expose the pattern "expression plus constant",
which `mkPlusConst` then collapses. -/
def mkPlus (a₁ a₂ : aexp) : aexp :=
  match a₁, a₂ with
  | .const m, _ => mkPlusConst a₂ m
  | _, .const m => mkPlusConst a₁ m
  | .plus b₁ (.const m₁), .plus b₂ (.const m₂) => mkPlusConst (.plus b₁ b₂) (m₁ + m₂)
  | .plus b₁ (.const m₁), _ => mkPlusConst (.plus b₁ a₂) m₁
  | _, .plus b₂ (.const m₂) => mkPlusConst (.plus a₁ b₂) m₂
  | _, _ => .plus a₁ a₂

/-- Build an expression equivalent to `a₁ - a₂`, simplified.  Note that
"expression minus constant" is always normalised to "expression plus the
opposite constant", which keeps the case analysis small. -/
def mkMinus (a₁ a₂ : aexp) : aexp :=
  match a₁, a₂ with
  | _, .const m => mkPlusConst a₁ (-m)
  | .plus b₁ (.const m₁), .plus b₂ (.const m₂) => mkPlusConst (.minus b₁ b₂) (m₁ - m₂)
  | .plus b₁ (.const m₁), _ => mkPlusConst (.minus b₁ a₂) m₁
  | _, .plus b₂ (.const m₂) => mkPlusConst (.minus a₁ b₂) (-m₂)
  | _, _ => .minus a₁ a₂

/-- Simplify an expression by rewriting it bottom-up with the smart
constructors. -/
def simplifAexp : aexp → aexp
  | .const n => .const n
  | .var x => .var x
  | .plus a₁ a₂ => mkPlus (simplifAexp a₁) (simplifAexp a₂)
  | .minus a₁ a₂ => mkMinus (simplifAexp a₁) (simplifAexp a₂)

example : simplifAexp (.minus (.plus (.var "x") (.const 1)) (.plus (.var "y") (.const 1)))
    = .minus (.var "x") (.var "y") := by native_decide

/-- Soundness of the smart constructors: they build expressions that denote
what they claim to denote. -/
theorem mkPlusConst_sound (s : Store) (a : aexp) (n : Int) :
    aeval s (mkPlusConst a n) = aeval s a + n := by
  unfold mkPlusConst
  split
  · omega
  · split <;> simp [aeval] <;> omega

theorem mkPlus_sound (s : Store) (a₁ a₂ : aexp) :
    aeval s (mkPlus a₁ a₂) = aeval s a₁ + aeval s a₂ := by
  unfold mkPlus
  split <;> simp [mkPlusConst_sound, aeval] <;> omega

theorem mkMinus_sound (s : Store) (a₁ a₂ : aexp) :
    aeval s (mkMinus a₁ a₂) = aeval s a₁ - aeval s a₂ := by
  unfold mkMinus
  split <;> simp [mkPlusConst_sound, aeval] <;> omega

theorem simplifAexp_sound (s : Store) : ∀ a : aexp, aeval s (simplifAexp a) = aeval s a
  | .const _ => rfl
  | .var _ => rfl
  | .plus a₁ a₂ => by
      simp [simplifAexp, mkPlus_sound, simplifAexp_sound s a₁, simplifAexp_sound s a₂, aeval]
  | .minus a₁ a₂ => by
      simp [simplifAexp, mkMinus_sound, simplifAexp_sound s a₁, simplifAexp_sound s a₂, aeval]

/-! ### Smart constructors for Boolean expressions -/

def mkEqual (a₁ a₂ : aexp) : bexp :=
  match a₁, a₂ with
  | .const n₁, .const n₂ => if n₁ = n₂ then .true else .false
  | .plus b₁ (.const n₁), .const n₂ => .equal b₁ (.const (n₂ - n₁))
  | _, _ => .equal a₁ a₂

def mkLessequal (a₁ a₂ : aexp) : bexp :=
  match a₁, a₂ with
  | .const n₁, .const n₂ => if n₁ ≤ n₂ then .true else .false
  | .plus b₁ (.const n₁), .const n₂ => .lessequal b₁ (.const (n₂ - n₁))
  | _, _ => .lessequal a₁ a₂

def mkNot : bexp → bexp
  | .true => .false
  | .false => .true
  | .not b => b
  | b => .not b

def mkAnd : bexp → bexp → bexp
  | .true, b₂ => b₂
  | b₁, .true => b₁
  | .false, _ => .false
  | _, .false => .false
  | b₁, b₂ => .and b₁ b₂

theorem mkEqual_sound (s : Store) (a₁ a₂ : aexp) :
    beval s (mkEqual a₁ a₂) = (aeval s a₁ == aeval s a₂) := by
  unfold mkEqual
  split
  · split <;> simp_all [beval, aeval]
  · simp only [beval, aeval]
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega
  · rfl

theorem mkLessequal_sound (s : Store) (a₁ a₂ : aexp) :
    beval s (mkLessequal a₁ a₂) = decide (aeval s a₁ ≤ aeval s a₂) := by
  unfold mkLessequal
  split
  · split <;> rename_i h <;> simp [beval, aeval, h]
  · rename_i b₁ n₁ n₂
    have h : (aeval s b₁ ≤ n₂ - n₁) ↔ (aeval s b₁ + n₁ ≤ n₂) := by omega
    simp only [beval, aeval, h]
    rfl
  · rfl

theorem mkNot_sound (s : Store) (b : bexp) : beval s (mkNot b) = !beval s b := by
  unfold mkNot; split <;> simp [beval]

theorem mkAnd_sound (s : Store) (b₁ b₂ : bexp) :
    beval s (mkAnd b₁ b₂) = (beval s b₁ && beval s b₂) := by
  unfold mkAnd; split <;> simp [beval]

/-! ### Smart constructors for commands

Commands benefit too: a conditional whose test is statically known needs no
code at all. -/

def mkIfthenelse (b : bexp) (c₁ c₂ : com) : com :=
  match b with
  | .true => c₁
  | .false => c₂
  | _ => .ifthenelse b c₁ c₂

def mkWhile (b : bexp) (c : com) : com :=
  match b with
  | .false => .skip
  | _ => .while b c

theorem cexec_mkIfthenelse {s₁ : Store} {b : bexp} {c₁ c₂ : com} {s₂ : Store}
    (h : cexec s₁ (if beval s₁ b then c₁ else c₂) s₂) : cexec s₁ (mkIfthenelse b c₁ c₂) s₂ := by
  unfold mkIfthenelse
  split
  · subst_vars; simpa [beval] using h
  · subst_vars; simpa [beval] using h
  · exact .ifthenelse h

theorem cexec_mkWhile_done {s₁ : Store} {b : bexp} {c : com} (h : beval s₁ b = false) :
    cexec s₁ (mkWhile b c) s₁ := by
  unfold mkWhile
  split
  · exact .skip _
  · exact .while_done h

theorem cexec_mkWhile_loop {b : bexp} {c : com} {s₁ s₂ s₃ : Store}
    (hb : beval s₁ b = true) (h₁ : cexec s₁ c s₂) (h₂ : cexec s₂ (mkWhile b c) s₃) :
    cexec s₁ (mkWhile b c) s₃ := by
  revert h₂
  unfold mkWhile
  split
  · subst_vars; simp [beval] at hb
  · exact fun h₂ => .while_loop hb h₁ h₂

/-! ## Abstract stores

An *abstract store* records what the analysis knows before or after a program
point: if it maps `x` to `n`, then `x` certainly holds `n` at run time; if it
maps `x` to nothing, then `x` may hold anything.  So *less information* means
*larger* in the lattice order, and the top element is the empty map.

Coq's development uses the `FMaps` library.  Lean's core library has no finite
maps, so we use association lists and prove the handful of facts we need.
Nothing below depends on the representation beyond those facts. -/

/-- An abstract store: a finite map from variables to known values. -/
abbrev AStore := List (Ident × Int)

namespace AStore

/-- Look up the value the analysis knows for `x`, if any. -/
def find : AStore → Ident → Option Int
  | [], _ => none
  | (y, n) :: S, x => if x = y then some n else find S x

def keys (S : AStore) : List Ident := S.map Prod.fst

/-- Build an abstract store from a list of keys and a partial value
assignment. -/
def ofKeys : List Ident → (Ident → Option Int) → AStore
  | [], _ => []
  | x :: ks, f =>
      match f x with
      | some n => (x, n) :: ofKeys ks f
      | none => ofKeys ks f

theorem find_isSome_iff (S : AStore) (x : Ident) :
    (S.find x).isSome = true ↔ x ∈ S.keys := by
  induction S with
  | nil => simp [find, keys]
  | cons p S ih =>
      obtain ⟨y, n⟩ := p
      by_cases h : x = y <;> simp [find, keys, h, ih]

theorem find_eq_none_of_not_mem {S : AStore} {x : Ident} (h : x ∉ S.keys) :
    S.find x = none := by
  cases hf : S.find x with
  | none => rfl
  | some n => exact absurd ((find_isSome_iff S x).mp (by simp [hf])) h

theorem find_ofKeys (ks : List Ident) (f : Ident → Option Int) (x : Ident) :
    (ofKeys ks f).find x = if x ∈ ks then f x else none := by
  induction ks with
  | nil => simp [ofKeys, find]
  | cons y ks ih =>
      simp only [ofKeys]
      cases hf : f y with
      | none =>
          rw [ih]
          by_cases hxy : x = y
          · subst hxy; simp [hf]
          · simp [hxy]
      | some n =>
          by_cases hxy : x = y
          · subst hxy; simp [find, hf]
          · simp [find, hxy, ih]

/-- The top element: nothing is known about any variable. -/
def top : AStore := []

@[simp] theorem find_top (x : Ident) : top.find x = none := rfl

/-- The join of two abstract stores keeps only the facts they agree on. -/
def join (S₁ S₂ : AStore) : AStore :=
  ofKeys S₁.keys (fun x =>
    match S₁.find x, S₂.find x with
    | some n₁, some n₂ => if n₁ = n₂ then some n₁ else none
    | _, _ => none)

theorem find_join (S₁ S₂ : AStore) (x : Ident) (n : Int) :
    (join S₁ S₂).find x = some n ↔ S₁.find x = some n ∧ S₂.find x = some n := by
  rw [join, find_ofKeys]
  by_cases hx : x ∈ S₁.keys
  · simp only [hx, if_true]
    cases h₁ : S₁.find x with
    | none => simp
    | some n₁ =>
        cases h₂ : S₂.find x with
        | none => simp
        | some n₂ => by_cases he : n₁ = n₂ <;> simp [he] <;> omega
  · simp [hx, find_eq_none_of_not_mem hx]

/-- Update an abstract store: `some n` records that `x` holds `n`, `none`
records that nothing is known about `x` any more. -/
def update (x : Ident) (N : Option Int) (S : AStore) : AStore :=
  match N with
  | none => S.filter (fun p => !(p.1 == x))
  | some n => (x, n) :: S

set_option linter.unusedSimpArgs false in
theorem find_filter (S : AStore) (x y : Ident) :
    find (S.filter (fun p => !(p.1 == x))) y = if y = x then none else find S y := by
  induction S with
  | nil => by_cases h : y = x <;> simp [find, h]
  | cons p S ih =>
      obtain ⟨z, m⟩ := p
      by_cases hzx : z = x
      · subst hzx
        by_cases hyz : y = z
        · subst hyz; simp [ih]
        · simp [find, hyz, ih]
      · by_cases hyz : y = z
        · subst hyz; simp [List.filter_cons, find, hzx]
        · simp [find, hyz, hzx, ih]

theorem find_update (S : AStore) (x : Ident) (N : Option Int) (y : Ident) :
    (update x N S).find y = if y = x then N else S.find y := by
  cases N with
  | some n => by_cases h : y = x <;> simp [update, find, h]
  | none => simpa [update] using find_filter S x y

/-- Structural equality test on abstract stores, used to detect that the
fixpoint iteration has stabilised. -/
def equal (S₁ S₂ : AStore) : Bool :=
  (S₁.keys ++ S₂.keys).all (fun x => S₁.find x == S₂.find x)

theorem equal_find {S₁ S₂ : AStore} (h : equal S₁ S₂ = true) (x : Ident) :
    S₁.find x = S₂.find x := by
  by_cases hx : x ∈ S₁.keys ++ S₂.keys
  · simp only [equal, List.all_eq_true] at h
    simpa using h x hx
  · simp only [List.mem_append, not_or] at hx
    rw [find_eq_none_of_not_mem hx.1, find_eq_none_of_not_mem hx.2]

end AStore

/-! ### The lattice structure

`Le S₁ S₂` says that `S₁` is at least as precise as `S₂`: every fact recorded
by `S₂` is also recorded by `S₁`.  `Matches s S` says that the concrete store
`s` is one of the stores described by `S` — the abstract-interpretation
analogue of "a term has a type". -/

def Le (S₁ S₂ : AStore) : Prop := ∀ x n, S₂.find x = some n → S₁.find x = some n

def Matches (s : Store) (S : AStore) : Prop := ∀ x n, S.find x = some n → s x = n

theorem Matches.mono {s : Store} {S₁ S₂ : AStore} (hle : Le S₁ S₂) (h : Matches s S₁) :
    Matches s S₂ := fun x n hf => h x n (hle x n hf)

theorem Le.trans {S₁ S₂ S₃ : AStore} (h₁ : Le S₁ S₂) (h₂ : Le S₂ S₃) : Le S₁ S₃ :=
  fun x n hf => h₁ x n (h₂ x n hf)

theorem Le_top (S : AStore) : Le S AStore.top := fun _ _ hf => by simp at hf

theorem Le_join_left (S₁ S₂ : AStore) : Le S₁ (AStore.join S₁ S₂) :=
  fun x n hf => ((AStore.find_join S₁ S₂ x n).mp hf).1

theorem Le_join_right (S₁ S₂ : AStore) : Le S₂ (AStore.join S₁ S₂) :=
  fun x n hf => ((AStore.find_join S₁ S₂ x n).mp hf).2

theorem equal_Le {S₁ S₂ : AStore} (h : AStore.equal S₁ S₂ = true) : Le S₁ S₂ :=
  fun x n hf => by rw [AStore.equal_find h x]; exact hf

/-! ## Abstract evaluation of expressions

`Aeval S a` returns `some v` when the value of `a` can be determined from what
`S` knows, and `none` otherwise. -/

def Aeval (S : AStore) : aexp → Option Int
  | .const n => some n
  | .var x => S.find x
  | .plus a₁ a₂ =>
      match Aeval S a₁, Aeval S a₂ with
      | some n₁, some n₂ => some (n₁ + n₂)
      | _, _ => none
  | .minus a₁ a₂ =>
      match Aeval S a₁, Aeval S a₂ with
      | some n₁, some n₂ => some (n₁ - n₂)
      | _, _ => none

def Beval (S : AStore) : bexp → Option Bool
  | .true => some Bool.true
  | .false => some Bool.false
  | .equal a₁ a₂ =>
      match Aeval S a₁, Aeval S a₂ with
      | some n₁, some n₂ => some (n₁ == n₂)
      | _, _ => none
  | .lessequal a₁ a₂ =>
      match Aeval S a₁, Aeval S a₂ with
      | some n₁, some n₂ => some (decide (n₁ ≤ n₂))
      | _, _ => none
  | .not b₁ => (Beval S b₁).map (! ·)
  | .and b₁ b₂ =>
      match Beval S b₁, Beval S b₂ with
      | some v₁, some v₂ => some (v₁ && v₂)
      | _, _ => none

theorem Aeval_sound {s : Store} {S : AStore} (hm : Matches s S) :
    ∀ (a : aexp) {n : Int}, Aeval S a = some n → aeval s a = n
  | .const m, n, h => by simp only [Aeval, Option.some.injEq] at h; simp [aeval, h]
  | .var x, n, h => hm x n h
  | .plus a₁ a₂, n, h => by
      simp only [Aeval] at h
      cases h₁ : Aeval S a₁ with
      | none => rw [h₁] at h; simp at h
      | some n₁ =>
          cases h₂ : Aeval S a₂ with
          | none => rw [h₁, h₂] at h; simp at h
          | some n₂ =>
              rw [h₁, h₂] at h; simp at h
              simp [aeval, Aeval_sound hm a₁ h₁, Aeval_sound hm a₂ h₂, ← h]
  | .minus a₁ a₂, n, h => by
      simp only [Aeval] at h
      cases h₁ : Aeval S a₁ with
      | none => rw [h₁] at h; simp at h
      | some n₁ =>
          cases h₂ : Aeval S a₂ with
          | none => rw [h₁, h₂] at h; simp at h
          | some n₂ =>
              rw [h₁, h₂] at h; simp at h
              simp [aeval, Aeval_sound hm a₁ h₁, Aeval_sound hm a₂ h₂, ← h]

theorem Beval_sound {s : Store} {S : AStore} (hm : Matches s S) :
    ∀ (b : bexp) {v : Bool}, Beval S b = some v → beval s b = v
  | .true, v, h => by simp only [Beval, Option.some.injEq] at h; simp [beval, h]
  | .false, v, h => by simp only [Beval, Option.some.injEq] at h; simp [beval, h]
  | .equal a₁ a₂, v, h => by
      simp only [Beval] at h
      cases h₁ : Aeval S a₁ with
      | none => rw [h₁] at h; simp at h
      | some n₁ =>
          cases h₂ : Aeval S a₂ with
          | none => rw [h₁, h₂] at h; simp at h
          | some n₂ =>
              rw [h₁, h₂] at h; simp at h
              simp [beval, Aeval_sound hm a₁ h₁, Aeval_sound hm a₂ h₂, ← h]
  | .lessequal a₁ a₂, v, h => by
      simp only [Beval] at h
      cases h₁ : Aeval S a₁ with
      | none => rw [h₁] at h; simp at h
      | some n₁ =>
          cases h₂ : Aeval S a₂ with
          | none => rw [h₁, h₂] at h; simp at h
          | some n₂ =>
              rw [h₁, h₂] at h; simp at h
              simp [beval, Aeval_sound hm a₁ h₁, Aeval_sound hm a₂ h₂, ← h]
  | .not b₁, v, h => by
      simp only [Beval] at h
      cases h₁ : Beval S b₁ with
      | none => rw [h₁] at h; simp at h
      | some v₁ =>
          rw [h₁] at h; simp at h
          simp [beval, Beval_sound hm b₁ h₁, ← h]
  | .and b₁ b₂, v, h => by
      simp only [Beval] at h
      cases h₁ : Beval S b₁ with
      | none => rw [h₁] at h; simp at h
      | some v₁ =>
          cases h₂ : Beval S b₂ with
          | none => rw [h₁, h₂] at h; simp at h
          | some v₂ =>
              rw [h₁, h₂] at h; simp at h
              simp [beval, Beval_sound hm b₁ h₁, Beval_sound hm b₂ h₂, ← h]

theorem Matches.update {s : Store} {S : AStore} {x : Ident} {n : Int} {N : Option Int}
    (hm : Matches s S) (hN : ∀ i, N = some i → n = i) :
    Matches (IMP.update x n s) (AStore.update x N S) := by
  intro y m hf
  rw [AStore.find_update] at hf
  by_cases hyx : y = x
  · subst hyx; simp only [if_true] at hf
    simp [IMP.update, hN m hf]
  · simp only [hyx, if_false] at hf
    simp [IMP.update, hyx, hm y m hf]

/-! ## The analysis

To analyse a loop we must find a fixpoint of a function from abstract stores
to abstract stores — intuitively, running the loop "in the abstract" until the
abstract state stops changing.  Guaranteeing termination of that search takes
real work; see `Fixpoints.lean`.  For now we use the engineer's answer: iterate
a fixed number of times and fall back to `top` (know nothing) if no fixpoint
has appeared.  That is sound, if imprecise, which is all the correctness proof
needs. -/

def fixpointRec (F : AStore → AStore) : Nat → AStore → AStore
  | 0, _ => AStore.top
  | fuel + 1, S => if AStore.equal (F S) S then S else fixpointRec F fuel (F S)

def numIter : Nat := 20

def fixpoint (F : AStore → AStore) (initS : AStore) : AStore := fixpointRec F numIter initS

/-- Whatever `fixpoint` returns is a post-fixpoint: `F S ≤ S`.  That is the
only property the soundness proof uses. -/
theorem fixpoint_sound (F : AStore → AStore) (initS : AStore) :
    Le (F (fixpoint F initS)) (fixpoint F initS) := by
  have key : ∀ (fuel : Nat) (S : AStore),
      fixpointRec F fuel S = AStore.top
      ∨ AStore.equal (F (fixpointRec F fuel S)) (fixpointRec F fuel S) = true := by
    intro fuel
    induction fuel with
    | zero => intro S; exact .inl rfl
    | succ fuel ih =>
        intro S
        by_cases h : AStore.equal (F S) S = true
        · simp only [fixpointRec, if_pos h]; exact .inr h
        · simp only [fixpointRec, if_neg h]; exact ih (F S)
  rcases key numIter initS with h | h
  · rw [fixpoint, h]; exact Le_top _
  · exact equal_Le h

/-- Abstract execution of a command: given what is known before `c`, compute
what is known after it. -/
def Cexec (S : AStore) (c : com) : AStore :=
  match c with
  | .skip => S
  | .assign x a => AStore.update x (Aeval S a) S
  | .seq c₁ c₂ => Cexec (Cexec S c₁) c₂
  | .ifthenelse b c₁ c₂ =>
      match Beval S b with
      | some Bool.true => Cexec S c₁
      | some Bool.false => Cexec S c₂
      | none => AStore.join (Cexec S c₁) (Cexec S c₂)
  | .while _ c₁ => fixpoint (fun X => AStore.join S (Cexec X c₁)) S

/-- Soundness of the analysis: if the concrete store before `c` is described
by `S`, then the concrete store after `c` is described by `Cexec S c`. -/
theorem Cexec_sound : ∀ (c : com) {s₁ s₂ : Store} {S₁ : AStore},
    cexec s₁ c s₂ → Matches s₁ S₁ → Matches s₂ (Cexec S₁ c)
  | .skip, s₁, s₂, S₁, hexec, hm => by cases hexec; exact hm
  | .assign x a, s₁, s₂, S₁, hexec, hm => by
      cases hexec
      exact hm.update (fun i hi => Aeval_sound hm a hi)
  | .seq c₁ c₂, s₁, s₂, S₁, hexec, hm => by
      cases hexec with
      | seq h₁ h₂ => exact Cexec_sound c₂ h₂ (Cexec_sound c₁ h₁ hm)
  | .ifthenelse b c₁ c₂, s₁, s₂, S₁, hexec, hm => by
      cases hexec with
      | ifthenelse h =>
          simp only [Cexec]
          cases hb : Beval S₁ b with
          | some v =>
              cases v
              · rw [Beval_sound hm b hb] at h
                simpa using Cexec_sound c₂ (by simpa using h) hm
              · rw [Beval_sound hm b hb] at h
                simpa using Cexec_sound c₁ (by simpa using h) hm
          | none =>
              simp only []
              cases hbv : beval s₁ b
              · rw [hbv] at h
                exact Matches.mono (Le_join_right _ _) (Cexec_sound c₂ (by simpa using h) hm)
              · rw [hbv] at h
                exact Matches.mono (Le_join_left _ _) (Cexec_sound c₁ (by simpa using h) hm)
  | .while b c, s₁, s₂, S₁, hexec, hm => by
      -- The analysis of a loop is a fixpoint, so the proof needs an inner
      -- induction on the number of iterations actually performed.
      have hpost : Le (AStore.join S₁ (Cexec (Cexec S₁ (.while b c)) c))
          (Cexec S₁ (.while b c)) := fixpoint_sound _ _
      have inner : ∀ {t₁ : Store} {c' : com} {t₂ : Store}, cexec t₁ c' t₂ →
          c' = com.while b c → Matches t₁ (Cexec S₁ (.while b c)) →
          Matches t₂ (Cexec S₁ (.while b c)) := by
        intro t₁ c' t₂ h
        induction h with
        | skip => intro he; cases he
        | assign => intro he; cases he
        | seq _ _ _ _ => intro he; cases he
        | ifthenelse _ _ => intro he; cases he
        | while_done _ => intro _ hm'; exact hm'
        | @while_loop b' c'' t₁ t' t₂ hb h₁ _ _ ih₂ =>
            intro he hm'
            cases he
            refine ih₂ rfl ?_
            exact Matches.mono hpost (Matches.mono (Le_join_right _ _)
              (Cexec_sound c h₁ hm'))
      exact inner hexec rfl (Matches.mono hpost (Matches.mono (Le_join_left _ _) hm))

/-! ## The optimisation

Now we use the analysis: replace each variable of known value by that value,
and simplify with the smart constructors. -/

def cpAexp (S : AStore) : aexp → aexp
  | .const n => .const n
  | .var x => match S.find x with | some n => .const n | none => .var x
  | .plus a₁ a₂ => mkPlus (cpAexp S a₁) (cpAexp S a₂)
  | .minus a₁ a₂ => mkMinus (cpAexp S a₁) (cpAexp S a₂)

def cpBexp (S : AStore) : bexp → bexp
  | .true => .true
  | .false => .false
  | .equal a₁ a₂ => mkEqual (cpAexp S a₁) (cpAexp S a₂)
  | .lessequal a₁ a₂ => mkLessequal (cpAexp S a₁) (cpAexp S a₂)
  | .not b => mkNot (cpBexp S b)
  | .and b₁ b₂ => mkAnd (cpBexp S b₁) (cpBexp S b₂)

theorem cpAexp_sound {s : Store} {S : AStore} (hm : Matches s S) :
    ∀ a : aexp, aeval s (cpAexp S a) = aeval s a
  | .const _ => rfl
  | .var x => by
      simp only [cpAexp]
      cases hf : S.find x with
      | none => rfl
      | some n => simp [aeval, hm x n hf]
  | .plus a₁ a₂ => by
      simp [cpAexp, mkPlus_sound, cpAexp_sound hm a₁, cpAexp_sound hm a₂, aeval]
  | .minus a₁ a₂ => by
      simp [cpAexp, mkMinus_sound, cpAexp_sound hm a₁, cpAexp_sound hm a₂, aeval]

theorem cpBexp_sound {s : Store} {S : AStore} (hm : Matches s S) :
    ∀ b : bexp, beval s (cpBexp S b) = beval s b
  | .true => rfl
  | .false => rfl
  | .equal a₁ a₂ => by
      simp [cpBexp, mkEqual_sound, cpAexp_sound hm a₁, cpAexp_sound hm a₂, beval]
  | .lessequal a₁ a₂ => by
      simp [cpBexp, mkLessequal_sound, cpAexp_sound hm a₁, cpAexp_sound hm a₂, beval]
  | .not b => by simp [cpBexp, mkNot_sound, cpBexp_sound hm b, beval]
  | .and b₁ b₂ => by
      simp [cpBexp, mkAnd_sound, cpBexp_sound hm b₁, cpBexp_sound hm b₂, beval]

/-- Optimising a command.  The parameter `S` is what is known *before* `c`, so
it must be updated exactly as the analysis updates it: the second half of a
sequence is optimised under `Cexec S c₁`, and the body of a loop under the
loop's own fixpoint. -/
def cpCom (S : AStore) (c : com) : com :=
  match c with
  | .skip => .skip
  | .assign x a => .assign x (cpAexp S a)
  | .seq c₁ c₂ => .seq (cpCom S c₁) (cpCom (Cexec S c₁) c₂)
  | .ifthenelse b c₁ c₂ => mkIfthenelse (cpBexp S b) (cpCom S c₁) (cpCom S c₂)
  | .while b c₁ =>
      let sfix := Cexec S (.while b c₁)
      mkWhile (cpBexp sfix b) (cpCom sfix c₁)

/-- Optimising Euclidean division under the (dubious) assumption that the
divisor is `0`: the test `b ≤ r` becomes `0 ≤ r` and `r := r - b` becomes
`r := r`. -/
example : cpCom (AStore.update "b" (some 0) AStore.top) euclideanDivision
    = (.assign "r" (.var "a") ;; .assign "q" (.const 0) ;;
       .while (.lessequal (.const 0) (.var "r"))
         (.assign "r" (.var "r") ;; .assign "q" (.plus (.var "q") (.const 1)))) := by
  native_decide

/-- Semantic preservation for terminating programs.  The induction pattern is
unusual: structural induction on `c`, with an inner induction on the number of
iterations when `c` is a loop.  It mirrors the structure of `Cexec` itself —
structural recursion plus a local fixpoint for loops. -/
theorem cpCom_correct_terminating : ∀ (c : com) {s₁ s₂ : Store} {S₁ : AStore},
    cexec s₁ c s₂ → Matches s₁ S₁ → cexec s₁ (cpCom S₁ c) s₂
  | .skip, s₁, s₂, S₁, hexec, _ => by cases hexec; exact .skip _
  | .assign x a, s₁, s₂, S₁, hexec, hm => by
      cases hexec
      have := cexec.assign s₁ x (cpAexp S₁ a)
      rwa [cpAexp_sound hm a] at this
  | .seq c₁ c₂, s₁, s₂, S₁, hexec, hm => by
      cases hexec with
      | seq h₁ h₂ =>
          exact .seq (cpCom_correct_terminating c₁ h₁ hm)
            (cpCom_correct_terminating c₂ h₂ (Cexec_sound c₁ h₁ hm))
  | .ifthenelse b c₁ c₂, s₁, s₂, S₁, hexec, hm => by
      cases hexec with
      | ifthenelse h =>
          refine cexec_mkIfthenelse ?_
          rw [cpBexp_sound hm b]
          cases hb : beval s₁ b
          · rw [hb] at h; simpa using cpCom_correct_terminating c₂ (by simpa using h) hm
          · rw [hb] at h; simpa using cpCom_correct_terminating c₁ (by simpa using h) hm
  | .while b c, s₁, s₂, S₁, hexec, hm => by
      have hpost : Le (AStore.join S₁ (Cexec (Cexec S₁ (.while b c)) c))
          (Cexec S₁ (.while b c)) := fixpoint_sound _ _
      have inner : ∀ {t₁ : Store} {c' : com} {t₂ : Store}, cexec t₁ c' t₂ →
          c' = com.while b c → Matches t₁ (Cexec S₁ (.while b c)) →
          cexec t₁ (mkWhile (cpBexp (Cexec S₁ (.while b c)) b)
            (cpCom (Cexec S₁ (.while b c)) c)) t₂ := by
        intro t₁ c' t₂ h
        induction h with
        | skip => intro he; cases he
        | assign => intro he; cases he
        | seq _ _ _ _ => intro he; cases he
        | ifthenelse _ _ => intro he; cases he
        | @while_done _b' c'' t hb =>
            intro he hm'
            cases he
            exact cexec_mkWhile_done (by rw [cpBexp_sound hm' b]; exact hb)
        | @while_loop b' c'' t₁ t' t₂ hb h₁ _ _ ih₂ =>
            intro he hm'
            cases he
            refine cexec_mkWhile_loop (by rw [cpBexp_sound hm' b]; exact hb)
              (cpCom_correct_terminating c h₁ hm') (ih₂ rfl ?_)
            exact Matches.mono hpost (Matches.mono (Le_join_right _ _)
              (Cexec_sound c h₁ hm'))
      exact inner hexec rfl (Matches.mono hpost (Matches.mono (Le_join_left _ _) hm))

end Constprop
