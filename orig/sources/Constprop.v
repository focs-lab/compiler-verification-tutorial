From Coq Require Import Arith ZArith Psatz Bool String List FMaps Recdef Program.Equality.
Require Import Sequences IMP.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * 8. An optimization: constant propagation *)

(** ** 8.1 Simplifying expressions using smart constructors *)

(** [mk_PLUS_CONST a n] produces an expression equivalent to [PLUS a (CONST n)]
  but further simplified.  *)

Function mk_PLUS_CONST (a: aexp) (n: Z) : aexp :=
  if n =? 0 then a else
  match a with
  | CONST m => CONST (m + n)
  | PLUS a (CONST m) => PLUS a (CONST (m + n))
  | _ => PLUS a (CONST n)
  end.

(** We use [Function] instead of [Definition] because [Function] produces
  a nicer case analysis principle, with exactly one case per line
  of the matching.  This simplifies the proofs of correctness. *)

(** [mk_PLUS a1 a2] produces a simplified expression equivalent to [PLUS a1 a2].
  It uses associativity and commutativity to find the pattern
  "an expression plus a constant", then uses [mk_PLUS_CONST] to simplify
  further. *)

Function mk_PLUS (a1 a2: aexp) : aexp :=
  match a1, a2 with
  | CONST m, _ => mk_PLUS_CONST a2 m
  | _, CONST m => mk_PLUS_CONST a1 m
  | PLUS a1 (CONST m1), PLUS a2 (CONST m2) => mk_PLUS_CONST (PLUS a1 a2) (m1 + m2)
  | PLUS a1 (CONST m1), _ => mk_PLUS_CONST (PLUS a1 a2) m1
  | _, PLUS a2 (CONST m2) => mk_PLUS_CONST (PLUS a1 a2) m2
  | _, _ => PLUS a1 a2
  end.

(** [mk_MINUS a1 a2] produces an expression equivalent to [MINUS a1 a2]
  using similar tricks.  Note that "expression minus constant" is
  always normalized into "expression plus opposite constant",
  simplifying the case analyses. *)

Function mk_MINUS (a1 a2: aexp) : aexp :=
  match a1, a2 with
  | _, CONST m => mk_PLUS_CONST a1 (-m)
  | PLUS a1 (CONST m1), PLUS a2 (CONST m2) => mk_PLUS_CONST (MINUS a1 a2) (m1 - m2)
  | PLUS a1 (CONST m1), _ => mk_PLUS_CONST (MINUS a1 a2) m1
  | _, PLUS a2 (CONST m2) => mk_PLUS_CONST (MINUS a1 a2) (-m2)
  | _, _ => MINUS a1 a2
  end.

(** To simplify an expression, we rewrite it bottom-up, applying the smart
  constructors at each step. *)

Fixpoint simplif_aexp (a: aexp) : aexp :=
  match a with
  | CONST n => CONST n
  | VAR x => VAR x
  | PLUS a1 a2 => mk_PLUS (simplif_aexp a1) (simplif_aexp a2)
  | MINUS a1 a2 => mk_MINUS (simplif_aexp a1) (simplif_aexp a2)
  end.

(** An example: *)

Compute (simplif_aexp (MINUS (PLUS (VAR "x") (CONST 1)) (PLUS (VAR "y") (CONST 1)))).

(** Result is: [MINUS (VAR "x") (VAR "y")]. *)

(** To show the soundness of these simplifications, we show that the
  optimized expressions evaluate to the same values as the original expressions. *)

Lemma mk_PLUS_CONST_sound:
  forall s a n, aeval s (mk_PLUS_CONST a n) = aeval s a + n.
Proof.
  intros. functional induction (mk_PLUS_CONST a n).
- assert (n = 0) by (apply Z.eqb_eq; auto). 
  lia.
- auto.
- cbn. lia.
- auto.
Qed.

Lemma mk_PLUS_sound:
  forall s a1 a2, aeval s (mk_PLUS a1 a2) = aeval s a1 + aeval s a2.
Proof.
  intros. functional induction (mk_PLUS a1 a2); rewrite ? mk_PLUS_CONST_sound; cbn; lia.
Qed.

Lemma mk_MINUS_sound:
  forall s a1 a2, aeval s (mk_MINUS a1 a2) = aeval s a1 - aeval s a2.
Proof.
  intros. functional induction (mk_MINUS a1 a2); rewrite ? mk_PLUS_CONST_sound; cbn; lia.
Qed.

Lemma simplif_aexp_sound:
  forall s a, aeval s (simplif_aexp a) = aeval s a.
Proof.
  induction a; cbn. 
- auto.
- auto.
- rewrite mk_PLUS_sound, IHa1, IHa2. auto.
- rewrite mk_MINUS_sound, IHa1, IHa2. auto.
Qed.

(** We can play the same game for Boolean expressions.
  Here are the smart constructors and their proofs of correctness. *)

Function mk_EQUAL (a1 a2: aexp) : bexp :=
  match a1, a2 with
  | CONST n1, CONST n2 => if n1 =? n2 then TRUE else FALSE
  | PLUS a1 (CONST n1), CONST n2 => EQUAL a1 (CONST (n2 - n1))
  | _, _ => EQUAL a1 a2
  end.

Function mk_LESSEQUAL (a1 a2: aexp) : bexp :=
  match a1, a2 with
  | CONST n1, CONST n2 => if n1 <=? n2 then TRUE else FALSE
  | PLUS a1 (CONST n1), CONST n2 => LESSEQUAL a1 (CONST (n2 - n1))
  | _, _ => LESSEQUAL a1 a2
  end.

Function mk_NOT (b: bexp) : bexp :=
  match b with
  | TRUE => FALSE
  | FALSE => TRUE
  | NOT b => b
  | _ => NOT b
  end.

Function mk_AND (b1 b2: bexp) : bexp :=
  match b1, b2 with
  | TRUE, _ => b2
  | _, TRUE => b1
  | FALSE, _ => FALSE
  | _, FALSE => FALSE
  | _, _ => AND b1 b2
  end.

Lemma mk_EQUAL_sound:
  forall s a1 a2, beval s (mk_EQUAL a1 a2) = (aeval s a1 =? aeval s a2).
Proof.
  intros. functional induction (mk_EQUAL a1 a2); cbn.
- auto.
- auto.
- destruct (Z.eqb_spec (aeval s a0) (n2 - n1));
  destruct (Z.eqb_spec (aeval s a0 + n1) n2);
  auto; lia.
- auto.
Qed.

Lemma mk_LESSEQUAL_sound:
  forall s a1 a2, beval s (mk_LESSEQUAL a1 a2) = (aeval s a1 <=? aeval s a2).
Proof.
  intros. functional induction (mk_LESSEQUAL a1 a2); cbn.
- auto.
- auto.
- destruct (Z.leb_spec (aeval s a0) (n2 - n1));
  destruct (Z.leb_spec (aeval s a0 + n1) n2);
  auto; lia.
- auto.
Qed.

Lemma mk_NOT_sound:
  forall s b, beval s (mk_NOT b) = negb (beval s b).
Proof.
  intros. functional induction (mk_NOT b); cbn.
- auto.
- auto.
- rewrite negb_involutive. auto.
- auto.
Qed.

Lemma mk_AND_sound:
  forall s b1 b2, beval s (mk_AND b1 b2) = beval s b1 && beval s b2.
Proof.
  intros. functional induction (mk_AND b1 b2); cbn.
- auto.
- rewrite andb_true_r; auto.
- auto.
- rewrite andb_false_r; auto.
- auto.
Qed.

(** *** Exercise (2 stars, recommended) *)

(** Write a simplification function for Boolean expressions and prove its soundness. *)

Fixpoint simplif_bexp (b: bexp) : bexp :=
  (* FILL IN HERE *)
  b.

Lemma simplif_bexp_sound:
  forall s b, beval s (simplif_bexp b) = beval s b.
Proof.
  (* FILL IN HERE *)
Abort.

(** *** Exercise (2-3 stars, optional) *)

(** Can you think of other algebraic simplifications on arithmetic and
  Boolean expressions that would be beneficial?  By this, I mean that
  the compiler would produce shorter code for the simplified expression.
  Try to add them to the smart constructors and update their proofs
  accordingly. *)

(** Even commands can benefit from smart constructors!  Here is a smart
   IFTHENELSE and a smart WHILE that take known conditions into account. *)

Function mk_IFTHENELSE (b: bexp) (c1 c2: com) : com :=
  match b with
  | TRUE => c1
  | FALSE => c2
  | _ => IFTHENELSE b c1 c2
  end.

Function mk_WHILE (b: bexp) (c: com) : com :=
  match b with
  | FALSE => SKIP
  | _ => WHILE b c
  end.

Lemma cexec_mk_IFTHENELSE: forall s1 b c1 c2 s2,
  cexec s1 (if beval s1 b then c1 else c2) s2 ->
  cexec s1 (mk_IFTHENELSE b c1 c2) s2.
Proof.
  intros. functional induction (mk_IFTHENELSE b c1 c2).
- auto.
- auto.
- apply cexec_ifthenelse; auto.
Qed.

Lemma cexec_mk_WHILE_done: forall s1 b c,
  beval s1 b = false ->
  cexec s1 (mk_WHILE b c) s1.
Proof.
  intros. functional induction (mk_WHILE b c). 
- apply cexec_skip.
- apply cexec_while_done. auto.
Qed.

Lemma cexec_mk_WHILE_loop: forall b c s1 s2 s3,
  beval s1 b = true -> cexec s1 c s2 -> cexec s2 (mk_WHILE b c) s3 ->
  cexec s1 (mk_WHILE b c) s3.
Proof.
  intros. functional induction (mk_WHILE b c).
- discriminate.
- apply cexec_while_loop with s2; auto.
Qed.

(** ** 8.2 A static analysis for constant propagation *)

Require Import FMaps.

(** The static analysis we need operates over finite maps from variables (strings)
  to values (integers).  Coq's standard library provides a rich, efficient
  implementation of finite sets and finite maps.  Before being able to use it, however,
  we must provide it with a Coq module equipping the type of strings
  with a decidable equality.  The implementation of this module follows. *)

Module Ident_Decidable <: DecidableType with Definition t := ident.
  Definition t := ident.
  Definition eq (x y: t) := x = y.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End Ident_Decidable.

(** We then instantiate the finite maps modules from Coq's standard library
  with strings as the type of keys. *)

Module IdentMap := FMapWeakList.Make(Ident_Decidable).
Module IMFact := FMapFacts.WFacts(IdentMap).
Module IMProp := FMapFacts.WProperties(IdentMap).

(** Our static analysis is going to compute "abstract stores", that is,
  compile-time approximations of run-time stores.  This is an instance
  of the general theory of abstract interpretation.

  (Notational convention: we use Capitalized identifiers to refer to
  abstract things and lowercase identifiers to refer to concrete things.)

  Abstract stores [Store] are represented as finite maps from variable names
  to integers.  If a variable [x] is mapped to [n], it means that
  we statically know that the run-time value of [x] is [n].  If [x] is not mapped,
  it means that the run-time value of [x] can be anything.

  This meaning is captured by the [matches s s'] predicate below,
  which says whether a concrete store [s] belongs to an
  abstract store [s'] obtained by static analysis.
  (A bit like a term belongs to a type in a type system.)
*)

Definition Store := IdentMap.t Z.

Definition matches (s: store) (S: Store): Prop :=
  forall x n, IdentMap.find x S = Some n -> s x = n.

(** Abstract stores have a lattice structure, with an order [Le], a top element,
  and a join operation.  We can also test whether two abstract stores are equal. *)

Definition Le (S1 S2: Store) : Prop :=
  forall x n, IdentMap.find x S2 = Some n -> IdentMap.find x S1 = Some n.
  
Definition Top : Store := IdentMap.empty Z.

Definition Join_aux (N1 N2: option Z): option Z :=
  match N1, N2 with
  | Some n1, Some n2 => if n1 =? n2 then Some n1 else None
  | _, _ => None
  end.

Definition Join (S1 S2: Store) : Store :=
  IdentMap.map2 Join_aux S1 S2.

Definition Equal (S1 S2: Store) : bool :=
  IdentMap.equal Z.eqb S1 S2.

(** We show the soundness of these lattice operations with respect to
  the [matches] and the [Le] relations. *)

Lemma matches_Le: forall s S1 S2, Le S1 S2 -> matches s S1 -> matches s S2.
Proof.
  unfold matches, Le; intros; auto.
Qed.

Lemma Le_Top: forall S, Le S Top.
Proof.
  unfold Le, Top; intros. rewrite IMFact.empty_o in H. discriminate.
Qed.

Lemma Join_characterization:
  forall S1 S2 x n,
  IdentMap.find x (Join S1 S2) = Some n <->
  IdentMap.find x S1 = Some n /\ IdentMap.find x S2 = Some n.
Proof.
  unfold Join; intros. rewrite IMFact.map2_1bis by auto. 
  unfold Join_aux. split.
- intros.
  destruct (IdentMap.find x S1) as [n1|]; try discriminate.
  destruct (IdentMap.find x S2) as [n2|]; try discriminate.
  destruct (n1 =? n2) eqn:E; try discriminate.
  assert (n1 = n2) by (apply Z.eqb_eq; auto).
  split; congruence.
- intros [FIND1 FIND2]. rewrite FIND1, FIND2. rewrite Z.eqb_refl. auto.
Qed.

Lemma Le_Join_l: forall S1 S2, Le S1 (Join S1 S2).
Proof.
  unfold Le; intros. rewrite Join_characterization in H. tauto.
Qed.

Lemma Le_Join_r: forall S1 S2, Le S2 (Join S1 S2).
Proof.
  unfold Le; intros. rewrite Join_characterization in H. tauto.
Qed.

Lemma Equal_Le: forall S1 S2, Equal S1 S2 = true -> Le S1 S2.
Proof.
  unfold Le, Equal; intros.
  assert (E: IdentMap.Equal S1 S2).
  { apply <- IMFact.Equal_Equivb. apply IdentMap.equal_2. eauto. apply Z.eqb_eq. }
  rewrite E. auto.
Qed. 

(** The abstract, compile-time evaluation of expressions returns [Some v]
  if the value [v] of the expression can be determined based on what
  the abstract store [S] tells us about the values of variables.
  Otherwise, [None] is returned. *)

Definition lift1 {A B: Type} (f: A -> B) (o: option A) : option B :=
  match o with Some x => Some (f x) | None => None end.

Definition lift2 {A B C: Type} (f: A -> B -> C) (o1: option A) (o2: option B) : option C :=
  match o1, o2 with Some x1, Some x2 => Some (f x1 x2) | _, _ => None end.

Fixpoint Aeval (S: Store) (a: aexp) : option Z :=
  match a with
  | CONST n => Some n
  | VAR x => IdentMap.find x S
  | PLUS a1 a2 => lift2 Z.add (Aeval S a1) (Aeval S a2)
  | MINUS a1 a2 => lift2 Z.sub (Aeval S a1) (Aeval S a2)
  end.

Fixpoint Beval (S: Store) (b: bexp) : option bool :=
  match b with
  | TRUE => Some true
  | FALSE => Some false
  | EQUAL a1 a2 => lift2 Z.eqb (Aeval S a1) (Aeval S a2)
  | LESSEQUAL a1 a2 => lift2 Z.leb (Aeval S a1) (Aeval S a2)
  | NOT b1 => lift1 negb (Beval S b1)
  | AND b1 b2 => lift2 andb (Beval S b1) (Beval S b2)
  end.

(** These compile-time evaluations are sound, in the following sense. *)

Lemma Aeval_sound:
  forall s S, matches s S ->
  forall a n, Aeval S a = Some n -> aeval s a = n.
Proof.
  intros s S AG; induction a; cbn; intros.
- congruence.
- apply AG; auto.
- destruct (Aeval S a1) as [n1|]; destruct (Aeval S a2) as [n2|]; try discriminate.
  cbn in H; inversion H. f_equal; auto.
- destruct (Aeval S a1) as [n1|]; destruct (Aeval S a2) as [n2|]; try discriminate.
  cbn in H; inversion H. f_equal; auto.
Qed.

Lemma Beval_sound:
  forall s S, matches s S ->
  forall b n, Beval S b = Some n -> beval s b = n.
Proof.
  intros s S AG; induction b; cbn; intros.
- congruence.
- congruence.
- destruct (Aeval S a1) as [n1|] eqn:A1;
  destruct (Aeval S a2) as [n2|] eqn:A2; try discriminate.
  cbn in H; inversion H. erewrite ! Aeval_sound by eauto. auto.
- destruct (Aeval S a1) as [n1|] eqn:A1;
  destruct (Aeval S a2) as [n2|] eqn:A2; try discriminate.
  cbn in H; inversion H. erewrite ! Aeval_sound by eauto. auto.
- destruct (Beval S b) as [n1|]; cbn in H; inversion H.
  f_equal; auto.
- destruct (Beval S b1) as [n1|]; destruct (Beval S b2) as [n2|]; try discriminate.
  cbn in H; inversion H. f_equal; auto.
Qed.

(** To analyze assignments, we need to update abstract stores with the result
  of [Aeval]. *)

Definition Update (x: ident) (N: option Z) (S: Store) : Store :=
  match N with
  | None => IdentMap.remove x S
  | Some n => IdentMap.add x n S
  end.

Lemma Update_characterization:
  forall S x N y,
  IdentMap.find y (Update x N S) = if string_dec x y then N else IdentMap.find y S.
Proof.
  intros. unfold Update. destruct N as [n|].
- apply IMFact.add_o.
- apply IMFact.remove_o.
Qed.
 
Lemma matches_update: forall s S x n N,
  matches s S -> 
  (forall i, N = Some i -> n = i) ->
  matches (update x n s) (Update x N S).
Proof.
  intros. unfold update, matches. intros x1 n1 FIND1.
  rewrite Update_characterization in FIND1. 
  destruct (string_dec x x1); auto.
Qed.

(** To analyze loops, we will need to find fixpoints of a function from
  abstract states to abstract states.  Intuitively, this corresponds
  to executing the loop in the abstract, stopping iterations when the
  abstract state is stable.

  Computing exact fixpoints with guaranteed termination is not easy;
  we will return to this question at the end of the lectures.
  In the meantime, we will use the simple, approximate algorithm below,
  which stops after a fixed number of iterations and returns [Top]
  if no fixpoint has been found earlier. *)

Fixpoint fixpoint_rec (F: Store -> Store) (fuel: nat) (S: Store) : Store :=
  match fuel with
  | O => Top
  | S fuel =>
      let S' := F S in
      if Equal S' S then S else fixpoint_rec F fuel S'
  end.

(** Let's say that we will do at most 20 iterations. *)

Definition num_iter := 20%nat.

Definition fixpoint (F: Store -> Store) (init_S: Store) : Store :=
  fixpoint_rec F num_iter init_S.

(** The result [S] of [fixpoint F] is sound, in that it satisfies
    [F S <= S] in the lattice ordering. *)

Lemma fixpoint_sound: forall F init_S,
  let S := fixpoint F init_S in Le (F S) S.
Proof.
  intros F.
  assert (A: forall fuel S,
             fixpoint_rec F fuel S = Top
             \/ Equal (F (fixpoint_rec F fuel S)) (fixpoint_rec F fuel S) = true).
  { induction fuel as [ | fuel]; cbn; intros.
  - auto.
  - destruct (Equal (F S) S) eqn:E. 
    + auto.
    + apply IHfuel.
  }
  intros. 
  assert (E: S = Top \/ Equal (F S) S = true) by apply A.
  destruct E as [E | E].
  - rewrite E.  apply Le_Top.
  - apply Equal_Le; auto.
Qed.

(** Now we can analyze commands by executing them "in the abstract".
  Given an abstract store [S] that represents what we statically know
  about the values of the variables before executing command [c],
  [cexec'] returns an abstract store that describes the values of
  the variables after executing [c]. *)

Fixpoint Cexec (S: Store) (c: com) : Store :=
  match c with
  | SKIP => S
  | ASSIGN x a => Update x (Aeval S a) S
  | SEQ c1 c2 => Cexec (Cexec S c1) c2
  | IFTHENELSE b c1 c2 =>
      match Beval S b with
      | Some true => Cexec S c1
      | Some false => Cexec S c2
      | None => Join (Cexec S c1) (Cexec S c2)
      end
  | WHILE b c1 =>
      fixpoint (fun x => Join S (Cexec x c1)) S
  end.

(** The soundness of the analysis follows. *)

Ltac inv H := inversion H; clear H; subst.

Lemma Cexec_sound:
  forall c s1 s2 S1,
  cexec s1 c s2 -> matches s1 S1 -> matches s2 (Cexec S1 c).
Proof.
  induction c; intros s1 s2 S1 EXEC AG; cbn [Cexec].
- (* SKIP *)
  inv EXEC. auto.
- (* ASSIGN *)
  inv EXEC. apply matches_update. auto. apply Aeval_sound. auto.
- (* SEQ *)
  inv EXEC. apply IHc2 with s'; auto. apply IHc1 with s1; auto.
- (* IFTHENELSE *)
  inv EXEC.
  destruct (Beval S1 b) as [[]|] eqn:BE.
  + erewrite Beval_sound in H4 by eauto. apply IHc1 with s1; auto.
  + erewrite Beval_sound in H4 by eauto. apply IHc2 with s1; auto.
  + destruct (beval s1 b).
    * eapply matches_Le. apply Le_Join_l. eapply IHc1; eauto.
    * eapply matches_Le. apply Le_Join_r. eapply IHc2; eauto.
- (* WHILE *)
  set (F := fun x => Join S1 (Cexec x c)).
  set (X := fixpoint F S1).
  assert (INNER: forall s1 c1 s2, 
                 cexec s1 c1 s2 ->
                 c1 = WHILE b c ->
                 matches s1 X ->
                 matches s2 X).
  { induction 1; intros EQ AG1; inv EQ.
  - (* WHILE stop *)
    auto.
  - (* WHILE loop *)
    apply IHcexec2; auto. 
    unfold X. eapply matches_Le. apply fixpoint_sound. 
    unfold F. eapply matches_Le. apply Le_Join_r.
    apply IHc with s. auto. fold F. fold X. auto.
  }
  eapply INNER; eauto. 
  unfold X. eapply matches_Le. apply fixpoint_sound. 
  unfold F. eapply matches_Le. apply Le_Join_l.
  auto.
Qed.

(** *** Exercise (3 stars, optional) *)

(** Extend the analysis to take advantage of equality tests against constants.
  For example, in the following program,
<<
   if x = 0
   then y = x + 1
   else y = 1
>>
  we could notice that [x = 0] in the "then" branch, hence [y = 1] at
  the end of both branches.  To this end, write a function
  [Binvert S b] that returns a pair of abstract stores [S1, S0],
  where [S1] is [S] enriched from equalities that hold when [b]
  evaluates to [true], and [S0] is [S] enriched from equalities that
  hold when [b] evaluates to [false].  Then use [Binvert] to refine
  the analysis of [IFTHENELSE] and [WHILE].
*)

(** *** Exercise (4 stars, optional) *)

(** Modify the static analysis to infer variation intervals instead of
  constant values.  Abstract stores map variables to pairs [(lo,hi)]
  of two integers, meaning that the concrete value of the variable is
  between [lo] and [hi] inclusive:
<<
  Definition matches (s: store) (S: Store) : Prop :=
    forall x lo hi, IdentMap.find x S = Some (lo, hi) -> lo <= s x <= hi.
>>
  (You could also support special values "minus infinity" for [lo]
   and "infinity" for [hi].)
   Adapt the operations over abstract stores and the abstract interpreters
   for expressions and commands accordingly.
*)

(** ** 8.3 The constant propagation optimization *)

(** We can use the results of the static analysis to simplify expressions
  further, replacing variables with known values by these values, then
  applying the smart constructors. *)

Fixpoint cp_aexp (S: Store) (a: aexp) : aexp :=
  match a with
  | CONST n => CONST n
  | VAR x => match IdentMap.find x S with Some n => CONST n | None => VAR x end
  | PLUS a1 a2 => mk_PLUS (cp_aexp S a1) (cp_aexp S a2)
  | MINUS a1 a2 => mk_MINUS (cp_aexp S a1) (cp_aexp S a2)
  end.

Fixpoint cp_bexp (S: Store) (b: bexp) : bexp :=
  match b with
  | TRUE => TRUE
  | FALSE => FALSE
  | EQUAL a1 a2 => mk_EQUAL (cp_aexp S a1) (cp_aexp S a2)
  | LESSEQUAL a1 a2 => mk_LESSEQUAL (cp_aexp S a1) (cp_aexp S a2)
  | NOT b => mk_NOT (cp_bexp S b)
  | AND b1 b2 => mk_AND (cp_bexp S b1) (cp_bexp S b2)
  end.

(** Under the assumption that the concrete store matchess with the abstract store,
  these optimized expressions evaluate to the same values as the original
  expressions. *)

Lemma cp_aexp_sound:
  forall s S, matches s S ->
  forall a, aeval s (cp_aexp S a) = aeval s a.
Proof.
  intros s S AG; induction a; cbn.
- auto.
- destruct (IdentMap.find x S) as [n|] eqn:FIND.
  + symmetry. apply AG. auto.
  + auto.
- rewrite mk_PLUS_sound, IHa1, IHa2. auto.
- rewrite mk_MINUS_sound, IHa1, IHa2. auto.
Qed.

Lemma cp_bexp_sound:
  forall s S, matches s S ->
  forall b, beval s (cp_bexp S b) = beval s b.
Proof.
  intros s S AG; induction b; cbn.
- auto.
- auto.
- rewrite mk_EQUAL_sound, ! cp_aexp_sound by auto. auto.
- rewrite mk_LESSEQUAL_sound, ! cp_aexp_sound by auto. auto.
- rewrite mk_NOT_sound, IHb. auto.
- rewrite mk_AND_sound, IHb1, IHb2. auto.
Qed.

(** The optimization of commands consists in propagating constants
  in expressions and simplifying the expressions, as above.
  In addition, conditionals and loops whose conditions are statically
  known will be simplified too, thanks to the smart constructors.

  The [S] parameter is the abstract store "before" the execution of [c].
  When recursing through [c], it must be updated like the static analysis
  [Cexec] does.  For example, if [c] is [SEQ c1 c2], [c2] is optimized
  using [Cexec S c1] as abstract store "before".  Likewise, if
  [c] is a loop [WHILE b c1], the loop body [c1] is optimized using
  [Cexec S (WHILE b c1)] as the abstract store "before".
*)

Fixpoint cp_com (S: Store) (c: com) : com :=
  match c with
  | SKIP => SKIP
  | ASSIGN x a =>
      ASSIGN x (cp_aexp S a)
  | SEQ c1 c2 =>
      SEQ (cp_com S c1) (cp_com (Cexec S c1) c2)
  | IFTHENELSE b c1 c2 =>
      mk_IFTHENELSE (cp_bexp S b) (cp_com S c1) (cp_com S c2)
  | WHILE b c =>
      let sfix := Cexec S (WHILE b c) in
      mk_WHILE (cp_bexp sfix b) (cp_com sfix c)
  end.

(** Example: let's "optimize" Euclidean division under the dubious assumption
  that the divisor is 0... *)

Compute (cp_com (Update "b" (Some 0) Top) Euclidean_division).

(** Result is (in pseudocode):         
<<
     r := a;
     q := 0;
     while 0 <= r do
       r := r; q := q + 1
     done
>>
*)

(** The proof of semantic preservation needs an unusual induction pattern:
  structural induction on the command [c], plus an inner induction
  on the number of iterations if [c] is a loop [WHILE b c1].
  This pattern follows closely the structure of the abstract interpreter
  [Cexec]: structural induction on the command + local fixpoint for loops. *)

Lemma cp_com_correct_terminating:
  forall c s1 s2 S1, 
  cexec s1 c s2 -> matches s1 S1 -> cexec s1 (cp_com S1 c) s2.
Proof.
  induction c; intros s1 s2 S1 EXEC AG; cbn [cp_com].
- (* SKIP *)
  auto.
- (* ASSIGN *)
  inv EXEC. replace (aeval s1 a) with (aeval s1 (cp_aexp S1 a)).
  apply cexec_assign.
  apply cp_aexp_sound; auto.
- (* SEQ *)
  inv EXEC. apply cexec_seq with s'.
  apply IHc1; auto.
  apply IHc2; auto. apply Cexec_sound with s1; auto.
- (* IFTHENELSE *)
  inv EXEC.
  apply cexec_mk_IFTHENELSE.
  rewrite cp_bexp_sound by auto.
  destruct (beval s1 b); auto.
- (* WHILE *)
  set (X := Cexec S1 (WHILE b c)).
  assert (INNER: forall s1 c1 s2, 
                 cexec s1 c1 s2 ->
                 c1 = WHILE b c ->
                 matches s1 X ->
                 cexec s1 (mk_WHILE (cp_bexp X b) (cp_com X c)) s2).
  { induction 1; intros EQ AG1; inv EQ.
  - (* WHILE stop *)
    apply cexec_mk_WHILE_done. rewrite cp_bexp_sound by auto. auto.
  - (* WHILE loop *)
    apply cexec_mk_WHILE_loop with s'. rewrite cp_bexp_sound by auto. auto.
    apply IHc; auto.
    apply IHcexec2; auto.
    unfold X. cbn [Cexec]. 
    eapply matches_Le. apply fixpoint_sound.
    eapply matches_Le. apply Le_Join_r. 
    apply Cexec_sound with s; auto.
  }
  eapply INNER; eauto.
  unfold X. cbn [Cexec].
  eapply matches_Le. apply fixpoint_sound.
  eapply matches_Le. apply Le_Join_l. auto.
Qed.
