(** Author: Alexander Anisimov *)
From mathcomp Require Import ssreflect ssrbool eqtype seq choice.
From CompDecModal.libs Require Import edone bcase base fset.

Set Implicit Arguments.
(*Unset Strict Implicit.*)

(** * Automation for finite Sets *)

Section TabRules.
  
  Variable T: choiceType.

  (** Simplification rules **)
  
  (** composite set operations and relations **)
  Lemma properSub (A B : {fset T}): A `<` B = (A `<=` B) && ~~ (B `<=` A).
  Proof. rewrite properEneq eqEsub. by case (A`<=`B), (B`<=`A). Qed.
  Lemma sepI (A B : {fset T}) : A `&` B = [fset x in A | x \in B].
  Proof. by rewrite /fsetI. Qed.
  Lemma sepD (A B : {fset T}) : A `\` B = [fset x in A | x \notin B].
  Proof. by rewrite /fsetD. Qed.

  Definition compSetOps := (sepI, sepD, properSub).
  
  
  (** ** Tableau rules **)

  (** nonbranching *)

  (** one premise*)
  Lemma prop_dn s : ~~ ~~ s -> s. (*P7*)
  Proof. exact (@ negbNE s). Qed.
  
  Lemma prop_conj s t : s && t -> s /\ t. (*P1*)
  Proof. apply: andP. Qed.
  
  Lemma prop_negDisj s t : ~~ (s || t) -> ~~ s /\ ~~ t. (*P5*)
  Proof. rewrite negb_or. apply: andP. Qed.

  Lemma prop_negImpl s t : ~~ (s ==> t) -> s /\ ~~ t. (*P6*)
  Proof. rewrite negb_imply. apply: andP. Qed.

  
  Lemma satr_eqSym (a b : T) : a == b -> b == a. (*S8*)
  Proof. by rewrite eq_sym. Qed.
  
  Lemma satr_memSgt (a b : T) : a \in [fset b] -> a == b. (*S9*)
  Proof. by rewrite in_fset1. Qed.
  
  Lemma satr_nmemSgt (a b : T) : a \notin [fset b] -> a != b. (*S10*)
  Proof. by rewrite in_fset1. Qed.

  Lemma satr_sgtSub (a:T) (A : {fset T}) : [fset a] `<=` A -> a \in A. (*S11*)
  Proof. by rewrite fsub1. Qed.

  Lemma satr_eqP (A B : {fset T}) : A == B -> (A `<=` B) /\ (B `<=` A). (*S4*)
  Proof. rewrite eqEsub. apply: andP. Qed.

  Lemma satr_nmemU (a:T) (A B : {fset T}) : a \notin A `|` B -> a \notin A /\ a \notin B. (*S13*)
  Proof. rewrite in_fsetU negb_or. apply: andP. Qed.

  Lemma pow_mem (A B : {fset T}) : A \in (powerset B) -> A `<=` B. (*Q1*)
  Proof. by rewrite powersetE. Qed.

  (** several premises *)
  Lemma satr_memSub (a:T) (A B : {fset T}) : a \in A -> A `<=` B -> a \in B. (*S1*)
  Proof. move => P Q. apply: (@subP T A) => //. Qed.

  Lemma satr_nmemSup (a:T) (A B : {fset T}) : a \notin A -> B `<=` A -> a \notin B. (*S2*)
  Proof. move => P Q. case R: (a \in B) => //. by rewrite (subP Q) in P. Qed.

  Lemma satr_eqMem (a b : T) (A : {fset T}) : a == b -> b \in A -> a \in A. (*S6*)
  Proof. intros P Q. by rewrite -(eqP P) in Q. Qed.
  
  Lemma satr_eqTrans (a b c : T) : a == b -> b == c -> a == c. (*S7*)
  Proof. intros P Q. by rewrite -(eqP P) in Q. Qed.

  (** fresh variable generation *)
  Lemma satr_notSub (A B : {fset T}) : ~~ (A `<=` B) -> exists a, (a \in A) /\ (a \notin B). (*S3*)
  Proof. move => P. move: (subPn A B P) => {P} [a P Q]. by exists a. Qed.

  Lemma pow_nmem (A B : {fset T}) : A \notin (powerset B) -> exists x, (x \in A) /\ (x \notin B). (*Q2*)
  Proof. rewrite powersetE => P. apply (satr_notSub A B P). Qed.

  
  (** branching *)

  Lemma prop_disj s t : s || t -> s \/ t. (*P2*)
  Proof. apply: orP. Qed.

  Lemma prop_impl s t : s ==> t -> ~~ s \/ t. (*P3*)
  Proof. rewrite implybE. apply: orP. Qed.

  Lemma prop_negConj s t : ~~ (s && t) -> ~~ s \/ ~~ t. (*P4*)
  Proof. rewrite negb_and. apply: orP. Qed.


  Lemma satr_memU (a:T) (A B : {fset T}) : a \in A `|` B -> a \in A \/ a \in B. (*S12*)
  Proof. rewrite in_fsetU. apply: orP. Qed.

  Lemma satr_neqP (A B : {fset T}) :
    A != B -> exists x, (x \in A /\ x \notin B) \/ (x \in B /\ x \notin A). (*S5*)
  Proof.
    rewrite eqEsub negb_and => P. move: (orP P) => {P} [P|P].
    - move: (satr_notSub A B P) => {P} [x [P Q]]. exists x; by left.
    - move: (satr_notSub B A P) => {P} [x [P Q]]. exists x; by right.
  Qed.

  
  (** branch closing *)

  Lemma clos_posNeg (s : bool) : s -> ~~ s -> False. (*D1*)
  Proof. by case s. Qed.

  Lemma clos_neqxx (a : T) : a != a -> False. (*D2*)
  Proof. by rewrite eqxx. Qed.

  Lemma clos_memEmp (a : T) : a \in fset0 -> False. (*D3*)
  Proof. by rewrite in_fset0. Qed.
  

  (** substitution *)
  
  Lemma subst_memSep (y:T) (A : {fset T}) (p : T -> bool) : y \in sep A p -> (y \in A) /\ (p y). (*R1*)
  Proof. rewrite in_sep. apply: andP. Qed.

  Lemma subst_nmemSep (y:T) (A : {fset T}) (p : T -> bool):
    y \notin [ fset x in A | p x] -> y \notin A \/ ~~ p y. (*R2*)
  Proof. rewrite in_sep => P . apply: orP. by rewrite -negb_and. Qed.
  
  (** cut *)

  Lemma cut_eq (a b : T) : a == b \/ a != b.
  Proof. case (a == b); first by left. right. by apply negbT. Qed. (*C1*)

  Lemma cut_mem a (A: {fset T}) : a \in A \/ a \notin A. (*C2*)
  Proof. case (a \in A); first by left. right. by apply negbT. Qed.

  Lemma cut_sub (A B : {fset T}) : A `<=` B \/ ~~ (A `<=` B). (*C3*)
  Proof. case (A `<=` B); first by left. right. by apply negbT. Qed.

End TabRules.


(** ** Implementation of the Tactic *)

(** adding conclusions of diffrerent rule types *)

Ltac extend X PX :=
  let V := fresh "H" in
  let X := constr:(is_true X) in
  match goal with
    | _:  X |- _ => fail 1
    | _ => have V: X by apply PX
  end.

Ltac extend_conj A B PX :=
  let U := fresh "H" in
  let V := fresh "H" in
  let A := (eval simpl in (is_true A)) in
  let B := (eval simpl in (is_true B)) in
  match goal with
    | _: A, _: B |- _ => fail 1
    | _ => have [U V]: A /\ B by apply PX
  end.

Ltac extend_disj A B PX :=
  let V := fresh "H" in
  let A := (eval simpl in (is_true A)) in
  let B := (eval simpl in (is_true B)) in
  match goal with
    | _: A |- _ => fail 1
    | _: B |- _ => fail 1
    | _ => have [V | V]: A \/ B by apply PX
  end.

Ltac extend_conj_ex A B PX :=
  let X := fresh "x" in
  let U := fresh "H" in
  let V := fresh "H" in
  match goal with
    | _: is_true(?x \in A), _: is_true (?x \notin B) |- _ => fail 1
    | _ => have [X [U V]]: exists x, (x \in A) /\ (x \notin B) by apply PX
  end.

Ltac extend_disconj_ex A B PX :=
  let X := fresh "x" in
  let U := fresh "H" in
  let V := fresh "H" in
  match goal with
    | _: is_true(?x \in A), _: is_true(?x \notin B) |- _ => fail 1
    | _: is_true(?x \in B), _: is_true(?x \notin A) |- _ => fail 1
    | _ => have [X [[U V] | [U V]]]:
             exists x, (x \in A /\ x \notin B) \/ (x \in B /\ x \notin A)
               by apply PX
  end.


(** saturation *)

Ltac closebranch :=
  match goal with
  | H0: is_true (?s), H1: is_true(~~ ?s) |- _ => apply (@ clos_posNeg s); first exact H0; exact H1
  | H0: is_true (?a != ?a)               |- _ => apply (@ clos_neqxx _ a); exact H0
  | H0: is_true (?a \in fset0)           |- _ => apply (@ clos_memEmp _ a); exact H0
  end.

Ltac nonbranching :=
  match goal with
  (* one premiss *)
  | _: is_true(~~ ~~ ?s)             |- _ => extend s (prop_dn s)
  | _: is_true(?s && ?t)             |- _ => extend_conj s t (prop_conj s t)
  | _: is_true(~~ (?s || ?t))        |- _ => extend_conj (~~ s) (~~ t) (prop_negDisj s t)
  | _: is_true(~~ (?s ==> ?t))       |- _ => extend_conj s (~~ t) (prop_negImpl s t)
  | _: is_true(?a == ?b)             |- _ => extend (b == a) (satr_eqSym a b)
  | _: is_true(?a \in [fset ?b])     |- _ => extend (a == b) (satr_memSgt _ a b)
  | _: is_true(?a \notin [fset ?b])  |- _ => extend (a != b) (satr_nmemSgt _ a b)
  | _: is_true([fset ?a] `<=` ?A)    |- _ => extend (a \in A) (satr_sgtSub a A)
  | _: is_true(?A == ?B)             |- _ => extend_conj (A `<=` B) (B `<=` A) (satr_eqP A B)
  | _: is_true(?a \notin ?A `|` ?B)  |- _ => extend_conj (a \notin A) (a \notin B) (satr_nmemU a A B)
  | _: is_true(?A \in (powerset ?B)) |- _ => extend (A `<=` B) (pow_mem A B)
  (* several premises *)
  | _: is_true(?a \in ?A), _: is_true(?A `<=` ?B)    |- _ => extend (a \in B) (satr_memSub a A B)
  | _: is_true(?a \notin ?A), _: is_true(?B `<=` ?A) |- _ => extend (a \notin B) (satr_nmemSup a A B)
  | _: is_true(?a == ?b), _: is_true(?b \in ?A)      |- _ => extend (a \in A) (satr_eqMem a b A)
  | _: is_true(?a == ?b), _: is_true(?b == ?c)       |- _ => extend (a == c) (satr_eqTrans _ a b c)
  (* freshvar *)
  | _: is_true(~~ (?A `<=` ?B))         |- _ => extend_conj_ex A B (satr_notSub A B)
  | _: is_true(?A \notin (powerset ?B)) |- _ => extend_conj_ex A B (pow_nmem A B)
  (* substitution *)
  | _: is_true(?a \in sep ?A ?p) |- _ => extend_conj (a \in A) (p a) (subst_memSep a A p)
  end.

Ltac branching :=
  match goal with
  | _: is_true(?s || ?t)            |- _ => extend_disj s t (prop_disj s t)
  | _: is_true(?s ==> ?t)           |- _ => extend_disj (~~ s) t (prop_impl s t)
  | _: is_true(~~ (?s && ?t))       |- _ => extend_disj (~~ s) (~~ t) (prop_negConj s t)
  (* basic saturation *)
  | _: is_true(?a \in ?A `|` ?B)    |- _ => extend_disj (a \in A) (a \in B) (satr_memU a A B)
  | _: is_true(?A != ?B)            |- _ => extend_disconj_ex A B (satr_neqP A B)
  (*substitution *)
  | _: is_true(?a \notin sep ?A ?p) |- _ => extend_disj (a \notin A) (~~ (p a)) (subst_nmemSep a A p)
  end.

Ltac cutrules :=
  match goal with
  | _: context[?a], _: context[?A] |- _ => extend_disj (a \in A) (a \notin A) (cut_mem a A)
  | _: context[?A], _: context[?B] |- _ => extend_disj (A `<=` B) (~~(A `<=` B)) (cut_sub A B)
  | _: context[?A], _: context[?B] |- _ => extend_disj (A == B) (A != B) (cut_eq _ A B)
  end.


(** form control *)

Ltac reverywhere X :=
  repeat rewrite X;
  repeat match goal with
           | H: _ |- _ => rewrite X in H
         end.

Ltac genSubst :=
  repeat (
      let V := fresh "su" in
      match goal with
        | H: is_true(?x == ?y) |- _ =>
          match goal with
            | _: x = y |- _ => fail 1
            | _ => move: (eqP H) => V
          end
        | x := _ |- _ => subst x
      end
    ); subst.

Ltac clearNonbools :=
  repeat(
      match goal with
      | H : _ |- _ =>
        match type of H with
        | is_true _ => fail 1
        | _ = _ => fail 1
        | _ => clear H
        end
      end
    ).


(** preprocessing *)

Lemma semiDN (b:bool) : ~ ~~ b -> b.
Proof. case: b => _ //. Qed.

Lemma eq2bool (T : eqType) (a b : T) : a = b -> a == b.
Proof. move => H. by rewrite H. Qed.

Ltac oDN :=
  let V := fresh "H" in
  match goal with
  | |- is_true _ => apply semiDN; hnf => V
  | |- _ = _ => apply:eqP; apply semiDN; hnf => V
  | |- False => idtac
  end.

Ltac eq2bool :=
  let V := fresh "H" in
  match goal with
  | H: _ = _ |- _ => move:(eq2bool _ H) => V
  | _ => idtac
  end.

Ltac preproc :=
  repeat (let V := fresh "H" in move => V);
  oDN;
  eq2bool;
  reverywhere compSetOps;
  clearNonbools.


(** automated saturation without cuts *)

Ltac core :=
  repeat(
      genSubst;
      repeat nonbranching;
      try closebranch;
      genSubst;
      try branching;
      try closebranch
    ).


(** ** User-level Tactics *)

Ltac fset_dec :=
  preproc;
  repeat(
      try closebranch;
      core;
      try cutrules
    ).

(** omits cut rules *)
Ltac fset_nocut := preproc; try closebranch; core.

Ltac invert X :=
  match X with
    | (?x, ?y) =>
      match x with
        | (?x0, ?x1) => let z := invert (x0, (x1, y)) in constr:(z)
      end
    | _ => constr:(X)
  end.

(** unfolds all definitions given in a tuple before applying fset_dec *)
Ltac fset_decu X :=
  let Y := invert X in
  match Y with
    | (?x, ?xs) => unfold x in *; fset_decu xs
    | ?x => unfold x in *; fset_dec
  end.

(** omits cut rules and unfolds definitions *)
Ltac fset_nocutu X :=
  let Y := invert X in
  match Y with
    | (?x, ?xs) => unfold x in *; fset_nocutu xs
    | ?x => unfold x in *; fset_nocut
  end.
