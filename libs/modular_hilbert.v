(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs Require Import edone base fset induced_sym.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Setoid Morphisms.
Require Import Relation_Definitions.

(** * A Modular Library for Reasoing in Hilbert Systems

We build a modular library for reasoning in Hilbert systems for
classical modal logics. The Hilbert systems for these logics often
just extend the Hilbert system for a weaker logic with additonal rules
and axioms.

We define abstractly what it means for a Hilbert system to implement
minimal logic, propositional logic, K, and CTL. The main part is the
development for propositional logic, where we define the remaining
logical connecitves and use big conjunctions to simulate ND-style
reasoing in our assumption free Hilbert systems.  *)

(** ** Minimal Logic

We start with a number of Lemmas for minimal logic. This is mostly
the very basic combinator infrasutructure a a few tactic definitions. *)

Record mSystem := MSystem {
                      T :> choiceType;
                      mprv : T -> Prop;
                      Imp : T -> T -> T;
                      rMP' s t : mprv (Imp s t) -> mprv s -> mprv t;
                      axK' s t : mprv (Imp s (Imp t s));
                      axS' s t u : mprv (Imp (Imp u (Imp s t)) (Imp (Imp u s) (Imp u t)))
                    }.

Arguments mprv [m] H.

(** This is reqired to preserve the notation for instances under simplification *)
Definition Imp_op := nosimpl Imp.
Notation "s ---> t" := (@Imp_op _ s t) (at level 35, right associativity).

Lemma rMP (mS : mSystem) (s t : mS) : mprv (s ---> t) -> mprv s -> mprv t.
Proof. exact: rMP'. Qed.

Lemma axS (mS : mSystem) (s t u : mS) : mprv ((u ---> s ---> t) ---> (u ---> s) ---> u ---> t).
Proof. exact: axS'. Qed.

Lemma axK (mS : mSystem) (s t : mS) : mprv (s ---> t ---> s).
Proof. exact: axK'. Qed.

Ltac mp := eapply rMP.
Ltac S := eapply axS.
Ltac K := eapply axK.

(** Tactic to treat axioms as rules *)
Ltac rule H := first [ mp; first eapply H | mp; first mp; first eapply H ].

Section MTheory0.
  Variable (mS : mSystem).
  Implicit Types s t : mS.

  Lemma axI s : mprv (s ---> s).
  Proof. rule (axS (s ---> s) s s); K. Qed.

  Lemma axC s t u : mprv ((s ---> t ---> u) ---> t ---> s ---> u).
  Proof. (* (S (S (K (S (K S) K)) S)) (K K) *)
    mp. mp. S. mp. mp. S. mp. K. mp. mp. S. mp. K. S. K. S. mp. K. K.
  Qed.

  Lemma axB u s t : mprv ((u ---> t) ---> (s ---> u) ---> (s ---> t)).
  Proof. mp. mp. S. mp. K. S. K. Qed.

  Lemma axDup s t : mprv ((s ---> s ---> t) ---> s ---> t).
  Proof. rule axS. rule axC. exact: axI. Qed.

  Definition mImpPrv s t := mprv (s ---> t).

  Definition mImpPrv_refl s : mImpPrv s s := axI s.
  Lemma mImpPrv_trans s t u : mImpPrv s t -> mImpPrv t u -> mImpPrv s u.
  Proof. move => H1 H2. rule axB; eassumption. Qed.

  Lemma mp2 s t u :
  mprv (s ---> t ---> u) -> mprv s -> mprv t -> mprv u.
Proof. move => ax A B. by [mp; first mp; first apply ax]. Qed.
End MTheory0.

Hint Resolve axI : core.

Ltac C := eapply axC.
Ltac B := eapply axB.
Ltac drop := rule axK.

Ltac Cut u := apply (mp2 (axB u _ _)); last first.
Ltac Have u := apply (mp2 (axS u _ _)); last first.
Ltac Suff u := apply (mp2 (axS u _ _)).

(** Enable Setoid rewriting for with provable implications *)

Instance mImpPrv_rel (mS : mSystem) : PreOrder (@mImpPrv mS).
Proof. split. exact: axI. exact: mImpPrv_trans. Qed.

Instance mprv_mor (mS : mSystem) :
  Proper ((@mImpPrv mS) ++> Basics.impl) (@mprv mS).
Proof. move => x y H H'. mp; eassumption. Qed.

Instance Imp_mor (mS : mSystem) :
  Proper ((@mImpPrv mS) --> (@mImpPrv mS) ++> (@mImpPrv mS)) (@Imp mS).
Proof.
  move => x' x X y y' Y. rewrite /mImpPrv in X Y *.
  (* Abs "f" (Abs "x" (A (V "Y") (A f (A (V "X") x)))) *)
  mp. mp. B. mp. B. apply Y. mp. mp. C. B. apply X.
Qed.

(** ** Propositional Logic

In the presence of [Bot] and double negation, we can define the
remaining propositional connectives and prove the corresponding
lemmas. We also define morphisms for these connectives to enable
Setoid rewriting. *)

Record pSystem := PSystem {
                      msort :> mSystem;
                      Bot' : msort;
                      axDN' s : mprv (Imp (Imp (Imp s Bot') Bot') s)
                    }.

(** Avoid simplifictation of [Bot] fo concrete instances to avoid breaking
notations based on [Bot] *)

Definition Bot := nosimpl Bot'.
Arguments Bot {p}.

(** Notations for derived logical opertions *)

Definition Top {pS : pSystem} := @Bot pS ---> Bot.

Definition Neg (pS : pSystem) (s : pS) := (s ---> Bot).
Notation "~~: s" := (Neg s) (at level 25).

Definition And (pS : pSystem) (s t : pS) := ~~: (s ---> ~~: t).
Notation "s :/\: t" := (And s t) (at level 30, right associativity).
Arguments And {pS} s t.

Definition Or (pS : pSystem) (s t : pS) := (~~: s ---> t).
Notation "s :\/: t" := (Or s t) (at level 33, right associativity).
Arguments Or {pS} s t.

Lemma axDN (pS : pSystem) (s:pS) : mprv ((~~: ~~: s) ---> s).
Proof. exact: axDN'. Qed.

(** *** Basic Propositional Logic Facts

We prove some basic propositonal lemmas which we need to set up the
ND-style reasoning. *)

Section PTheoryBase.
  Variable pS : pSystem.
  Implicit Types s t u : pS.

  Lemma axT : mprv (@Top pS).
  Proof. exact: axI. Qed.

  Lemma axsT s : mprv (s ---> Top).
  Proof. drop. exact: axI. Qed.

  Lemma axBE s : mprv (Bot ---> s).
  Proof. rewrite <- (axDN s). K. Qed.

  Lemma axContra s t : mprv (s ---> (~~: s) ---> t).
  Proof. rewrite /Neg. rewrite -> (axBE t). by rule axC.  Qed.

  Lemma axDNI s : mprv (s ---> (~~: ~~: s)).
  Proof. exact: axContra. Qed.

  Lemma axW s t u : mprv ((s ---> t) ---> ((t ---> u) ---> s ---> u)).
  Proof. rule axC. B. Qed.

  Lemma axAEl s t : mprv (s :/\: t ---> s).
  Proof.
    rewrite /And /Neg. rewrite <- (axDN s) at 2. rule axW.
    rule axC. exact: axContra.
  Qed.

  Lemma axAEr s t : mprv (s :/\: t ---> t).
  Proof.
    rewrite /And /Neg. rewrite <- (axDN t) at 2. rule axW.
    rule axC. by drop.
  Qed.

  Lemma axAI s t : mprv (s ---> t ---> s :/\: t).
  Proof. rewrite /And /Neg. mp. mp. B. C. mp. C. done. Qed.

  Lemma axAC s t : mprv (s :/\: t ---> t :/\: s).
  Proof.
    rule axS; last apply axAEl. rule axS; last apply axAEr.
    drop. exact: axAI.
  Qed.

End PTheoryBase.

Hint Resolve axT axAEl axAEr : core.

(** Morphisms for defined locial operators *)

Instance Neg_mor (pS : pSystem) :
  Proper ((@mImpPrv pS) --> (@mImpPrv pS))(@Neg pS).
Proof. rewrite /Neg; solve_proper. Qed.

Instance And_mor (pS : pSystem) :
  Proper ((@mImpPrv pS) ==> (@mImpPrv pS) ==> (@mImpPrv pS)) (@And pS).
Proof. by rewrite /And; solve_proper. Qed.

Instance Or_mor (pS : pSystem) :
  Proper ((@mImpPrv pS) ==> (@mImpPrv pS) ==> (@mImpPrv pS)) (@Or pS).
Proof. by rewrite /Or; solve_proper. Qed.

(** *** Equivalence (Experimental)

We extend rewriting from the preorder of imlications to rewriting with
equivalences. *)

Definition Eqi (pS : pSystem) (s t : pS) := (s ---> t) :/\: (t ---> s).
Notation "s <--> t" := (Eqi s t) (at level 40, no associativity).

Definition EqiPrv (pS : pSystem) (s t : pS) := mprv (Eqi s t).

Section EqiTheoryBase.
  Variable (pS : pSystem) (s t : pS).

  Lemma axEEl : mprv ((s <--> t) ---> (s ---> t)).
  Proof. exact: axAEl. Qed.

  Lemma axEEr : mprv ((s <--> t) ---> (t ---> s)).
  Proof. exact: axAEr. Qed.

  Lemma axEI : mprv ((s ---> t) ---> (t ---> s) ---> (s <--> t) ).
  Proof. exact: axAI. Qed.
End EqiTheoryBase.

Instance eqi_induced_symmety (pS : pSystem) : InducedSym (@mImpPrv pS) (@EqiPrv pS).
Proof.
  move => s t. split => [H | [H1 H2]].
  split. by rule axEEl. by rule axEEr. by rule axEI.
Qed.

Instance induced_eqi (pS : pSystem) : Equivalence (@EqiPrv pS).
Proof. apply: induced_eqi. Qed.

(** Short cut morphisms for faster equivalence rewrites *)
Instance mprv_eqi_mor (pS : pSystem) :
  Proper (@EqiPrv pS ==> iff) (@mprv pS).
Proof. move => s t H. split. by rewrite -> H. by rewrite <- H. Qed.

Instance Neg_Eqi_mor (pS : pSystem) :
  Proper ((@EqiPrv pS) ==> (@EqiPrv pS))(@Neg pS).
Proof. rewrite /Neg; solve_proper. Qed.

Instance And_Eqi_mor (pS : pSystem) :
  Proper ((@EqiPrv pS) ==> (@EqiPrv pS) ==> (@EqiPrv pS)) (@And pS).
Proof. by rewrite /And; solve_proper. Qed.

Instance Or_Eqi_mor (pS : pSystem) :
  Proper ((@EqiPrv pS) ==> (@EqiPrv pS) ==> (@EqiPrv pS)) (@Or pS).
Proof. by rewrite /Or; solve_proper. Qed.

(** Rewriting below Equivalences *)

Instance Eqi_mor (pS : pSystem) :
  Proper ((@EqiPrv pS) ==> (@EqiPrv pS) ==> (@EqiPrv pS)) (@Eqi pS).
Proof. rewrite /Eqi. solve_proper. Qed.

Lemma ax_eq_refl (pS : pSystem)(s : pS) : mprv (s <--> s).
Proof. rule axEI; exact: axI. Qed.
Hint Resolve ax_eq_refl : core.

(** *** Big Boolean Operators *)

Notation "\and_ ( i <- r ) F" := (\big [And/Top]_(i <- r)  F)
  (at level 41, F at level 41, i at level 0,
    format "'[' \and_ ( i <- r ) '/ '  F ']'").

Notation "\and_ ( <- r )" := (\and_(i <- r) i)
  (at level 41, format "'[' \and_ ( <- r ) ']'").

Notation "\and_ ( i \in A ) F" := (\big [And/Top]_(i <- enum A)  F)
 (at level 41, F at level 41, i at level 0,
 format "'[' \and_ ( i  \in  A ) '/ '  F ']'").

Notation "\or_ ( i <- r ) F" := (\big [Or/Bot]_(i <- r)  F)
  (at level 42, F at level 42, i at level 0,
    format "'[' \or_ ( i <- r ) '/ '  F ']'").

Notation "\or_ ( <- r )" := (\or_(i <- r) i)
  (at level 42, format "'[' \or_ ( <- r ) ']'").

Notation "\or_ ( i \in A ) F" := (\big [Or/Bot]_(i <- enum A)  F)
  (at level 42, F at level 42, i at level 0,
    format "'[' \or_ ( i  \in  A ) '/ '  F ']'").

Section BigAnd.
  Variable pS : pSystem.
  Implicit Types s t : pS.

  Lemma rAI s t u : mprv (s ---> t) -> mprv (s ---> u) -> mprv (s ---> t :/\: u).
  Proof. move => H1 H2. rewrite <- H1, <- H2. rule axDup. exact: axAI. Qed.

  Lemma rAIL s t u : mprv (s :/\: t ---> u) -> mprv (s ---> t ---> u).
  Proof. move => H. rewrite <- H. exact: axAI. Qed.

  (** Introduction and eliminiation for big conjunctions *)

  Lemma bigAE (T:eqType) (F : T -> pS) (xs : seq T) (s:T) :
    s \in xs -> mprv ((\and_(x <- xs) F x) ---> F s).
  Proof.
    elim: xs; first by rewrite in_nil. move => t xs IH. rewrite inE big_cons.
    case/orP; first by move/eqP->. move/IH => E. by rewrite <- E.
  Qed.

  Lemma bigAI (T : eqType) s (r : seq T) F :
    (forall i, i \in r -> mprv (s ---> F i)) -> mprv (s ---> \and_(i <- r) F i).
  Proof.
    elim: r => [ _ |x r IH H]; first by rewrite big_nil; mp; [K|].
    rewrite big_cons. apply: rAI; first by apply: H; rewrite mem_head.
    apply: IH => i Hi. apply: H. by rewrite inE Hi orbT.
  Qed.

  Lemma and_sub (T : eqType) (xs ys : seq T) (F : T -> pS) :
    {subset xs <= ys} -> mprv ((\and_(i <- ys) F i) ---> \and_(j <- xs) F j).
  Proof. move => H. apply: bigAI => s /H. exact: bigAE. Qed.

  Lemma bigAdup s xs : mprv (\and_(<- s :: xs) ---> \and_(<-[:: s, s & xs])).
  Proof. apply: and_sub => x. by rewrite !inE orbA Bool.orb_diag. Qed.

  Lemma bigAdrop s xs : mprv (\and_(<- s :: xs) ---> \and_(<- xs)).
  Proof. apply: and_sub => x. by rewrite !inE => ->. Qed.

  Lemma bigA1E s : mprv (\and_(<- [:: s]) ---> s).
  Proof. by rewrite -> big_cons, big_nil. Qed.

  (** We use big conjuctions for assumption management to allow for ND-style reasoning *)

  Lemma rIntro s t xs : mprv ((\and_(<- s :: xs) ---> t)) -> mprv (\and_(<- xs) ---> s ---> t).
  Proof. rewrite big_cons => H. rewrite <- H, <- axAC. exact: axAI. Qed.

  Lemma rHyp s : mprv (\and_(<- [::]) ---> s) -> mprv s.
  Proof. move => H. by rewrite <- H, big_nil. Qed.

  Lemma rHyp1 s t : mprv (\and_(<- [:: s]) ---> t) -> mprv (s ---> t).
  Proof. move => H. by apply rHyp,rIntro. Qed.

  Lemma rDup s xs t : mprv (\and_(<-[:: s, s & xs]) ---> t) -> mprv (\and_(<- s :: xs) ---> t).
  Proof. move => H. by rewrite -> bigAdup. Qed.

  Lemma axRot s xs : mprv (\and_(<- s :: xs) ---> \and_(<- rcons xs s)).
  Proof. apply: and_sub => x. by rewrite mem_rcons. Qed.

  Lemma rRot s xs t : mprv (\and_(<- rcons xs s) ---> t) -> mprv (\and_(<- s :: xs) ---> t).
  Proof. move => H. by rewrite -> axRot. Qed.

  Lemma rApply s xs t : mprv (\and_(<-xs) ---> s) -> mprv (\and_(<- s ---> t :: xs) ---> t).
  Proof. move => H. rewrite -> big_cons, H. by rule (axS s). Qed.

  Lemma rApply2 s0 s1 xs t :
    mprv (\and_(<-xs) ---> s0) -> mprv (\and_(<-xs) ---> s1)  ->
    mprv (\and_(<- s0 ---> s1 ---> t :: xs) ---> t).
  Proof. move => *. rule (axS s1). by apply rApply. by rewrite -> bigAdrop. Qed.

  Lemma rApply3 s0 s1 s2 xs t :
    mprv (\and_(<-xs) ---> s0) -> mprv (\and_(<-xs) ---> s1)  -> mprv (\and_(<-xs) ---> s2) ->
    mprv (\and_(<- s0 ---> s1 ---> s2 ---> t :: xs) ---> t).
  Proof. move => *. rule (axS s2). by apply rApply2. by rewrite -> bigAdrop. Qed.

End BigAnd.

Ltac Asm := by apply: bigAE; rewrite !inE !eqxx.
Ltac Intro := first [apply rIntro | apply rHyp1].
Ltac Apply := first [eapply rApply | eapply rApply2 | eapply rApply3 ]; try Asm.
Tactic Notation "Apply*" integer(n) := (do n apply rRot); Apply.

Lemma axAcase (pS : pSystem) (u s t : pS) : mprv ((u ---> s ---> t) ---> (u :/\: s ---> t)).
Proof. do 2 Intro. Apply* 1; by rewrite -> bigA1E. Qed.

Lemma rRev (pS : pSystem) (s t : pS) xs : mprv (\and_(<- xs) ---> s ---> t) -> mprv ((\and_(<- s :: xs) ---> t)).
Proof. rewrite big_cons => H. rewrite -> axAC. by rule axAcase. Qed.

Lemma rRev1 (pS : pSystem) (s t : pS) : mprv (s ---> t) -> mprv ((\and_(<- [:: s]) ---> t)).
Proof. rewrite big_cons => H. by rewrite -> axAEl. Qed.

Ltac Rev := first [eapply rRev1 | eapply rRev].

Ltac ApplyH H := first [ drop; by apply H
                       | rule axS; first (drop; by apply H)
                       | rule axS; first (rule axS; first (drop; by apply H))
                       | rule axS; first (rule axS; first (rule axS ; first (drop; by apply H))) ]; try Asm.


Ltac Rot n := do n (apply rRot).
Tactic Notation "Rev*" integer(n) := (do n apply rRot); Rev.

(** *** Remaining Propostional Logic Facts *)

Section PTheory.
  Variable pS : pSystem.
  Implicit Types s t u : pS.

  Lemma axDNE s : mprv ((~~: ~~: s) <--> s).
  Proof. rule axAI. exact: axDN. exact: axDNI. Qed.

  Lemma ax_case s t : mprv ((s ---> t) ---> (Neg s ---> t) ---> t).
  Proof.
    rewrite <- (axDN t) at 3. do 3 Intro. apply rDup; Apply.
    Apply* 1. Intro. Apply* 2. by Apply* 1.
  Qed.

  Lemma ax_contra s t : mprv ((~~:t ---> ~~: s) ---> (s ---> t)).
  Proof. do 2 Intro. ApplyH axDN. Intro. by Apply* 2. Qed.

  Lemma ax_contraNN s t : mprv ((s ---> t) ---> ~~:t ---> ~~: s).
  Proof. do 3 Intro. Apply* 1. Apply. Qed.

  Lemma axA2 s : mprv (s <--> s :/\: s).
  Proof. rule axEI; last exact: axAEl. Intro. ApplyH axAI. Qed.

  Lemma axAsT s : mprv (s <--> s :/\: Top).
  Proof. rule axEI. by rewrite <- axAC, <- axAI. exact: axAEl. Qed.

  Lemma axOIl s t : mprv (s ---> s :\/: t).
  Proof. exact: axContra. Qed.

  Lemma axOIr s t : mprv (t ---> s :\/: t).
  Proof. exact: axK. Qed.

  Lemma axOE s t u : mprv ((s ---> u) ---> (t ---> u) ---> (s :\/: t ---> u)).
  Proof. rewrite /Or. do 3 Intro. ApplyH (ax_case s u). Intro. do 2 Apply* 2. Qed.

  Lemma axOC s t : mprv (s :\/: t ---> t :\/: s).
  Proof. rule axOE; auto using axOIl, axOIr. Qed.

  Lemma axOF s : mprv (Bot :\/: s ---> s).
  Proof. rule axOE => //. exact: axBE. Qed.

  Lemma bigOE (T : eqType) F (xs :seq T) (s : pS) :
    (forall j, j \in xs -> mprv (F j ---> s)) -> mprv ((\or_(i <- xs) F i) ---> s).
  Proof.
    elim: xs. move => _. rewrite big_nil. exact: axBE.
    move => t xs IH H. rewrite big_cons. rule axOE. exact: H (mem_head _ _).
    apply: IH => j in_xs. apply: H. by rewrite inE in_xs.
  Qed.

  Lemma bigOI (T : eqType) (xs :seq T) j (F : T -> pS) :
     j \in xs -> mprv (F j ---> \or_(i <- xs) F i).
  Proof.
    elim: xs => //= t xs IH.
    rewrite inE big_cons => /orP [/eqP -> |]. exact: axOIl.
    move => in_xs. rewrite -> IH => //. exact: axOIr.
  Qed.

  Lemma or_sub (T : eqType) (xs ys :seq T) (F : T -> pS) :
    {subset xs <= ys} -> mprv ((\or_(i<-xs) F i) ---> (\or_(j<-ys) F j)).
  Proof. move => H. apply: bigOE => s /H. exact: bigOI. Qed.

  Lemma axIO s t : mprv ((s ---> t) ---> (~~: s :\/: t)).
  Proof. rewrite /Or. by rewrite -> axDN. Qed.

  Lemma axAODr s t u : mprv (u :/\: (s :\/: t) <--> u :/\: s :\/: u :/\: t).
  Proof. rule axEI. 
    rule axAcase. rule axC. rule axOE; rule axC; [rewrite <- axOIl|rewrite <- axOIr];exact: axAI.
    rule axOE;[rewrite <- axOIl|rewrite <- axOIr]; exact: axI.
  Qed.

  Lemma bigODr (T:eqType) (xs : seq T) (t : pS) (F : T -> pS) : 
    mprv ((\or_(i <- xs) F i) :/\: t <--> (\or_(i <- xs) F i :/\: t)).
  Proof. rule axEI. 
    - rule axAcase. apply: bigOE => j Hj. apply: rAIL. rewrite <- (bigOI _ Hj). exact: axI.
    - apply: bigOE => j Hj. rule axAcase. do 2 Intro. ApplyH axAI. Rev* 1. drop. exact: bigOI.
  Qed.

  Lemma dmO s t : mprv (~~: (s :\/: t) <--> (~~: s) :/\: (~~: t)).
  Proof. rewrite /Or /And. rule axAI; by rewrite -> axDNE. Qed.

  Lemma dmA s t : mprv (~~: (s :/\: t) <--> (~~: s) :\/: (~~: t)).
  Proof. rewrite /Or /And. rule axAI; by do ! rewrite -> axDNE. Qed.

  Lemma dmI s t : mprv (~~: (s ---> t) <-->  s :/\: ~~: t).
  Proof. rewrite /And. rule axAI; by do ! rewrite -> axDNE. Qed. 

End PTheory.

Lemma axADr (pS : pSystem) (s t u : pS) :
  mprv ((s :\/: t) :/\: u <--> s :/\: u :\/: t :/\: u).
Proof. rule axAI.
  - rule axAcase. rule axOE. rewrite <- axOIl. exact: axAI.
    rewrite <- axOIr. exact: axAI.
  - rule axOE; rule axAcase. rewrite <- axOIl. exact: axAI.
    rewrite <- axOIr. exact: axAI.
Qed.

Lemma axAA (pS : pSystem) (s t u : pS) : mprv ((s :/\: t) :/\: u <--> s :/\: t :/\: u).
Proof. rule axAI.
  - do 2 rule axAcase. do 3 Intro. ApplyH axAI. ApplyH axAI.
  - rule axAcase; Intro. ApplyH axAcase; do 2 Intro. ApplyH axAI. ApplyH axAI.
Qed.

(** ** Basic Modal Logic *)


Record kSystem := KSystem { psort   :> pSystem;
                            AX     : psort -> psort;
                            rNec s  : mprv s -> mprv (AX s);
                            axN s t: mprv (AX (s ---> t) ---> AX s ---> AX t) }.

Lemma rNorm (kS : kSystem) (s t : kS) : mprv (s ---> t) -> mprv (AX s ---> AX t).
Proof. move => H. rule axN. exact: rNec. Qed.

Instance AX_mor (kS : kSystem) : Proper ((@mImpPrv kS) ==> (@mImpPrv kS)) (@AX kS).
Proof. exact: rNorm. Qed.

Definition EX (kS : kSystem) (s : kS) := ~~: AX (~~: s).

Instance EX_mor (kS : kSystem) : Proper ((@mImpPrv kS) ==> (@mImpPrv kS)) (@EX kS).
Proof. move => x y H. rewrite /EX /mImpPrv. by rewrite -> H. Qed.

(** Redundant Morphisms for Equivalence *)

Instance AX_Eqi_mor (kS : kSystem) : Proper ((@EqiPrv kS) ==> (@EqiPrv kS)) (@AX kS).
Proof. move => s t H. rewrite -> H. reflexivity. Qed.

Instance EX_Eqi_mor (kS : kSystem) : Proper ((@EqiPrv kS) ==> (@EqiPrv kS)) (@EX kS).
Proof. move => s t H. rewrite -> H. reflexivity. Qed.

Section KTheory.
  Variable kS : kSystem.
  Implicit Types s t u : kS.

  Lemma axBT : mprv (@AX kS Top).
  Proof. exact: rNec. Qed.
  Hint Resolve axBT : core.

  Lemma axDF : mprv (@EX kS Bot ---> Bot).
  Proof. rewrite /EX. Intro; Apply. drop. exact: axBT. Qed.

  Lemma axABBA s t : mprv (AX s :/\: AX t <--> AX (s :/\: t)).
  Proof. rule axEI. 
    - rule axAcase. rewrite <- axN. apply rNorm. exact: axAI.
    - Intro. ApplyH axAI; Rev; by apply rNorm.
  Qed.
  
  Lemma bigABBA (T : eqType) (xs : seq T) (F : T -> kS) :
    mprv ((\and_(s <- xs) AX (F s)) ---> AX (\and_(s <- xs) F s)).
  Proof.
    elim: xs; first by drop; rewrite big_nil.
    move => t xs IH. rewrite !big_cons. by rewrite -> IH, axABBA.
  Qed.

  Lemma axDBD s t : mprv (EX s ---> AX t ---> EX (s :/\: t)).
  Proof.
    rewrite /EX. do 3 Intro. Apply* 2. do 2 Rev. rewrite <- axN.
    apply: rNorm. do 3 Intro. Apply* 1. ApplyH axAI.
  Qed.

  Lemma rEXn s t : mprv (s ---> t) -> mprv (EX s ---> EX t).
  Proof. rewrite /EX => H. by rewrite -> H. Qed.

  Lemma dmAX s : mprv (~~: AX s <--> EX (~~: s)).
  Proof. rewrite /EX. by rewrite -> axDNE. Qed.

End KTheory.

(** ** K* *)

Record ksSystem :=
  KSSystem { ksort'       :> kSystem;
             AG          : ksort' -> ksort';
             axAGEl s    : mprv (AG s ---> s) ;
             axAGEr s    : mprv (AG s ---> AX (AG s)) ;
             rAG_ind u s : mprv (u ---> AX u) -> mprv (u ---> s) -> mprv (u ---> AG s)
           }.

Definition EF {ksS : ksSystem} (s : ksS) := ~~: AG (~~: s).

Section KStarTheory.
  Variables (ksS : ksSystem).
  Implicit Types s t u : ksS.

  Lemma rNecS s : mprv s -> mprv (AG s).
  Proof. move => H. apply: rMP (H). apply: rAG_ind => //. drop. exact: rNec. Qed.

  Lemma axAGN s t : mprv (AG (s ---> t) ---> AG s ---> AG t).
  Proof.
    apply: rAIL. apply: rAG_ind.
    - rewrite -> axAGEr at 1. by rewrite -> (axAGEr s),axABBA at 1.
    - rule axAcase. by do 2 rewrite -> axAGEl.
  Qed.

  Lemma axAGE s : mprv (AG s <--> s :/\: AX (AG s)).
  Proof.
    have S: mprv (AG s ---> s :/\: AX (AG s)).
      rewrite -> (axA2 (AG s)) at 1. by rewrite -> axAGEl,axAGEr at 1.
    rule axEI => //. apply: rAG_ind; last exact: axAEl.
    rule axAcase. drop. exact: rNorm.
  Qed.

  Lemma rNormS s t : mprv (s ---> t) -> mprv (AG s ---> AG t).
  Proof. move/rNecS. apply: rMP. exact: axAGN. Qed.

  Instance AG_mor : Proper ((@mImpPrv ksS) ==> (@mImpPrv ksS)) (@AG ksS).
  Proof. exact: rNormS. Qed.

  Lemma axAGEn s : mprv (~~: AG s ---> ~~: s :\/: ~~: AX (AG s)).
  Proof. rewrite -> axAGE at 1. by rewrite -> dmA. Qed.

  Lemma rAGp_ind (k : ksSystem) (u s : k) : mprv (u ---> AX (u :/\: s)) -> mprv (u ---> AX (AG s)).
  Proof.
    move => H /=. rewrite -> H. apply: rNorm. apply: rAG_ind; last exact: axAEr.
    rewrite <- H. exact: axAEl.
  Qed.

  Lemma segerberg s : mprv (AG (s ---> AX s) ---> s ---> AG s).
  Proof.
    apply: rAIL. apply: rAG_ind; last exact: axAEr.
    rewrite -> axAGE at 1. do 2 rule axAcase. 
    do 3 Intro. rewrite <- axABBA. ApplyH axAI. by Apply* 2.
  Qed.

End KStarTheory.

(** ** CTL *)

Record ctlSystem :=
  CTLSystem { ksort         :> kSystem;
              AU            : ksort -> ksort -> ksort;
              AR            : ksort -> ksort -> ksort;
              rAU_ind s t u : mprv (t ---> u) -> mprv (s ---> AX u ---> u) -> mprv ((AU s t) ---> u);
              axAUI s t     : mprv (t ---> AU s t);
              axAUf s t     : mprv (s ---> AX (AU s t) ---> AU s t);
              rAR_ind s t u :
                mprv (u ---> t) -> mprv (u ---> (s ---> Bot) ---> AX u) -> mprv (u ---> AR s t);
              axARE s t    : mprv (AR s t ---> t);
              axARu s t    : mprv (AR s t ---> (s ---> Bot) ---> AX (AR s t))
            }.

Definition ER {cS : ctlSystem} (s t : cS) := ~~: AU (~~: s) (~~: t).
Definition EU {cS : ctlSystem} (s t : cS) := ~~: AR (~~: s) (~~: t).
Notation "'EG' s" := (ER Bot s) (at level 8).

Instance AU_mor (cS : ctlSystem) :
  Proper ((@mImpPrv cS) ==> (@mImpPrv cS) ==> (@mImpPrv cS))(@AU cS).
Proof.
  move => x x' X y y' Y. rewrite /mImpPrv in X Y *.
  apply: rAU_ind. rewrite -> Y. exact: axAUI. rewrite -> X. exact: axAUf.
Qed.

Instance ER_mor (cS : ctlSystem) :
  Proper ((@mImpPrv cS) ==> (@mImpPrv cS) ==> (@mImpPrv cS))(@ER cS).
Proof. rewrite /ER. solve_proper. Qed.

Instance AR_mor (cS : ctlSystem) :
  Proper ((@mImpPrv cS) ==> (@mImpPrv cS) ==> (@mImpPrv cS))(@AR cS).
Proof.
  move => x x' X y y' Y. rewrite /mImpPrv in X Y *.
  apply: rAR_ind. rewrite <- Y. exact: axARE. rewrite <- X. exact: axARu.
Qed.

Instance EU_mor (cS : ctlSystem) :
  Proper ((@mImpPrv cS) ==> (@mImpPrv cS) ==> (@mImpPrv cS))(@EU cS).
Proof. rewrite /EU. solve_proper. Qed.

Section CTLTheory.
  Variable cS : ctlSystem.
  Implicit Types s t u : cS.

  Lemma axAUeq s t : mprv (AU s t <--> t :\/: s :/\: AX (AU s t)).
  Proof.
    rule axAI.
    - apply: rAU_ind; first exact: axOIl.
      rewrite /Or. do 3 Intro. ApplyH axAI. apply: rRot => /=. Rev. drop.
      apply: rNorm. Intro. ApplyH (ax_case t); Intro; first by ApplyH axAUI.
      ApplyH axAUf; [ApplyH axAEl|ApplyH axAEr]; Apply* 1.
    - rule axOE; first exact: axAUI. rule axAcase. exact: axAUf.
  Qed.

  Lemma rER_ind u s t : mprv (u ---> t) -> mprv (u ---> ~~: s ---> EX u) -> mprv (u ---> ER s t).
  Proof.
    move => H0 H1. rewrite /ER. rule ax_contra. rewrite -> axDN.
    apply: rAU_ind. by rewrite -> H0. do 3 Intro. by ApplyH H1.
  Qed.

  Lemma axAUEGF s t : mprv (AU s t ---> EG (~~: t) ---> Bot).
  Proof. rewrite /ER. do 2 Intro. Apply. Rev. by rewrite -> (axsT s), <-(axDNI t). Qed.

  (** de Morgan Lemmas *)

  Lemma dmAR s t : mprv (~~: (AR s t) <--> EU (~~: s) (~~: t)).
  Proof. rewrite /EU. by rule axEI; do ! rewrite -> axDNE. Qed.

  Lemma dmAU s t : mprv ((~~: AU s t) <--> ER (~~: s) (~~: t)).
  Proof. rewrite /ER. rule axAI; by do ! rewrite -> axDNE. Qed.

  Lemma dmER s t : mprv ((~~: ER s t) <--> AU (~~: s) (~~: t)).
  Proof. rewrite /ER. rule axAI; by do ! rewrite -> axDNE. Qed.

  Lemma dmEU s t : mprv ((~~: EU s t) <--> AR (~~: s) (~~: t)).
  Proof. rewrite /EU. rule axAI; by do ! rewrite -> axDNE. Qed.
  
  Lemma axERu s t : mprv (ER s t ---> t :/\: (s :\/: EX (ER s t))).
  Proof.
    rule ax_contra. rewrite /ER. rewrite <- axDNI, dmA, dmO.
    rewrite /EX. do ! rewrite -> axDN. rule axOE. exact: axAUI.
    rule axAcase. exact: axAUf.
  Qed.

  Lemma axAUERF s t : mprv (AU s t :/\: ER (~~: s) (~~: t) ---> Bot).
  Proof. rule axAcase. rewrite /ER. do 2 Intro. Apply. Rev. by do ! rewrite <- axDNI. Qed.


  Lemma axAUAEr s t u : mprv (AU (s :/\: u) (t :/\: u) ---> u).
  Proof. apply: rAU_ind => //. rewrite -> axAEr. by K. Qed.

  Lemma axAUAw s t u : mprv (AU (s :/\: u) (t :/\: u) ---> AU s t).
  Proof.
    apply: rAU_ind. rewrite -> axAEl. exact: axAUI.
    rewrite -> axAEl. exact: axAUf.
  Qed.

  Lemma EU_ind s t u :
    mprv (t ---> u) -> mprv (s ---> EX u ---> u) -> mprv (EU s t ---> u).
  Proof.
    move => H1 H2. rewrite /EU. rule ax_contra. rewrite <- axDNI.
    apply: rAR_ind; first by rule ax_contraNN.
    rewrite -[~~: s ---> Bot]/(~~: ~~: s). rewrite -> axDN. rule axC.
    Intro. ApplyH ax_contra. rewrite <- axDNI. ApplyH H2.
  Qed.


  Lemma axEUI s t : mprv (t ---> EU s t).
  Proof. rewrite /EU. rewrite -> (axDNI t) at 1. rule ax_contraNN. exact: axARE. Qed.

  Lemma axEUI2 s t : mprv (s ---> EX (EU s t) ---> EU s t).
  Proof.
    rewrite /EU. rewrite -> (axDNI s) at 1. Intro. ApplyH ax_contraNN; Intro.
    Suff (AX (AR (~~: s) (~~: t))). drop. apply: rNorm. exact: axDNI.
    ApplyH axARu.
  Qed.

  Lemma axAReq s t : mprv (AR s t <--> t :/\: (s :\/: AX (AR s t))).
  Proof.
    rule axEI.
    - ApplyH axAI. exact: axARE. do 2 Intro. ApplyH axARu.
    - apply: rAR_ind; first exact: axAEl.
      rule axAcase; drop. rule axOE; first exact: axContra. rule axC; drop.
      apply: rNorm. ApplyH axAI. exact: axARE. exact: axARu.
  Qed.

  Lemma axEUeq s t : mprv (EU s t <--> t :\/: s :/\: EX (EU s t)).
  Proof.
    rewrite /EU /EX. rewrite -> axDNE, axAReq at 1. rewrite -> dmA,dmO at 1.
    by do ! rewrite -> axDNE.
  Qed.    

  Lemma axEUw s t u : mprv (EU (s :/\: u) (t :/\: u) ---> EU s t).
  Proof. by do ! rewrite -> axAEl. Qed.

  Lemma axEUEr s t u : mprv (EU (s :/\: u) (t :/\: u) ---> u).
  Proof.
    rewrite -> axEUeq. rule axOE; first exact: axAEr.
    rewrite -> axAEl. exact: axAEr.
  Qed.

  Lemma rAU_ind_weak u s t :
    mprv (t ---> u) -> mprv (AX u ---> u) -> mprv ((AU s t) ---> u).
  Proof. move => A B. apply rAU_ind => //. rewrite -> B. by drop. Qed.

  Lemma rER_ind_weak u s t :
    mprv (u ---> t) -> mprv (u ---> EX u) -> mprv (u ---> ER s t).
  Proof.
    move => H0 H1. rewrite /ER. rule ax_contra. rewrite -> axDN.
    apply: rAU_ind_weak. by rewrite -> H0. do 2 Intro. ApplyH H1.
  Qed.

  Lemma EXR_ind s t u : mprv (u ---> EX (t :/\: (s :\/: u))) -> mprv (u ---> EX (ER s t)).
  Proof.
    move => IH. rewrite -> IH. apply: rEXn. apply: rER_ind. exact: axAEl.
    rewrite <- IH. rule axAcase. drop. exact: axI.
  Qed.

  Lemma AXR_ind s t u : mprv (u ---> AX (t :/\: (s :\/: u))) -> mprv (u ---> AX (AR s t)).
  Proof. 
    move => IH. rewrite -> IH. apply: rNorm. apply: rAR_ind. exact: axAEl.
    rewrite <- IH. rule axAcase. drop. exact: axI. 
  Qed.

End CTLTheory.


(** fset lemmas *)

Lemma andU  (T : choiceType) (pS : pSystem) (F : T -> pS) (X Y : {fset T}) :
  mprv ((\and_(s <- X `|` Y) F s) <--> (\and_(s <- X) F s) :/\: (\and_(s <- Y) F s)).
Proof. rule axAI.
  - apply: rAI; apply: and_sub; apply/subP; auto with fset.
  - apply: bigAI => s; case/fsetUP; [rewrite -> axAEl|rewrite -> axAEr]; exact: bigAE.
Qed.

Lemma bigA1 (T : choiceType) (pS : pSystem) (F : T -> pS) (s : T) :
  mprv ((\and_(s <- [fset s]) F s) <--> F s).
Proof.
  rewrite fset1Es. rule axAI. rewrite big_cons big_nil. by rewrite -> axAEl.
  apply: bigAI => ?. by rewrite inE => /eqP ->.
Qed.

(** set lemmas (Ssreflect's finite sets) *)

Lemma bigAUA (T : finType) (pS : pSystem) (A B : {set T}) (F : T -> pS) :
  mprv ((\and_(s \in A :|: B) F s) ---> (\and_(s \in A) F s) :/\: (\and_(s \in B) F s)).
Proof. apply: rAI; apply: and_sub => x; by rewrite !mem_enum inE => ->.  Qed.

Lemma andAAU (T : finType) (pS : pSystem) (A B : {set T}) (F : T -> pS) :
  mprv ((\and_(s \in A) F s) :/\: (\and_(s \in B) F s) ---> (\and_(s \in A :|: B) F s)).
Proof.
  apply: bigAI => s.
  rewrite mem_enum => /setUP [H|H]; [rewrite -> axAEl | rewrite -> axAEr];
    apply: bigAE; by rewrite mem_enum.
Qed.
