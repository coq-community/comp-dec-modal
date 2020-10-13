(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base sltype.
From CompDecModal.K
 Require Import K_def.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments subsep {T X P}.

Implicit Types (S cls X Y : {fset clause}) (C D : clause).

(** * Demos *)

(** A demo consists of a finite set of clauses that satisfy the demo
conditions. We do not enfoce that that the demo contains only literal
clauses. However, non-literal clauses do not change the support of a
clause and therefore also need not be satisfied by the construced
model (See [supp_eval]). *)

Definition D0 cls := forall C, C \in cls -> lcons C.
Definition D1 cls := forall C, C \in cls -> forall s, fAX s^- \in C -> suppS cls (s^- |` R C).

Record demo := Demo
{
  cls :> {fset clause} ; 
  demoD0 : D0 cls ;
  demoD1 : D1 cls
}.

Arguments demoD1 [d C] _ [s] _.


Canonical demo_predType := PredType (fun (S : demo) (C : clause) => nosimpl C \in cls S).

Lemma LCF C : lcons C ->
  ((fF^+ \in C) = false) * (forall p, (fV p^+ \in C) && (fV p^- \in C) = false).
Proof.
  move => /andP [/negbTE-> /allP H]. split => // p.
  case e: (_^+ \in _) => //=. by rewrite (negbTE (H _ e)).
Qed.

(** ** Model Existence *)

Definition rtrans C D := suppC D (R C).

Section ModelExistience.
  Variables (S : demo).

  Definition Mtype := seq_sub S.
  Definition Mtrans : rel Mtype := @restrict _ S rtrans.
  Definition Mlabel (p:var) (C : Mtype) := fV p^+ \in val C.

  Definition model_of := FModel Mtrans Mlabel.

  Implicit Types (x y : model_of).

  Lemma supp_eval s x : val x |> s -> eval (interp s) x.
  Proof.
    case: s x. elim => [|p|s IHs t IHt|s IHs] [|] x.
    - by rewrite /= (LCF (demoD0 (ssvalP x))).
    - by rewrite /=. 
    - done.
    - rewrite /= /Mlabel. case: (LCF (demoD0 (ssvalP x))) => [_ /(_ p)].
      by case: (_^+ \in _) => //= ->.
    - rewrite /=. case/orP => [/IHs|/IHt] /=; tauto.
    - rewrite /=. case/andP => [/IHs ? /IHt] /=; tauto.
    - move => inX y xy. apply: (IHs true).
      rewrite -suppC1. apply: suppC_sub xy. by rewrite fsub1 RE.
    - rewrite [_ |> _]/= => H. case/hasP : (demoD1 (ssvalP x) H) => D inS.
      rewrite suppCU suppC1 => /andP [D1 D2] /= /(_ (Sub D inS)) /(_ D2).
      exact: (IHs false).
  Qed.

End ModelExistience.

(** ** Pruning *)

Section Pruning.
  Variables (F : clause).
  Hypothesis sfc_F : sf_closed F.

  Definition U := powerset F.
  Definition S0 := [fset C in U | literalC C && lcons C].

  Definition pcond C S :=
    ~~ [all u in C, if u is fAX s^- then suppS S (s^- |` R C) else true].

  (** Pruning yields a demo *)

  Lemma prune_D0 : D0 (prune pcond S0).
  Proof. move => C. move/(subP (prune_sub _ _)). rewrite inE. bcase. Qed.

  Lemma prune_D1 : D1 (prune pcond S0).
  Proof. move => C /pruneE. rewrite negbK => /allP H s inC. exact: (H _ inC). Qed.

  Definition DD := Demo prune_D0 prune_D1.

  (** Note: in contrast to the mathematical text the pruning function uses [pcond C S]
  as pruning rules rather than [~~ pcond C S] *)

  (** ** Refutation Predicates and corefutability of the pruning demo *)

  Definition coref (ref : clause -> Prop) S :=
    forall C, C \in S0 `\` S -> ref C.

  Inductive ref : clause -> Prop :=
  | R1 S C : C \in U -> coref ref S -> ~~ suppS S C -> ref C
  | R2 C s : ref (s^- |` R C) -> ref (fAX s^- |` C).
    
  Lemma corefD1 S C : ref C -> coref ref S -> coref ref (S `\` [fset C]).
  Proof.
    move => rC coS D. rewrite !in_fsetD negb_and andb_orr -in_fsetD negbK in_fset1.
    case/orP; first exact: coS. by case/andP => [_ /eqP->].
  Qed.

  Lemma R1inU C s : C \in U -> fAX s^- \in C -> s^- |` R C \in U.
  Proof.
    move => CinU inC. rewrite powersetU RinU // powersetE fsub1 andbT.
    rewrite powersetE in CinU. by move/(subP CinU)/sfc_F : inC.
  Qed.

  (** The pruning demo is corefutable *)

  Lemma coref_DD : coref ref DD.
  Proof.
    apply: prune_myind => [C|C S]; first by rewrite inE andbN.
    - case/allPn. (do 2 case) => // s [//|] inC nS inS corefS subS0.
      apply: corefD1 (corefS). 
      rewrite (fset1U inC). apply R2 => //. apply: R1 nS => //.
      move/(subP subS0)/(subP subsep): inS => inU. exact: R1inU.
  Qed.

  Lemma DD_refute C : C \in U -> ~~ suppS DD C -> ref C.
  Proof. move => inU. apply: R1 inU _  => //. exact: coref_DD. Qed.

End Pruning.

(** ** Refutation Completeness *)

Theorem refutation_completeness F (sfc_F : sf_closed F) C :
  C \in U F -> ref F C + exists2 M:fmodel, sat M C & #|{: M}| <= 2 ^ size F.
Proof.
  move => inU. case: (boolP (suppS (DD F) C)) => H; [right|left; exact: DD_refute].
  - exists (model_of (DD F)).
    case/hasP : H => D D1 D2. exists (SeqSub _ D1) => s /(allP D2) ?. exact: supp_eval.
  - rewrite card_seq_sub ?funiq // -powerset_size subset_size // /DD /=.
    exact: sub_trans (prune_sub _ _) (subsep).
Qed.

