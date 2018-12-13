(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base sltype.
Require Import Kstar_def.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments subsep [T X P].

Implicit Types (S cls X Y : {fset clause}) (C D : clause).

(** * Demos *)

Definition suppS S C := [some D in S, suppC D C].

Definition rtrans C D := suppC D (R C).

Inductive fulfillAG S s C : Prop :=
| fulfillAG1 D : D \in S -> rtrans C D -> D |> s^- -> fulfillAG S s C
| fulfillAGn D : D \in S -> rtrans C D -> fulfillAG S s D -> fulfillAG S s C.

Lemma fulfillAGEn s S C : ~ fulfillAG S s C ->
  forall D, D \in S -> rtrans C D -> ~~ D |> s^- /\ ~ fulfillAG S s D. 
Proof.
  move => (* inS *) H D CD.
  split => [|Ds]; last by apply: H; apply: fulfillAGn Ds.
  apply/negP => Ds. apply H. exact: fulfillAG1 Ds.
Qed.

Definition D0 cls := forall C, C \in cls -> lcons C.
Definition D1 cls := forall C, C \in cls -> forall s, fAX s^- \in C -> suppS cls (s^- |` R C).
Definition D2 cls := forall C, C \in cls -> forall s, fAX (fAG s)^- \in C -> fulfillAG cls s C.

(** A demo consists of a finite set of clauses that satisfy the demo
conditions. We do not enfoce that that the demo contains only literal
clauses. However, non-literal clauses do not change the support of a
clause and therefore also need not be satisfied by the construced
model (See [supp_eval]). *)

Record demo := Demo
{
  cls :> {fset clause} ; 
  demoD0 : D0 cls ;
  demoD1 : D1 cls ;
  demoD2 : D2 cls }.

Arguments demoD1 [d C] _ [s] _.
Arguments demoD2 [d C] _ [s] _.

Canonical demo_predType := mkPredType (fun (S : demo) (C : clause) => nosimpl C \in cls S).

Lemma LCF (S : demo) C : C \in S ->
  ((fF^+ \in C) = false) * (forall p, (fV p^+ \in C) && (fV p^- \in C) = false).
Proof.
  move/demoD0 => /andP [/negbTE-> /allP H]. split => // p.
  case e: (_^+ \in _) => //=. by rewrite (negbTE (H _ e)).
Qed.

(** ** Model Existence *)

Section ModelExistience.
  Variables (S : demo).

  Definition Mtype := seq_sub S.
  Definition Mtrans : rel Mtype := restrict S rtrans.
  Definition Mlabel (p:var) (C : Mtype) := fV p^+ \in val C.

  Definition model_of := FModel Mtrans Mlabel.

  Implicit Types (x y : model_of).

  Lemma supp_eval s x : val x |> s -> eval (interp s) x.
  Proof.
    case: s x. elim => [|p|s IHs t IHt|s IHs|s IHs] [|] x.
    - by rewrite /= (LCF (ssvalP x)).
    - by rewrite /=. 
    - done.
    - rewrite /= /Mlabel. case: (LCF (ssvalP x)) => [_ /(_ p)].
      by case: (_^+ \in _) => //= ->.
    - rewrite /=. case/orP => [/IHs|/IHt] /=; tauto.
    - rewrite /=. case/andP => [/IHs ? /IHt] /=; tauto.
    - move => inX y xy. apply: (IHs true).
      rewrite -suppC1. apply: suppC_sub xy. by rewrite fsub1 RE.
    - rewrite [_ |> _]/= => H. case/hasP : (demoD1 (ssvalP x) H) => D inS.
      rewrite suppCU suppC1 => /andP [D1 D2] /= /(_ (Sub D inS)) /(_ D2).
      exact: (IHs false).
    - move: x. cofix supp_eval => x. rewrite [_ |> _]/= => /andP [X1 X2].
      apply: AGs => [|y xy]; [exact: IHs X1|apply: supp_eval].
      rewrite -suppC1. apply: suppC_sub xy. by rewrite fsub1 RE.
    - move => H. apply: cAG_cEF. apply: EF_strengthen (IHs false) _. 
      move: H. rewrite [_ |> _]/=. case/orP => [?|]; first exact: EF0.
      move/(demoD2 (ssvalP x)). case: x => C inS supp. rewrite /= in supp.
      elim: supp inS => {C} C D DinS CD.
      + move => Ds inS. apply: (EFs (v := Sub D DinS)) => //. exact: EF0.
      + move => _ IH inS. apply: (EFs (v := Sub D DinS)) => //. exact: IH.
  Qed.

End ModelExistience.

(** ** Pruning *)

Section Pruning.
  Variables (F : clause).
  Hypothesis sfc_F : sf_closed F.

  Definition U := powerset F.
  Definition S0 := [fset C in U | literalC C && lcons C].

  (** To construct the pruning demo, we need to decide the fulfillment
  relations. For this we again use a fixpoint computation *)

  Definition fulfillAG_fun s S X : {fset clause} :=
    [fset C in S | [some D in S, rtrans C D && ((D |> s^-) || (D \in X))]].

  Lemma fulfillAG_fun_mono s S : monotone (fulfillAG_fun s S).
  Proof.
    move => X Y /subP XsubY.
    apply: sep_sub (subxx _) _ => C inS. apply: sub_has => D.
    case: (_ C D) => //=. case: (D |> s^-) => //=. exact: XsubY.
  Qed.

  Lemma fulfillAG_fun_bounded s S : bounded S (fulfillAG_fun s S).
  Proof. move => *. exact: subsep. Qed.
                                                               
  Definition fulfillAGb s S := fset.lfp S (fulfillAG_fun s S).

  Lemma fulfillAGE s S C :
    (C \in fulfillAGb s S) = (C \in fulfillAG_fun s S (fulfillAGb s S)).
  Proof.
    by rewrite /fulfillAGb {1}(fset.lfpE (fulfillAG_fun_mono s S) (@fulfillAG_fun_bounded s S)).
  Qed.

  Lemma fulfillAGP s S C : reflect (C \in S /\ fulfillAG S s C) (C \in fulfillAGb s S).
  Proof.
    apply: (iffP idP).
    - move: C. apply: fset.lfp_ind => C X IH /sepP[-> /hasP[D inS] /andP[CD]].
      case/orP => H; split => //; first exact: fulfillAG1 H.
      apply: fulfillAGn CD _ => //. by apply IH.
    - case => inS H. elim: H inS => {C} C D DinS CD.
      + move => Ds CinS. rewrite fulfillAGE inE CinS andTb.
        by apply/hasP; exists D; bcase.
      + move => _ /(_ DinS) HD CinS. rewrite fulfillAGE inE CinS andTb.
        by apply/hasP; exists D; bcase.
  Qed.

  Definition P1 C S := ~~ [all u in C, if u is fAX s^- then suppS S (s^- |` R C) else true].
  Definition P2 C S := ~~ [all u in C, if u is fAX (fAG s)^- then C \in fulfillAGb s S else true].
  Definition pcond C S := P1 C S || P2 C S.

  (** Pruning yields a demo *)

  Lemma prune_D0 : D0 (prune pcond S0).
  Proof. move => C. move/(subP (prune_sub _ _)). rewrite inE. bcase. Qed.

  Lemma prune_D1 : D1 (prune pcond S0).
  Proof.
    move => C /pruneE. rewrite negb_or => /andP [P _ s inC]. rewrite negbK in P.
    by move/allP : P => /(_ _ inC). 
  Qed.

  Lemma prune_D2 : D2 (prune pcond S0).
  Proof.
    move => C /pruneE. rewrite negb_or => /andP [_ P s inC]. rewrite negbK in P.
    move/allP : P => /(_ _ inC) /fulfillAGP. tauto.
  Qed.

  Definition DD := Demo prune_D0 prune_D1 prune_D2.

  (** ** Refutation Predicates and corefutability of the pruning demo *)

  Definition coref (ref : clause -> Prop) S :=
    forall C, C \in S0 `\` S -> ref C.

  Inductive ref : clause -> Prop :=
  | R1 S C : C \in U -> coref ref S -> ~~ suppS S C -> ref C
  | R2 C s : ref (s^- |` R C) -> ref (fAX s^- |` C)
  | R3 S C s : S `<=` S0 -> coref ref S -> 
                 C \in S -> fAX (fAG s)^- \in C -> ~ fulfillAG S s C -> ref C.

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
    case/orP.
    - case/allPn. (do 2 case) => // s [//|] inC nS inS corefS subS0.
      apply: corefD1 (corefS). 
      rewrite (fset1U inC). apply R2 => //. apply: R1 nS => //.
      move/(subP subS0)/(subP subsep): inS => inU. exact: R1inU.
    - move => H inS corefS ?. apply: corefD1 (corefS).
      case/allPn :H. (do 3 case) => // s [//|] inC. move/(elimN (fulfillAGP _ _ _)) => H.
      apply: R3 (inS) inC _ => //. tauto.
  Qed.

  Lemma DD_refute C : C \in U -> ~~ suppS DD C -> ref C.
  Proof. move => inU. apply: R1 inU _  => //. exact: coref_DD. Qed.

End Pruning.

(** ** Refutation Correctness *)

Definition sat (M:cmodel) C := exists (w:M), forall s, s \in C -> eval (interp s) w.

Theorem pruning_completeness F (sfc_F : sf_closed F) C :
  C \in U F -> ref F C + exists2 M:fmodel, sat M C & #|{: M}| <= 2 ^ size F.
Proof.
  move => inU. case: (boolP (suppS (DD F) C)) => H; [right|left; exact: DD_refute].
  - exists (model_of (DD F)).
    case/hasP : H => D D1 D2. exists (SeqSub _ D1) => s /(allP D2) ?. exact: supp_eval.
  - rewrite card_seq_sub ?funiq // -powerset_size subset_size // /DD /=.
    exact: sub_trans (prune_sub _ _) (subsep).
Qed.

