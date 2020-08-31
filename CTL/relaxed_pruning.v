(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base sltype.
Require Import CTL_def dags demo.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D L : clause) (S : {fset clause}).

Arguments prune_sub {T p S}.
Prenex Implicits prune_sub.

(** * Pruning *)

Section Prune.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Definition U := powerset F.
  Definition S0 := [fset L in U | literalC L && lcons L].

  Lemma Fsub s t X : t \in ssub s -> s \in X -> X \in U -> t \in F.
  Proof.
    move => Hsub sX XU. rewrite powersetE in XU.
    have/(sf_ssub sfc_F)/subP : s \in F by exact: (subP XU).
    by apply.
  Qed.

  Lemma ReqU L C : L \in U -> C \in Req L -> C \in U.
  Proof.
    move => inU. rewrite !inE. case/predU1P => [->|]; first by rewrite RinU.
    case/fimsetP => s. rewrite inE andbC. move: s => [[|p|? ?|s|? ?|? ?] [|]] //= inL ->.
    rewrite powersetU RinU // andbT powersetE fsub1.
    apply: Fsub inL inU. by rewrite /= !inE ssub_refl.
  Qed.

  Lemma SsubU S : S `<=` S0 -> {subset S <= U}.
  Proof. move => sub_S. apply/subP. apply: sub_trans sub_S _. exact: subsep. Qed.

  Definition pAXn L S :=
    [some C in Req L, ~~ suppS S C].
  Definition pAU C S :=
   [some u in C, if u is fAX (fAU s t)^+ then ~~ fulfillsAU S S0 s t C else false].
  Definition pAR C S :=
   [some u in C, if u is fAX (fAR s t)^- then ~~ fulfillsAR S S0 s t C else false].

  Definition pcond L S := [|| pAXn L S, pAU L S | pAR L S].

  Definition DD := prune pcond S0.

  (** ** Pruning yields a demo  *)

  Definition subDD : {subset DD <= U}.
  Proof. apply: SsubU. exact: prune_sub. Qed.

  Lemma AXn_complete_DD : AXn_complete DD.
  Proof.
    move => L C /pruneE. rewrite !negb_or. case/and3P => [/hasPn H _ _] /H {H L}.
    rewrite negbK. case/hasP => L ? ?. by exists L; bcase.
  Qed.

  Lemma fulfillsAU_DD s t L : L \in DD -> fAX (fAU s t)^+ \in L -> fulfillsAU DD S0 s t L.
  Proof.
    move => inDD inL.
    move: (inDD)  => /pruneE. rewrite !negb_or. case/and3P => [_ H _].
    move/hasPn : H => /(_ _ inL). by rewrite negbK.
  Qed.

  Lemma fulfillsAR_DD s t L : L \in DD -> fAX (fAR s t)^- \in L -> fulfillsAR DD S0 s t L.
  Proof.
    move => inDD inL.
    move: (inDD)  => /pruneE. rewrite !negb_or. case/and3P => [_ _ H].
    move/hasPn : H => /(_ _ inL). by rewrite negbK.
  Qed.

  Lemma demoDD_S0 : demo DD S0.
  Proof.
    have lc C : C \in S0 -> lcons C by rewrite inE; bcase.
    have sub : {subset DD <= S0} by apply/subP; exact: prune_sub.
    by split; auto using fulfillsAR_DD, fulfillsAU_DD,AXn_complete_DD.
  Qed.

  Lemma DD_size : size S0 <= 2^(size F).
  Proof. rewrite -powerset_size. apply: subset_size. exact: subsep. Qed.

  Lemma Fs_size : size (Fs DD) <= size F.
  Proof.
    apply : subset_size. apply/subP => s. case/cupP => C /and3P[C1 _ C2].
    move/(subP prune_sub) : C1. rewrite inE => /and3P [H _ _].
    move: H. rewrite powersetE. by move/subP; apply.
  Qed.

  Lemma DD_small_model u L : u \in Fs DD -> L \in DD ->
    exists2 M : fmodel, #|M| <= size F * 2 ^ (2 * (size F) + 1)
                      & exists (w : M), forall s : sform, L |> s -> eval (interp' s) w.
  Proof.
    move => inFs inDD.
    case: (small_models inFs demoDD_S0) => M M1 M2.
    exists M; last exact: M2.
    apply: leq_trans M1 _.
    rewrite addn1 [2 ^ _]expnS expnM -mulnn expnMn.
    rewrite !mulnA. rewrite leq_mul ?DD_size // ?[_ * 2]mulnC -?mulnA ?leq_mul2l.
    by rewrite leq_mul ?DD_size ?Fs_size.
  Qed.

  Lemma DD_sat u L : u \in Fs DD -> L \in DD ->
    exists (M : fmodel) (w : M), forall s : sform, L |> s -> eval (interp' s) w.
  Proof. move => inFs inD. case: (DD_small_model inFs inD) => M _ ?. by exists M. Qed.

  (** ** Refutation Calculus *)

  Definition coref (ref : clause -> Prop) S :=
    forall C, C \in S0 `\` S -> ref C.

  Inductive ref : clause -> Prop :=
  | R1 S C : C \in U -> coref ref S -> ~~ suppS S C -> ref C
  | R2 C D : D \in Req C -> ref D -> ref C
  | R3 S C : S `<=` S0 -> coref ref S -> C \in S -> pAR C S -> ref C
  | R4 S C : S `<=` S0 -> coref ref S -> C \in S -> pAU C S -> ref C.

  Lemma corefD1 S C : ref C -> coref ref S -> coref ref (S `\` [fset C]).
  Proof.
    move => rC coS D. rewrite !in_fsetD negb_and andb_orr -in_fsetD negbK in_fset1.
    case/orP; first exact: coS. by case/andP => [_ /eqP->].
  Qed.

  Lemma coref_DD : coref ref DD.
  Proof.
    apply: prune_myind => [C|C S]; first by rewrite inE andbN.
    case/or3P.
    - case/hasP => D D1 D2 inS corefS H. apply: corefD1 (corefS).
      apply: R2 (D1) _ => //. apply: R1 D2 => //. apply: ReqU D1. exact: (SsubU H). 
    - move => H inS corefS ?. apply: corefD1 (corefS). exact: R4 H.
    - move => H inS corefS ?. apply: corefD1 (corefS). exact: R3 H.
  Qed.

  Lemma DD_refute C : C \in U -> ~~ suppS DD C -> ref C.
  Proof. move => inU. apply: R1 inU _  => //. exact: coref_DD. Qed.

End Prune.

(** ** Refutation Completeness *)

Theorem ref_compl (F C: clause) u (sfc_F : sf_closed F) (inhF : u \in F) (inU : C \in U F) : 
      (ref F C)
    + (exists2 M:fmodel, #|M| <= size F * 2 ^ (2 * size F + 1) &
       exists w:M, forall s, s \in C -> eval (interp' s) w).
Proof.
  case: (boolP (suppS (DD F) C)) => H; [right|left]; last exact: DD_refute.
  case: (fset0Vmem C) => [E|[s inC]];subst.
  - exists unit_model.
    + rewrite card_unit muln_gt0 expn_gt0 /= andbT. apply/size_gt0P. by exists u.
    + exists tt => s. by rewrite inE.
  - case/hasP : H => D D1 /allP H. move: (H _ inC)=>/suppE/emptyPn [v inD]. 
    have inFs : v \in Fs (DD F) by apply/cupP; exists D; bcase.
    case: (DD_small_model inFs D1) => M ? [w Hw]. exists M => //; exists w.
    move => t /H. exact: Hw.
Qed.
