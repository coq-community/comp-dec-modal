(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.
Require Import K_def demo.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (S X Y : {fset clause}) (C D E : clause).

(** * Gentzen System for K *)

(** Definition of the Rules *)

Inductive gen : clause -> Prop :=
| gen_F C :
    gen (fF^+ |` C)
| gen_p p C :
    gen ([fset fV p^+ , fV p^-  & C])
| gen_Ip s t C :
    gen (s^- |` C) -> gen (t^+ |` C) -> gen (fImp s t^+ |` C)
| gen_In s t C :
    gen ([fset s^+ , t^- & C]) -> gen (fImp s t^- |` C)
| gen_AXn s C :
    gen (s^- |` R C) -> gen (fAX s^- |` C)
.

(** Soundness *)

Theorem gen_hsound C : gen C -> prv ([af C] ---> Bot).
Proof.
  elim => {C} [C|p C|s t C _ IHs _ IHt|s t C _ IH|s C _ IH] /=.
  - rewrite -> andU,afp1. exact: axAEl.
  - rewrite -> andU,andU,afp1,afn1.
    rule axAcase. Intro. ApplyH axAcase. do 2 Intro. Apply* 1.
  - rewrite -> andU,afp1. rewrite -> andU,<- af1n in IHs. rewrite -> andU,<- af1p in IHt.
    rule axAcase. do 2 Intro. ApplyH IHs. ApplyH axAI.
    Intro. ApplyH IHt. ApplyH axAI. Apply* 2.
  - rewrite -> andU,afn1,dmI,axAA. by rewrite -> andU,->andU, <- af1n, <-af1p in IH.
  - rewrite <- axDF, -> andU, -> (afn1 (fAX s)).
    rewrite <- (modular_hilbert.axDN s), -> box_request.
    rewrite -> andU,<- af1n in IH. rewrite <- IH. rule axAcase. exact: axDBD.
Qed.

Lemma gen_ref_sound C : gen C -> ~ (exists M : cmodel, sat M C).
Proof. move => H. apply: href_sound. exact: gen_hsound. Qed.

(** ** Refutation Completeness  *)

Section RefPred.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation U := (U F).
  Local Notation xaf := (fun L => [af L]).

  Lemma lcons_gen C : ~~ lcons C -> gen C.
  Proof.
    rewrite /lcons negb_and negbK. case/orP => [H|/allPn[s]].
    - rewrite (fset1U H). by constructor.
    - case: s => [[|n|s t|s]] [|] //. rewrite negbK => H1 H2.
      rewrite (fset1U H1) (fset1U H2). by constructor.
  Qed.

  Ltac Lsupp1 := by rewrite /= ?fsubUset !fsub1 !inE // !ssub_refl.
  Ltac Lsupp2 := rewrite /weight /= ?fsumU !fsum1 /= /sltype.f_weight /= -?(plusE,minusE); apply/leP; lia.
  Ltac Lsupp3 := move => L; rewrite /= ?suppCU !suppC1 /=; by bcase.

  Lemma ref_R0 C : C \in U -> (forall D, D \in base S0 C -> gen D) -> gen C.
  Proof.
    move: C. apply: @nat_size_ind _ _ (@weight _) _ => C IH inU.
    case: (posnP (weight C)) => [/weight0 lC |/weightS wC] B.
    - case (boolP (lcons C)) => L; last exact: lcons_gen.
      apply B. rewrite !inE suppxx; bcase.
    - have H (s : sform) (D : clause) :
        s \in C -> D `<=` (ssub s) -> (weight D < s_weight s) ->
        (forall E, suppC E D -> E |> s) -> gen (D `|` (C `\` [fset s])).
        move => inC sub_s wD sDs. apply IH.
        - by apply: fsum_replace; rewrite ?fsum1 ?fsub1.
        - rewrite powersetU [_ `\` _ \in _](@sub_power _ _ C) // andbT powersetE.
          apply: sub_trans sub_s _. apply: sf_ssub => //.
          rewrite powersetE in inU. exact: (subP inU).
        - move => E. rewrite !inE suppCU => /and3P [C1 C2 C3].
          apply: B. rewrite !inE C1 /=. apply: suppCD C3. by rewrite suppC1 /= sDs.
      case/allPn : (wC). move => [[|p|s t|s] [|]] // inC _ ; rewrite -(fsetUD1 inC);
        by constructor;rewrite ?fsetUA; (apply H => //; [Lsupp1|Lsupp2|Lsupp3]).
  Qed.

  Lemma ref_coref S C : C \in U -> coref F gen S -> 
    (forall D, D \in base S C -> gen D) -> gen C.
  Proof.
    move => inU corefS baseP. apply: ref_R0 inU _ => D /sepP [D1 D2].
    case: (boolP (D \in S)) => H; first by apply: baseP; rewrite inE H.
    apply: corefS. by rewrite inE D1.
  Qed.

  Lemma ref_R1 S C : C \in U -> coref F gen S -> ~~ suppS S C -> gen C.
  Proof.
    move => inU coS sSC. apply: ref_R0 => // D. rewrite inE => /andP[D1 D2].
    apply: coS. rewrite inE D1 /=. apply: contraNN sSC => ?. by apply/hasP; exists D.
  Qed.
  
  Lemma ref_R2 C s : gen (s^- |` R C) -> gen (fAX s^- |` C).
  Proof. by constructor. Qed.

  Lemma gen_of_ref C : ref F C -> gen C.
  Proof. elim => *;[ apply: ref_R1 | apply: ref_R2]; eassumption. Qed.

End RefPred.

Lemma ex_fc (P : cmodel -> Prop) : (exists M : fmodel, P M) -> (exists M : cmodel, P M).
Proof. move => [M ?]. by exists M. Qed.

Theorem gen_completeness C : gen C + (exists M : fmodel, sat M C).
Proof.
  case: (@refutation_completeness (sfc C) (@closed_sfc C) C) => // [?|H].
  - left. exact: (gen_of_ref (@closed_sfc C)).
  - right. move: H => [M] [w] Hw _. by exists M; exists w. 
Qed.

Corollary gen_correctness C : gen C <-> ~ (exists M : cmodel, sat M C).
Proof.
  split; first exact: gen_ref_sound.
  case: (gen_completeness C) => // ? H. exfalso. apply H. exact: ex_fc.
Qed.

Corollary gen_dec C : decidable (gen C).
Proof.
  case: (gen_completeness C) => [|H]; first by left.
  right => /gen_correctness. apply. exact: ex_fc.
Qed.
