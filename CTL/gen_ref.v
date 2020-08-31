(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base sltype.
Require Import CTL_def demo gen_def relaxed_pruning.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D L : clause) (S : {fset clause}).

(** * Completeness of the Gentzen System *)

(** ** Pruning Refutations to Gentzen derivations *)

Section RefPred.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation U := (U F).
  Local Notation xaf := (fun L => [af L]).

  Definition ref' C := gen (C,aVoid).

  Lemma lcons_gen C a : ~~ lcons C -> gen (C,a).
  Proof.
    rewrite /lcons negb_and negbK. case/orP => [H|/allPn[s]].
    - rewrite (fset1U H). by constructor.
    - case: s => [[|n|s t|s|s t|s t]] [|] //. rewrite negbK => H1 H2.
      rewrite (fset1U H1) (fset1U H2). by constructor.
  Qed.

  Ltac Lsupp1 := by rewrite /= ?fsubUset !fsub1 !inE // !ssub_refl.
  Ltac Lsupp2 := rewrite /weight /= ?fsumU !fsum1 /= /sltype.f_weight /= -?(plusE,minusE); apply/leP; lia.
  Ltac Lsupp3 := move => L; rewrite /= ?suppCU !suppC1 /=; by bcase.

  Lemma ref_R0 C a : C \in U -> (forall D, D \in base S0 C -> gen (D,a)) -> gen (C,a).
  Proof.
    move: C. apply: @nat_size_ind _ _ (@weight _) _ => C IH inU.
    case: (posnP (weight C)) => [/weight0 /= lC |/weightS wC] B.
    - case (boolP (lcons C)) => L; last exact: lcons_gen.
      apply B. rewrite !inE suppxx; bcase.
    - have H (s : sform) (D : clause) :
        s \in C -> D `<=` (ssub s) -> (weight D < s_weight s) ->
        (forall E, suppC E D -> E |> s) -> gen (D `|` (C `\` [fset s]),a).
        move => inC sub_s wD sDs. apply IH.
        - by apply: fsum_replace; rewrite ?fsum1 ?fsub1.
        - rewrite powersetU [_ `\` _ \in _](@sub_power _ _ C) // andbT powersetE.
          apply: sub_trans sub_s _. apply: sf_ssub => //.
          rewrite powersetE in inU. exact: (subP inU).
        - move => E. rewrite !inE suppCU => /and3P [C1 C2 C3].
          apply: B. rewrite !inE C1 /=. apply: suppCD C3. by rewrite suppC1 sDs.
          case/allPn : (wC). move => [[|p|s t|s|s t|s t] [|]] // inC _ ; rewrite -(fsetUD1 inC);
            try by constructor;rewrite ?fsetUA; (apply H => //; [Lsupp1|Lsupp2|Lsupp3]).
  Qed.

  Lemma ref_R1 C S : C \in U -> coref F ref' S -> ~~ suppS S C -> ref' C.
  Proof.
    move => inU coS sSC. apply: ref_R0 => // D. rewrite inE => /andP[D1 D2].
    apply: coS. rewrite inE D1 /=. apply: contraNN sSC => ?. by apply/hasP; exists D.
  Qed.

  Lemma ref_R2 C D a : D \in Req C -> gen (D,aR a) -> gen (C,a).
  Proof.
    case/fsetU1P => [->|]; first by constructor.
    case/fimsetP => u. rewrite inE andbC. case: (isDiaP _) => //= s -> inC -> H.
    rewrite (fset1U inC). by constructor.
  Qed.

  Lemma fulfillsAUEn s t S C : C \in S0 -> ~~ fulfillsAU S S0 s t C -> exists D,
    [/\ D \in Req C , ~~ suppS S (t^+ |` D) &
        forall E, E \in base S0 (s^+ |` D) -> ~~ fulfillsAU S S0 s t E].
  Proof.
    move => inS. rewrite /fulfillsAU {1}fulfillsAUE inE inS /=.
    case/allPn => D D1. rewrite negb_or => /andP [S1 /hasPn S2].
    exists D. split => // E. rewrite inE => /andP [E1 E2].
    move: (S2 _ E1). by rewrite E2.
  Qed.

  Lemma ref_R4_aux s t (sF : s^+ \in F) (tF : t^+ \in F) S H C :
    coref F ref' S -> H `<=` U -> C \in U -> ~~ suppS S (t^+ |` C) ->
    (forall E, E \in base S0 (s^+ |` C) -> ~~ fulfillsAU S S0 s t E) ->
    gen (C,aAU (s,t,H)).
  Proof.
    move => coS subU. move: H subU C. apply: slack_ind => H IH subU C inU C1 C2.
    case: (boolP (C \in H)) => HC; first by rewrite (fset1U HC); exact: gen_AUrep.
    apply: gen_AUh.
    - apply: ref_R1 C1 => //. by rewrite powersetU inU powersetE fsub1 tF.
    - apply: ref_R0 => [|E in_base]; first by rewrite powersetU inU powersetE fsub1 sF.
      move/C2 : (in_base) => E1. case/sepP : in_base => E2 E3.
      case : (fulfillsAUEn E2 E1) => D [D1 D2 D3].
      apply: ref_R2 (D1) _ => /=. apply: IH => //.
      + by rewrite fsubUset fsub1; bcase.
      + by rewrite fproper1.
      + apply: ReqU D1 => //. rewrite inE in E2. by bcase.
  Qed.

  Lemma ref_R4 S C : S `<=` S0 -> coref F ref' S -> C \in S -> pAU F C S -> ref' C.
  Proof.
    move => S1 S2 inS. case/hasP. do 3 case => //. move => s t [|//] C1 C2.
    move/(subP S1) : inS => C3.
    case (fulfillsAUEn C3 C2) => E [E1 E2 E3].
    apply: ref_R2 (E1) _ => /=.
    have inE': fAU s t^+ \in E. apply: (subP (Req_RC E1)). by rewrite RE.
    have inF: fAU s t^+ \in F.
      suff: E `<=` F by move/subP; apply.
      rewrite -powersetE. apply: ReqU E1 => //. by rewrite inE in C3; bcase.
    rewrite (fset1U inE'). apply: gen_AUfoc. apply: ref_R4_aux E2 _ => //.
    - move/sfc_F : inF => /=. by bcase.
    - move/sfc_F : inF => /=. by bcase.
    - apply: ReqU E1 => //. by rewrite inE in C3; bcase.
  Qed.

  Lemma fulfillsAREn s t S C : C \in S0 -> ~~ fulfillsAR S S0 s t C ->
    (exists2 D : clause, D \in Req C & ~~ suppS S D) \/
    ~~ suppS S (t^-|` R C) /\ forall E : clause, E \in base S0 (s^- |` R C) -> ~~ fulfillsAR S S0 s t E.
  Proof.
    move => inS. rewrite /fulfillsAR {1}fulfillsARE inE inS /=.
    rewrite negb_and negb_or. case/orP => [C1|/andP [C1 C2]].
    - by left; apply/allPn.
    - right. split => // E. rewrite inE => /andP [E1 E2].
    move/hasPn : C2 => /(_ E). rewrite E1 E2 //=. by auto.
  Qed.

  Lemma ref_R3_aux s t (sF : s^- \in F) (tF : t^- \in F) S H C :
    coref F ref' S -> H `<=` U -> C \in U -> ~~ suppS S (t^- |` C) ->
    (forall E, E \in base S0 (s^- |` C) -> ~~ fulfillsAR S S0 s t E) ->
    gen (C,aAR (s,t,H)).
  Proof.
    move => coS subU. move: H subU C. apply: slack_ind => H IH subU C inU C1 C2.
    case: (boolP (C \in H)) => HC; first by rewrite (fset1U HC); exact: gen_ARrep.
    apply: gen_ARh.
    - apply: ref_R1 C1 => //. by rewrite powersetU inU powersetE fsub1 tF.
    - apply: ref_R0 => [|E in_base]. by rewrite powersetU inU powersetE fsub1 sF.
      move/C2 : (in_base) => E1. case/sepP : in_base => E2 E3.
      case: (fulfillsAREn E2 E1) => [[D D1 D2]|[D1 D2]].
      + apply: ref_R2 (D1) _ => /=. apply: ref_R1 D2 => //. 
        apply: ReqU D1 => //. by rewrite inE in E2; bcase.
      + apply: gen_aAXR. apply: IH => //.
        + by rewrite fsubUset fsub1; bcase.
        + by rewrite fproper1.
        + apply: RinU _ => //. rewrite inE in E2. by bcase.
  Qed.

  Lemma ref_R3 S C : S `<=` S0 -> coref F ref' S -> C \in S -> pAR F C S -> ref' C.
  Proof.
    move => S1 S2 inS. case/hasP. do 3 case => //. move => s t [//|] C1 C2.
    move/(subP S1) : inS => C3.
    case: (fulfillsAREn C3 C2) => [[D D1 D2]|[C4 C5]].
    - apply: ref_R2 (D1) _. apply: ref_R1 D2 => //. 
      apply: ReqU D1 => //. by rewrite inE in C3; bcase.
    - rewrite (fset1U C1). apply: gen_AXn => /=. apply: gen_ARfoc.
      have/sfc_F/and3P [F1 F2 F3] : fAR s t^- \in F.
      { suff: C `<=` F. move/subP => /(_ _ C1). exact: sfc_F.
        rewrite -powersetE. by rewrite inE in C3; bcase. }
      apply: ref_R3_aux C5 => //.
      apply: RinU => //. by rewrite inE in C3; bcase.
  Qed.
      
  Theorem refpred_ref' C : ref F C -> ref' C.
  Proof.
    elim => *;
      [apply: ref_R1|apply: ref_R2|apply: ref_R3|apply: ref_R4]; eassumption.
  Qed.

End RefPred.

(** ** Completeness Theorem *)

Theorem gen_complete C :
  gen (C,aVoid) + (exists (M:fmodel) (w:M), forall s, s \in C -> eval (interp' s) w).
Proof.
  case: (fset0Vmem C) => [->|[s inC]].
  - right. exists unit_model. exists tt => s. by rewrite inE.
  - pose sf := @closed_sfc C.
    have in_sfc : s \in sfc C by exact: (subP (@sub_sfc _)).
    have inU : C \in U (sfc C) by rewrite powersetE sub_sfc. 
    case: (@ref_compl _ C _ sf in_sfc inU) => [ref_C|H];[left|right].
    + exact: refpred_ref' ref_C.
    + move: H => [M] _ [w] ?. by exists M; exists w.
Qed.
