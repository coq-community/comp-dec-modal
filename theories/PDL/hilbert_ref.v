(* (c) Copyright Christian Doczkal and Joachim Bard                       *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations Omega.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs Require Import edone bcase fset base modular_hilbert.
From CompDecModal.PDL Require Import PDL_def demo.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D : clause).

(** * Hilbert Refutations *)

Section HilbertRef.
  Variable (F : {fset form}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation PU := (PU F).
  Local Notation xaf := (fun C => [af C]).

  Definition href C := prv ([af C] ---> Bot).

  Lemma refI1n s C : prv ([af C] ---> s) -> href (s^- |` C).
  Proof. 
    move => H. rewrite /href. rewrite -> andU,H,bigA1,axAC. 
    rule axAcase. exact: axContra.
  Qed.

  Lemma refE1n s C : href (s^- |` C) -> prv ([af C] ---> s).
  Proof.
    move => H. rewrite /href in H. rewrite -> andU,bigA1 in H. 
    Intro. ApplyH axDN. Intro. ApplyH H. by ApplyH axAI.
  Qed.

  Lemma ax_lcons C : ~~ lcons C -> prv ([af C] ---> Bot).
  Proof.
    rewrite negb_and -has_predC negbK.
    case/orP => [inC|/hasP [s sinC /=]].
    - rewrite -> (bigAE _ inC). exact: axI.
    - rewrite negbK => nsinC.
      rewrite -> (axA2 [af C]). rewrite -> (bigAE _ sinC) at 2.
      rewrite -> (bigAE _ nsinC). simpl. rule axAcase. case: s sinC nsinC => s [|] _ _ /=.
      exact: axI. exact: axContra.
  Qed.

  Section ContextRefutations.
    Variable S : {fset clause}.
    Hypothesis sub_S : S `<=` S0.
    Hypothesis coref_S : coref F href S.

    (* Lemma 6.1 *)
    Lemma not_hint_max C : C \in PU -> maximal F C -> ~~ hintikka C -> prv ([af C] ---> Bot).
    Proof.
      move/powersetP => Csub /allP => M. 
      rewrite negb_and. case/orP; first exact: ax_lcons.
      case/allPn => s inC /=. move: (Csub _ inC). move/flip_drop_sign.
      case: s inC. case => [|x|s t|[a|p0 p1|p0 p1|p|s] t] [|] //= inC inF.
      - move: (sfc_F inF) => /=. case/andP => sinF tinF.
        rewrite negb_or. case/andP => /negbTE sninC /negbTE tninC. move: (M s sinF).
        rewrite sninC orbF => sinC. move: (M t tinF). rewrite tninC /= => tinC.
        do 2 rule axDup. rewrite -> (bigAE _ inC) at 1. rewrite -> (bigAE _ tinC) at 1.
        rewrite -> (bigAE _ sinC) => /=. exact: ax_contraNN.
      - move: (sfc_F inF) => /=. case/andP => sinF tinF. rewrite negb_and.
        case/orP => [/negbTE sninC | /negbTE tninC].
        + move: (M s sinF). rewrite sninC /= => sinC. rule axDup.
          rewrite -> (bigAE _ inC) at 1. rewrite -> (bigAE _ sinC). do 2 Intro. Apply* 1. Intro.
          rewrite <- (axBE t). by Apply* 1.
        + move: (M t tinF). rewrite tninC orbF => tinC. rule axDup. rewrite -> (bigAE _ inC) at 1.
          rewrite -> (bigAE _ tinC). do 2 Intro. Apply* 1. Intro. by Asm.
      - move: (sfc_F inF) => /=. case/and3P => inF0 inF1 _. rewrite negb_and.
        case/orP => [/negbTE ninC0 | /negbTE ninC1].
        + move: (M _ inF0). rewrite ninC0 /= => inC0. rule axDup. rewrite -> (bigAE _ inC0) at 1.
          rewrite -> (bigAE _ inC) => /=. rewrite -> axChEl. exact: axI.
        + move: (M _ inF1). rewrite ninC1 /= => inC1. rule axDup. rewrite -> (bigAE _ inC1) at 1.
          rewrite -> (bigAE _ inC) => /=. rewrite -> axChEr. exact: axI.
      - move: (sfc_F inF). case/and3P => inF0 inF1 _. rewrite negb_or.
        case/andP => /negbTE ninC0 /negbTE ninC1. move: (M _ inF0) (M _ inF1).
        rewrite ninC0 ninC1 !orbF => inC0 inC1. do 2 rule axDup. rewrite -> (bigAE _ inC0) at 1.
        rewrite -> (bigAE _ inC1) at 1. rewrite -> (bigAE _ inC) => /=.
        rewrite -> (axDNE [p0 + p1]t). exact: axCh.
      - move/negbTE => ninC. move: (sfc_F inF). case/andP => inF' _. move: (M _ inF').
        rewrite ninC /= => inC'. rule axDup. rewrite -> (bigAE _ inC') at 1.
        rewrite -> (bigAE _ inC) => /=. rewrite -> axConE. exact: axI.
      - move/negbTE => ninC. move: (sfc_F inF). case/andP => inF' _. move: (M _ inF').
        rewrite ninC orbF => inC'. rule axDup. rewrite -> (bigAE _ inC') at 2.
        rewrite -> (bigAE _ inC) => /=. rewrite <- axCon. exact: axI.
      - move: (sfc_F inF). case/andP => pinF sinF. rewrite negb_and.
        case/orP => [/negbTE sninC | /negbTE pninC].
        + move: (M _ sinF). rewrite sninC /= => sinC. rule axDup. rewrite -> (bigAE _ sinC) at 1.
          rewrite -> (bigAE _ inC) => /=. rewrite -> axStarEl. exact: axI.
        + move: (M _ pinF). rewrite pninC /= => pinC. rule axDup.
          rewrite -> (bigAE _ inC) at 2 => /=. rewrite -> axStarEr.
          rewrite -> (bigAE _ pinC) => /=. exact: axI.
      - move: (sfc_F inF). case/andP => pinF sinF. rewrite negb_or.
        case/andP => /negbTE sninC /negbTE pninC. move: (M _ pinF) (M _ sinF).
        rewrite sninC pninC !orbF => pinC sinC. do 2 rule axDup.
        rewrite -> (bigAE _ inC) at 3 => /=. rewrite -> (axDNE [p^*]t).
        rewrite -> (bigAE _ sinC) at 1. rewrite -> (bigAE _ pinC). exact: axStar.

      (* Essentially the same as the implication cases *)
      - move: (sfc_F inF) => /=. case/andP => sinF tinF.
        rewrite negb_or. case/andP => /negbTE sninC /negbTE tninC. move: (M s sinF).
        rewrite sninC orbF => sinC. move: (M t tinF). rewrite tninC /= => tinC.
        do 2 rule axDup. rewrite -> (bigAE _ inC) at 1. rewrite -> (bigAE _ tinC) at 1.
        rewrite -> (bigAE _ sinC) => /=. rewrite -> axTestE. exact: ax_contraNN.
      - move: (sfc_F inF) => /=. case/andP => sinF tinF. rewrite negb_and.
        case/orP => [/negbTE sninC | /negbTE tninC].
        + move: (M s sinF). rewrite sninC /= => sinC. rule axDup.
          rewrite -> (bigAE _ inC) at 1. rewrite -> (bigAE _ sinC). rewrite /=.
          rewrite <- axTestI. do 2 Intro. Apply* 1. Intro. rewrite <- (axBE t). by Apply* 1.
        + move: (M t tinF). rewrite tninC orbF => tinC. rule axDup. rewrite -> (bigAE _ inC) at 1.
          rewrite /=. rewrite <- axTestI. rewrite -> (bigAE _ tinC). do 2 Intro. Apply* 1. Intro. by Asm.
    Qed.

    Lemma bigxm C s : prv ([af C] ---> [af s^+ |` C] :\/: [af s^- |` C]).
    Proof.
      apply: (rMP (s := s :\/: ~~:s)); last exact: axI. rule axOE.
      - rewrite <- axOIl. do 2 Intro. apply: bigAI => t /fsetU1P [->|inC]; first by Asm.
        Rev. drop. exact: bigAE.
      - rewrite <- axOIr. do 2 Intro. apply: bigAI => t /fsetU1P [->|inC]; first by Asm.
        Rev. drop. exact: bigAE.
    Qed.

    Lemma extension0 C : C \in PU ->
      prv ([af C] ---> \or_(D <- [fset D in S0 | C `<=` D]) [af D]).
    Proof.
      rewrite powersetE. apply: (slack_ind (P := fun C => prv ([af C] ---> _))) => D IH sub.
      case (boolP (maximal F D)).
      - case (boolP (hintikka D)).
        + move => H M. apply: bigOI. by rewrite !inE powersetE sub H M /= subxx. 
        + move: sub. rewrite -powersetE => sub nH M. rewrite -> (not_hint_max sub M nH).
          exact: axBE.
      - case/allPn => s inF /=. rewrite negb_or. case/andP => sninD fsninD.
        rewrite -> (bigxm D s). rule axOE; (rewrite -> IH; last by rewrite fproper1).
        + apply: or_sub. move => E. rewrite !inE. case/andP => /and3P [-> -> ->] /=.
          by case/fsubUsetP.
        + rewrite fsubUset sub fsub1 /= andbT. apply/cupP. exists s. by rewrite inF !inE eqxx.
        + apply: or_sub. move => E. rewrite !inE. case/andP => /and3P [-> -> ->] /=.
          by case/fsubUsetP.
        + rewrite fsubUset sub fsub1 /= andbT. apply/cupP. exists s. by rewrite inF !inE eqxx.
    Qed.

    (* Lemma 6.2 (Extension) *)
    Lemma extension C : C \in PU ->
      prv ([af C] ---> \or_(D <- [fset D in S | C `<=` D]) [af D]).
    Proof.
      move => Csub. rewrite -> extension0 => //. apply: bigOE => D. rewrite !inE.
      case/andP => /and3P [Dsub M H] CsubD.
      case inS: (D \in S).
      - apply: bigOI. by rewrite !inE inS CsubD.
      - rewrite -> coref_S; first exact: axBE. by rewrite !inE Dsub M H inS.
    Qed.

    (* Lemma 6.3 (Admissibility of P1 *)
    Lemma adm_P1 C : C \in PU -> ~~ S |> C -> href C.
    Proof.
      rewrite /href => H1 H2. rewrite -> extension => //.
      apply: bigOE => D. rewrite inE => /andP [D1 D2]. case: notF.
      apply: contraNT H2 => _. by apply/hasP; exists D.
    Qed.

    Lemma nsub_contra C D :
      C \in S -> D \in S -> ~~ (C `<=` D) -> prv ([af C] ---> [af D] ---> fF).
    Proof.
      move => /(subP sub_S). rewrite inE powersetE. case/and3P => sub _ _.
      move/(subP sub_S). rewrite inE. case/and3P => _ _ /allP maxD. case/subPn.
      case => s [|]; move => inC ninD; move: (maxD s); rewrite (negbTE ninD) ?orbF /=;
      rewrite -> (bigAE _ inC); move: inC => /(subP sub) => inF;
      rewrite (flip_drop_sign inF) => inD; rule axC; (rewrite -> bigAE;
      last exact: inD); [done| by rule axC].
    Qed.
    
    (* Lemma 6.4 *)
    Lemma neq_contra C D : C \in S -> D \in S -> C != D -> prv ([af C] ---> [af D] ---> fF).
    Proof.
      move => CinS DinS. rewrite eqEsub negb_and.
      case/orP => H; [exact: nsub_contra | rule axC; exact: nsub_contra].
    Qed.

    (* Lemma 6.5 (1) *)
    Lemma or_S : prv (\or_(C <- S) [af C]).
    Proof.
      apply (rMP (s := [af fset0])).
      - rewrite -> extension; last by rewrite powersetE sub0x. apply: bigOE => C. rewrite inE.
        case/andP => inS _. exact: bigOI.
      - mp; last exact: axT. apply: bigAI => s. by rewrite inE.
    Qed.

    (* Lemma 6.5 (2) *)
    Lemma neg_or A : A `<=` S -> prv ((~~: \or_(C <- A) [af C]) ---> \or_(C <- S `\` A) [af C]).
    Proof.
      move => sub. mp; last exact: or_S. apply: bigOE => C inS. case inA: (C \in A).
      - rewrite <- (bigOI _ inA). exact: axContra.
      - rule axC. drop. apply: bigOI. by rewrite inE inS inA.
    Qed.

    Lemma maxS0 C s b : C \in S -> (s,b) \notin C -> s \in F -> (s,~~ b) \in C.
    Proof. 
      move/(subP sub_S). rewrite inE => /and3P[_ _ /allP] H inC /H.
      case: b inC => /negbTE-> //=. by rewrite orbF.
    Qed.

    Ltac adm_P2_aux_tac := 
      try match goal with 
            [ Hu : is_true (_ \in F) |- _] => 
              by [move/sfc_F : Hu => /and3P[]|move/sfc_F : Hu => /andP[]]
          end.

    (* Lemma 6.7 *)
    Lemma adm_P2_aux C D p u : [p]u \in F -> 
      C \in S -> D \in S -> ~~ reach_demo S p C D -> prv ([af C] ---> [p]~~:[af D]).
    Proof with adm_P2_aux_tac.
      elim: p u C D => [a|p0 IH0 p1 IH1|p0 IH0 p1 IH1|p IHp|s] u C D Hu CinS DinS /=.
      - rewrite -has_predC. case/hasP. case => s [|]; last by rewrite (negbTE (Rpos _ _ _)).
        rewrite RE /= => inC ninD.
        have inD : s^- \in D.
        { apply: maxS0 DinS ninD _. move: CinS => /(subP sub_S).
          rewrite inE powersetE. case/and3P => /subP sub _ _.
          apply: (@flip_drop_sign _ (s^+)).
          apply: flipcl_refl. move/sub : inC. by move/flip_drop_sign/sfc_F. }
        rewrite <- (axDN ([pV a](~~: [af D]))).
        rewrite -> (dmAX (pV a) (~~: [af D])). rewrite -> rEXn; last exact: axDN.
        rewrite -> (bigAE _ inC). rewrite -> (rEXn (pV a) (t:= ~~: s)).
        + rule axC. do 2 Intro. rule axB; last by do 2 Rev; exact: axDBD.
          rewrite -> rEXn; first exact: axnEXF. rewrite -> (axDNE (~~: s ---> ~~: s)). exact: axI.
        + rewrite -> bigAE; last exact: inD. exact: axI. 
      - rewrite negb_or. case/andP => H0 H1. rewrite <- axDup. rewrite -> (IH0 u) at 1 => //...
        rewrite -> (IH1 u C D) => //... exact: axCh. 
      - rewrite -all_predC. move/allP => H. rewrite <- axCon.
        rewrite <- (axDN ([p0][p1](~~: [af D]))).
        rewrite -> (dmAX p0 ([p1](~~: [af D]))).
        rewrite -> (rEXn p0 (t:= (\or_(E <- S) [af E]) :/\: EX p1 [af D])); last
          by apply: (rMP _ or_S); exact: axAI.
        rewrite -> rEXn; last by rewrite -> bigODr; exact: axI. rewrite -> bigEOOE.
        rule axC. apply: bigOE => E inS. move: (H E inS) => /=. rewrite negb_and.
        case/orP => [H0|H1].
        + rewrite -> (IH0 [p1]u C E) => //... do 2 Intro. rule axB; last by do 2 Rev; exact: axDBD.
          rewrite -> rEXn; first exact: axnEXF. do 2 rule axAcase. rule axC. drop.
          exact: axContra. 
        + rule axC. drop. rewrite -> rEXn; first exact: axnEXF.
          rule axDup. rewrite -> axAEl at 2. rewrite -> axAEr. rewrite -> (IH1 u E D) => //...
      - move => H.
        set I := [fset E in S | reach_demo S (p^*) C E].
        set v := \or_(E <- I)[af E].
        suff X : prv (v ---> [p]v). 
        { Cut v; first by apply: bigOI;rewrite !inE CinS /= connect_in0.
          rewrite -> (rStar_ind' X). apply: rNorm. apply: bigOE => E inI.
          apply: neq_contra => //; first by apply/(subP subsep); exact: inI.
          apply: contraTN inI => /eqP->. by rewrite inE DinS /= (negbTE H). }
        rewrite /v. rewrite <- (axDN ([p](\or_(E<-I) [af E]))), -> (dmAX p (\or_(E<-I) [af E])).
        apply: bigOE => E EinI. rewrite -> rEXn; last by apply: neg_or; exact: subsep.
        rewrite -> bigEOOE. rule axC. apply: bigOE => G GninI. rewrite -> (IHp [p^*]u E G) => //... 
        * apply: (subP subsep). exact: EinI.
        * apply: (subP (fsubDl _ _)). exact: GninI.
        * apply/negP => ERG. move: GninI. rewrite inE. case/andP => GinS. apply/negP.
          apply/negPn. rewrite inE GinS /=. apply: connect_in_trans. move: EinI.
          case/sepP => _ CE. exact: CE. apply: connect_in1 => //. apply: (subP subsep).
          exact: EinI.
      - rewrite <- axTestI. case: (boolP (C == D)) => /= [/eqP-> A|].
        + suff X : s^- \in D. { rewrite -> (bigAE _ X) => /=. do 3 Intro. by Apply. }
          move/sfc_F : Hu => /andP [B _]. exact: (maxS0 DinS A).  
        + move => A _. do 3 Intro. by ApplyH (neq_contra CinS DinS A).
    Qed.

    Lemma sfc_box p s : [p]s \in F -> s \in F.
    Proof. by case: p => [a|p1 p2|p1 p2|p|t] /sfc_F => /=; case:(s \in F); rewrite ?andbF. Qed.

    (* Lemma 6.8 (Admissibility of P2 *)
    Lemma adm_P2 C p s :
      C \in S -> [p]s^- \in C -> ~~[some D in S, reach_demo S p C D && (s^- \in D)]
        -> href C.
    Proof.
      move => inS inC. rewrite -all_predC. move/allP => nR.
      set X := [fset D in S | [fset s^-] `<=` D].
      have AAX: prv ([af C] ---> [p]\and_(D <- X) ~~:[af D]).
      { rewrite <- bigABBA. apply: bigAI => D. rewrite inE fsub1. case/andP => DinS inD.
        apply: (adm_P2_aux (u := s)) => //. 
        - move/(subP sub_S) : inS inC. 
          by rewrite inE powersetE => /andP [/subP H _] /H /flip_drop_sign.
        - move: (nR D DinS) => /=. by rewrite negb_and inD orbF.
      }
      have EOX: prv ([af C] ---> EX p (\or_(D <- X) [af D])).
      { rewrite <- rEXn; first by rewrite <- dmAX; exact: (bigAE _ inC).
        rewrite /X. rewrite <- (extension (C:= [fset s^-])).
        - apply: bigAI => t. rewrite inE. move/eqP => -> /=. exact: axI.
        - rewrite powersetE fsub1. apply: flipcl_refl.
          move/(subP sub_S) : inS inC. 
          by rewrite inE powersetE => /andP [/subP H _] /H /flip_drop_sign /sfc_box.
      }
      rule axDup. rewrite -> EOX at 1. rewrite -> AAX. do 2 Intro.
      rule axB; last by do 2 Rev; exact: axDBD.
      rewrite -> rEXn; first exact: axnEXF.
      rewrite <- (axAcase (\or_(D<-X) [af D]) (\and_(D<-X) ~~: [af D]) Bot).
      apply: bigOE => D inX. rule axC. exact: bigAE.
    Qed.

  End ContextRefutations.

  (* Lemma 6.9 *)
  Theorem href_of C : pref F C -> href C.
  Proof. elim => *;[ apply: adm_P1 | apply: adm_P2 ]; eassumption. Qed.
 
End HilbertRef.

(** ** Completeness *)

(* Theorem 6.10 (Informative Completeness) *)
Theorem informative_completeness t : 
    prv (fImp t fF)
  + ({ M: fmodel & #|M| <= 2^(2 * sizef t) & { w: M | eval t w}}).
Proof.
  set F := FL t. have sfc_s := @FL_closed t.
  case: (@pruning_completeness F _ [fset t^+]) => //.
  - by rewrite powersetE fsub1 flipcl_refl // FL_refl.
  - move => /href_of H. left. rewrite /href in H. rewrite <- H => //. apply: bigAI => u.
    by rewrite inE => /eqP ->.
  - move => H. right. move: H => [M] [w] /(_ (t^+) (fset11 _)) /= ? S.
    exists M; last by exists w.
    apply: leq_trans S _. by rewrite leq_exp2l ?leq_mul ?FL_size.
Qed.

(** ** Main Results *)

(* Corollary 6.11 *)
Corollary completeness s : valid s -> prv s.
Proof.
  case: (informative_completeness (~~: s)) => [H|[M] _ [w] H] V.
  - by rule axDN.
  - exfalso. apply: H. exact: (V (cmodel_of_fmodel M)).
Qed.

(* Corollary 6.12 (Decidability) *)
Corollary prv_dec s : decidable (prv s).
Proof.
  case: (informative_completeness (~~: s)) => H; [left|right].
  - by rule axDN. 
  - move => prv_s. case: H => M _ [w]. apply. exact: (@soundness _ prv_s M).
Qed.

Corollary sat_dec s : decidable (exists (M: cmodel) (w: M), eval s w).
Proof.
  case: (informative_completeness s) => H; [right|left].
  - case => M [w] Hw. exact: (@soundness _ H M).
  - case: H => M _ [w] ?. by exists M; exists w.
Qed.

Corollary valid_dec s : decidable (forall (M: cmodel) (w: M), eval s w).
Proof.
  case (sat_dec (fImp s fF)) => /= H; [by firstorder|left => M w].
  apply: modelP => A. apply: H. by exists M;exists w.
Qed.

(* Corollary 6.13 (Small-Model Property) *)
Corollary small_models s:
  (exists (M: cmodel) (w: M), eval s w) ->
  (exists2 M: fmodel, #|M| <= 2^(2 * sizef s) & exists w: M, eval s w).
Proof.
  case: (informative_completeness s); last by firstorder.
  move => /(soundness) H [M] [w] w_s. exfalso. exact: H w_s.
Qed.
