(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.
Require Import Kstar_def demo.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (C D : clause).

(** * Hilbert Refutations *)

Arguments decomp_ab {_ _ _} _.

Section RefPred.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation U := (U F).
  Local Notation xaf := (fun C => [af C]).

  Definition ref C := prv ([af C] ---> Bot).

  Lemma refI1n s C : prv ([af C] ---> s) -> ref (s^- |` C).
  Proof. 
    move => H. rewrite /ref. rewrite -> andU,H,bigA1,axAC. 
    rule axAcase. exact: axContra.
  Qed.

  Lemma refE1n s C : ref (s^- |` C) -> prv ([af C] ---> s).
  Proof.
    move => H. rewrite /ref in H. rewrite -> andU,bigA1 in H. 
    Intro. ApplyH axDN. Intro. ApplyH H. by ApplyH axAI.
  Qed.

  Definition base0 C := [fset L in U | literalC L && suppC L C].


  Ltac Lbase_aux := move => D; rewrite !inE; (try case/orP) =>/eqP->.
  Ltac Lbase1 := Lbase_aux; by rewrite /= ?fsubUset ?fsub1 ?powersetE ?fsubUset ?fsub1 ?inE ?ssub_refl.
  Ltac Lbase3 := Lbase_aux; rewrite /weight /= ?fsumU !fsum1 /= /sltype.f_weight /= -?(plusE,minusE); apply/leP; lia.
  Ltac Lbase4 := move => L; Lbase_aux; by rewrite /sltype.supp /= ?suppCU ?suppC1 /=; bcase.

  Lemma base0P C : C \in U ->
     prv ([af C] ---> \or_(L <- base [fset D in U | literalC D] C) [af L]).
  Proof with try solve [Lbase1|Lbase3|Lbase4].
    apply: (@supp_aux _ ssub) => /= {C} ; last by move => ?; exact: sf_ssub.
    - move => [[|p|s t|s|s] [|]] //=; try exact: decomp_lit.
      + apply: (decomp_ab [fset [fset s^-]; [fset t^+]]) => /=...
        rewrite -[fImp s t]/(s ---> t). rewrite -> (axIO s t).
        rule axOE.
        * rewrite -> af1n. apply: (bigOI xaf). by rewrite !inE eqxx.
        * rewrite -> (af1p t) at 1. apply: (bigOI xaf). by rewrite !inE eqxx.
      + apply: (decomp_ab [fset [fset s^+; t^-]]) => /=...
        rewrite -[fImp s t]/(s ---> t). rewrite -> dmI.
        rewrite -> (af1p s),(af1n t), <- andU at 1.
        apply: (bigOI xaf). by rewrite inE.
      + apply: (decomp_ab [fset [fset s^+;fAX (fAG s)^+]]) => /=...
        rewrite -> axAGE at 1. rewrite -> (af1p s),(af1p (AX (AG s))), <- andU at 1.
        apply: (bigOI xaf). by rewrite !inE.
      + apply: (decomp_ab [fset [fset s^-]; [fset fAX (fAG s)^-]]) => /=...
        rewrite -> axAGEn. rewrite -> (af1n s),(af1n (AX (AG s))) at 1.
        rule axOE; apply: (bigOI xaf); by rewrite !inE eqxx.
  Qed.
        
  Lemma ax_lcons C : ~~ lcons C -> prv ([af C] ---> Bot).
  Proof.
    rewrite negb_and -has_predC negbK.
    case/orP => [inC|/hasP [[[] //= p [|] //]]].
    - rewrite -> (bigAE _ inC). exact: axI.
    - rewrite negbK => pP pN.
      rewrite -> (axA2 [af C]). rewrite -> (bigAE _ pP) at 2.
      rewrite -> (bigAE _ pN). simpl. rule axAcase. exact: axI.
  Qed.

  Lemma R2 C s : ref (s^- |` R C) -> ref (fAX s^- |` C).
  Proof.
    rewrite /ref. do 2 rewrite -> andU,bigA1. 
    rewrite -[_ (s^-)]/(~~: s) -[_ (fAX s^-)]/(~~: AX s) => H.
    rewrite -> dmAX,box_request.
    rewrite /=. rewrite <- axDF. rewrite <- H.
    rule axAcase. apply axDBD.
  Qed.

  Section ContextRefutations.
  Variable S : {fset clause}.
  Hypothesis sub_S : S `<=` S0.
  Hypothesis coref_S : coref F ref S.

  Lemma baseP C : C \in U ->
     prv ([af C] ---> \or_(D <- base S C) [af D]).
  Proof.
    move => inU. rewrite -> base0P => //.
    apply: bigOE => L. rewrite !inE andbC => /and3P [L1 L2 L3].
    case: (boolP (L \in S)) => LS; first by apply: (bigOI xaf); rewrite inE LS.
    case: (boolP (lcons L)) => LL; last by rewrite -> (ax_lcons LL); exact: axBE.
    have H : L \in S0 `\` S by rewrite !inE LS LL L2 L3.
    Intro. ApplyH axBE. Rev. exact: (coref_S H).
  Qed.

  Lemma R1 C : C \in U -> ~~ suppS S C -> ref C.
  Proof. 
    rewrite /ref => H1 H2. rewrite -> baseP => //.
    apply: bigOE => D. rewrite inE => /andP [D1 D2]. case:notF.
    apply: contraNT H2 => _. by apply/hasP; exists D.
  Qed.

  Lemma R3 C s : C \in S -> fAX (fAG s)^- \in C -> ~ fulfillAG S s C -> ref C.
  Proof.
    move => CinS inC nsupp_s. rewrite (fset1U inC). apply: refI1n.
    pose I := [fset D in S | D \notin fulfillAGb s S].
    pose u := \or_(D <- I) [af D].
    have IP D : D \in I -> ~~ suppS S (s^- |` R D) /\ {subset base S (R D) <= I}.
      case/sepP => inS. rewrite fulfillAGE inE inS /= => /hasPn H. split.
      + apply/hasPn => D' inS'. move: (H _ inS'). rewrite suppCU suppC1 /rtrans.
        by apply contraNN => /andP [-> ->].        
      + move => D' /sepP [D1 D2]. rewrite inE D1 /=. move: (H _ D1).
        rewrite /rtrans D2 /= negb_or. by case/andP.
    Cut u; first by apply: (bigOI xaf); rewrite inE CinS /=; apply/negP => /fulfillAGP; tauto.
    apply: rAGp_ind. apply: bigOE => D inI.
    rewrite -> box_request. apply: rNorm.
    have HR : R D \in U. 
      rewrite RinU //. rewrite inE in inI. case/andP : inI => /(subP sub_S) H _.
      rewrite inE /U in H. by case/and3P: H.
    ApplyH axAI.
    - rewrite -> baseP => //. apply: or_sub. by apply IP.
    - apply: refE1n. apply: R1; last by apply IP.
      rewrite powersetU HR powersetE fsub1 andbT.
      move/(subP sub_S) : CinS. rewrite inE => /and3P [X _ _].
      rewrite powersetE in X. move/(subP X) : inC. 
      move => /sfc_F /= /sfc_F /=. by case/andP => _ ->.
  Qed.  
     
  End ContextRefutations.

  Theorem href_of C : demo.ref F C -> ref C.
  Proof. elim => *;[ apply: R1 | apply: R2 | apply: R3]; eassumption. Qed.
 
End RefPred.

(** ** Completeness *)

Lemma prf_ref_sound C : prv ([af C] ---> Bot) -> ~ (exists M : fmodel, sat M C).
Proof.  move => H [M] [w] X. apply satA in X. exact: finite_soundness H M w X. Qed.

Theorem informative_completeness s : 
    prv (fImp s fF)
  + (exists2 M:fmodel, #|M| <= 2^(2 * f_size s) & exists w:M, eval s w).
Proof.
  set F := ssub (s^+). have ? := @sfc_ssub (s^+).
  case: (@pruning_completeness F _ [fset s^+]) => //.
  - by rewrite powersetE fsub1 ssub_refl.
  - move => /href_of H. left. rewrite /ref in H. rewrite <- af1p in H. exact: H.
  - move => H. right. move: H => [M] [w] /(_ (s^+) (fset11 _)) /= ? S.
    exists M; last by exists w.
    apply: leq_trans S _. by rewrite leq_exp2l ?size_ssub.
Qed.

Corollary prv_dec s : decidable (prv s).
Proof.
  case: (informative_completeness (~~: s)) => H;[left|right].
  - by rule axDN. 
  - move => prv_s. case: H => M _ [w]. apply. exact: (@soundness _ prv_s M).
Qed.

Corollary sat_dec s : decidable (exists (M:cmodel) (w:M), eval s w).
Proof.
  case: (informative_completeness s) => H;[right|left].
  - case => M [w] Hw. exact: (@soundness _ H M).
  - case: H => M _ [w] ?. by exists M; exists w.
Qed.

Corollary valid_dec s : decidable (forall (M:cmodel) (w:M), eval s w).
Proof.
  case (sat_dec (fImp s fF)) => /= H;[by firstorder|left => M w].
  by case (modelP s w); firstorder.
Qed.


(** ** Small Model Theorem *)

Corollary small_models s:
  (exists (M:cmodel) (w:M), eval s w) ->
  (exists2 M:fmodel, #|M| <= 2^(2 * f_size s) & exists w:M, eval s w).
Proof.
  case: (informative_completeness s) => // /(soundness) H [M] [w] w_s.
  exfalso. exact: H w_s.
Qed.
