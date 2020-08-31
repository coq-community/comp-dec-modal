(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import Relations Lia.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base modular_hilbert sltype.

Require Import Kstar_def demo hilbert_ref gen_def. 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Implicit Types (S X Y H : {fset clause}) (C D E : clause).

Definition AXn C := [fset s in C | isDia s].
Definition Req C := [fset body s |` R C | s <- AXn C].

(** The argument order for fulfillAG differs from the paper version since we want
the induction principle where [S0], [S], and [s] remain constant during the
proofs. *)

Inductive fulfillAG S0 S s C : Prop :=
| fulfillAG1 D :
    (forall E, E \in Req C -> suppS S E) ->
    D \in S -> rtrans C D -> D |> s^- -> fulfillAG S0 S s C
| fulfillAGn D :
    (forall E, E \in Req C -> suppS S E) -> 
    D \in S0 -> rtrans C D -> fulfillAG S0 S s D -> fulfillAG S0 S s C.

Section Decidability.
  Variables (S0 S : {fset clause}).

  (** To construct the pruning demo, we need to decide the fulfillment
  relations. For this we again use a fixpoint computation *)

  Definition fulfillAG_fun s X : {fset clause} :=
    [fset C in S0 | [all D in Req C, suppS S D] &&
      (suppS S (s^- |` R C) || [some D in S0, rtrans C D && (D \in X)])].

  Lemma fulfillAG_fun_mono s : monotone (fulfillAG_fun s).
  Proof.
    move => X Y /subP XsubY.
    apply: sep_sub (subxx _) _ => C inS.
    case: ([all _ in _ ,  _]) => //=. case: (suppS _ _ ) => //=.
    apply: sub_has => D. case: (_ C D) => //=. exact: XsubY.
  Qed.

  Lemma fulfillAG_fun_bounded s : bounded S0 (fulfillAG_fun s).
  Proof. move => *. exact: subsep. Qed.

  Definition fulfillAGb s := fset.lfp S0 (fulfillAG_fun s).

  Lemma fulfillAGE s C :
    (C \in fulfillAGb s) = (C \in fulfillAG_fun s (fulfillAGb s)).
  Proof.
    by rewrite /fulfillAGb {1}(fset.lfpE (fulfillAG_fun_mono s) (@fulfillAG_fun_bounded s)).
  Qed.

  Lemma fulfillAGP s C : reflect (C \in S0 /\ fulfillAG S0 S s C) (C \in fulfillAGb s).
  Proof.
    apply: (iffP idP).
    - move: C. apply: fset.lfp_ind=> C X IH /sepP [-> /andP[/allP A]].
      case/orP => /hasP [D inS] H; split => //.
      + move: H. rewrite suppCU suppC1 => /andP[H ?]. exact: fulfillAG1 H.
      + case/andP: H => CD H2. apply: fulfillAGn CD _ => //. by apply IH.
    - case => inS H.
      elim: H inS => {C} - C D Req DinS CD.
      + move => Ds CinS. rewrite fulfillAGE inE CinS andTb.
        apply/andP;split; first exact/allP.
        leftb. apply/hasP; exists D => //. by rewrite suppCU suppC1 /= Ds.
      + move => _ /(_ DinS) HD CinS. rewrite fulfillAGE inE CinS andTb.
        apply/andP;split; first exact/allP. rightb.
        apply/hasP; exists D => //. bcase.
  Qed.
End Decidability.

Lemma fulfillAG_Req S0 S s C : C \in fulfillAGb S0 S s -> (forall E, E \in Req C -> suppS S E).
Proof. by case/fulfillAGP => _ []. Qed.

Section Pruning.
  Variables (F : clause).
  Hypothesis sfc_F : sf_closed F.

  Definition U := powerset F.
  Definition S0 := [fset C in U | literalC C && lcons C].

  Definition P1 C S := ~~ [all D in Req C, suppS S D].
  Definition P2 C S := ~~ [all u in C, if u is fAX (fAG s)^- then C \in fulfillAGb S0 S s else true].
  Definition pcond C S := P1 C S || P2 C S.

  (** Pruning yields a demo *)

  Definition S := prune pcond S0.
  Let Fs := \bigcup_(C in S) C.

  Definition T := [fset C in S0 | [all D in Req C, suppS S D]].

  Arguments prune_sub {T p S}.

  Lemma prune_D0 : D0 (S `|` T).
  Proof.
    move => C H. suff: C \in S0 by rewrite !inE; bcase.
    case/fsetUP : H; by [move/(subP prune_sub)| case/sepP].
  Qed.

  Lemma prune_D1_strong C s : fAX s^- \in C -> C \in S `|` T -> suppS S (s^- |` R C).
  Proof.
    move => inC.
    have Req_s : (s^- |` R C) \in Req C. 
        apply/fimsetP; exists (fAX s^-) => //. by rewrite inE inC.
    case/fsetUP.
    - move/pruneE. rewrite negb_or => /andP [/negPn /allP P _]. exact: P.
    - by case/sepP => _ /allP /(_ _ Req_s). 
  Qed.
  
  Lemma prune_D1 : D1 (S `|` T).
  Proof.
    move => C inST s inC. apply: sub_has_dom (prune_D1_strong inC inST).
    exact/subP.
  Qed.

  Lemma prune_S_aux C s : C \in S -> fAX (fAG s)^- \in C -> fulfillAG S0 S s C.
  Proof.
    move => inS inC.
    move/pruneE : inS. rewrite negb_or => /andP [_ P]. rewrite negbK in P.
    move/allP : P => /(_ _ inC) /fulfillAGP. tauto.
  Qed.

  Lemma prune_D2_S C s : C \in S -> fAX (fAG s)^- \in C -> demo.fulfillAG (S `|` T) s C.
  Proof.
    move => inS inC. move: (prune_S_aux inS inC). elim.
    + move => {C inS inC} - C D _ D1 D2 D3.
      apply: demo.fulfillAG1 D2 D3. by rewrite inE D1.
    + move => {C inS inC} - C D _ inS0 CD IH1 IH2.
      apply: demo.fulfillAGn CD _ => //.
      apply/fsetUP;right. rewrite inE inS0. apply/allP. 
      apply: (@fulfillAG_Req S0 _ s D). exact/fulfillAGP.
  Qed.
    
  Lemma prune_D2 : D2 (S `|` T).
  Proof.
    move => C. case/fsetUP; first by move => *; exact: prune_D2_S.
    move => inT s inC.
    have inST : C \in S `|` T by rewrite inE inT.
    case/hasP : (prune_D1_strong inC inST) => D.
    rewrite suppCU suppC1 => D1 /andP [/= D2 D3].
    case/orP : D2 => Hs.
    - apply: demo.fulfillAG1 D3 _  => //. by rewrite inE D1.
    - apply: demo.fulfillAGn D3 _; first by rewrite inE D1.
      exact: prune_D2_S.
  Qed.
 
  Definition DD := @Demo (S `|` T) prune_D0 prune_D1 prune_D2.

  (** ** Refutation Predicates and corefutability of the pruning demo *)

  Definition coref (ref : clause -> Prop) S :=
    forall C, C \in S0 `\` S -> ref C.

  Inductive ref : clause -> Prop :=
  | R1 S C : C \in U -> coref ref S -> ~~ suppS S C -> ref C
  | R2 C s : ref (s^- |` R C) -> ref (fAX s^- |` C)
  | R3 S C s : S `<=` S0 -> coref ref S -> 
                 C \in S -> fAX (fAG s)^- \in C -> ~ fulfillAG S0 S s C -> ref C.

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

  Lemma coref_S : coref ref S.
  Proof.
    apply: prune_myind => [C|C S]; first by rewrite inE andbN.
    case/orP.
    - case/allPn => D. case/fimsetP => t /sepP [inC].
      case: (isDiaP t) inC => // s -> inC _ -> /= nS inS corefS subS0.
      apply: corefD1 (corefS). 
      rewrite (fset1U inC). apply R2 => //. apply: R1 nS => //.
      move/(subP subS0)/(subP subsep): inS => inU. exact: R1inU.
    - move => H inS corefS subS0. apply: corefD1 (corefS).
      case/allPn :H. (do 3 case) => // s [//|] inC. move/(elimN (fulfillAGP _ _ _ _)) => H.
      case: (boolP (C \in S0)) => [inS0|].
      + apply: R3 (inS) inC _ => //. tauto.
      + by move/(subP subS0) : inS => ->.
  Qed.

  Lemma S_refute C : C \in U -> ~~ suppS S C -> ref C.
  Proof. move => inU. apply: R1 inU _  => //. exact: coref_S. Qed.

End Pruning.



(** ** Refutation Completeness for History-Free Clauses *)

Section RefPred.
  Variable (F : {fset sform}).
  Hypothesis (sfc_F : sf_closed F).

  Local Notation S0 := (S0 F).
  Local Notation U := (U F).
  Local Notation xaf := (fun L => [af L]).

  Definition tref C := gen (C,aVoid).

  Lemma lcons_gen C a : ~~ lcons C -> gen (C,a).
  Proof.
    rewrite /lcons negb_and negbK. case/orP => [H|/allPn[s]].
    - rewrite (fset1U H). by constructor.
    - case: s => [[|n|s t|s|s]] [|] //. rewrite negbK => H1 H2.
      rewrite (fset1U H1) (fset1U H2). by constructor.
  Qed.

  Ltac Lsupp1 := by rewrite /= ?fsubUset !fsub1 !inE // !ssub_refl.
  Ltac Lsupp2 := rewrite /weight /= ?fsumU !fsum1 /= /sltype.f_weight /= -?(plusE,minusE); apply/leP; lia.
  Ltac Lsupp3 := move => L; rewrite /= ?suppCU !suppC1 /=; by bcase.

  Lemma tref_R0 C a : C \in U -> (forall D, D \in base S0 C -> gen (D,a)) -> gen (C,a).
  Proof.
    move: C. apply: @nat_size_ind _ _ (@weight _) _ => C IH inU.
    case: (posnP (weight C)) => [/weight0 lC |/weightS wC] B.
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
          apply: B. rewrite !inE C1 /=. apply: suppCD C3. by rewrite suppC1 /= sDs.
      case/allPn : (wC). move => [[|p|s t|s|s] [|]] // inC _ ; rewrite -(fsetUD1 inC);
        constructor;rewrite ?fsetUA; (apply H => //; [Lsupp1|Lsupp2|Lsupp3]).
  Qed.

  Lemma tref_R1 S C : C \in U -> coref F tref S -> ~~ suppS S C -> tref C.
  Proof.
    move => inU coS sSC. apply: tref_R0 => // D. rewrite inE => /andP[D1 D2].
    apply: coS. rewrite inE D1 /=. apply: contraNN sSC => ?. by apply/hasP; exists D.
  Qed.
  
  Lemma tref_R2 C s : tref (s^- |` R C) -> tref (fAX s^- |` C).
  Proof. by constructor. Qed.

  Ltac unfold_U := (repeat progress match goal with
                                    | [H : context[U] |- _] => rewrite /U in H
                                    end); rewrite /U.
    
  Lemma tref_R3 S C s : S `<=` S0 -> coref F tref S -> C \in S ->
    fAX (fAG s)^- \in C -> ~ fulfillAG S0 S s C -> tref C.
  Proof.
    move => subS0 corefS inS inC H.
    have {H} AGn : C \notin fulfillAGb S0 S s by apply/fulfillAGP; tauto.
    have inF: s^- \in F. 
      move/(subP subS0)/(subP subsep) : inS => inU. rewrite powersetE in inU.
      move/(subP inU)/sfc_F/sfc_F : inC => //=. by case/andP.
    rewrite (fset1U inC). apply: gen_foc => {inC}.
    apply (subP subS0) in inS.
    move: fset0 (sub0x U) C inS AGn. apply: slack_ind => H IH subU C inS.
    rewrite -[{fset _}]/{fset clause} in IH. (* cleanup *)
    have /andP [inU RU] : (C \in U) && (R C \in U). 
      move/(subP subsep) : inS => inU. by rewrite RinU.
    rewrite fulfillAGE inE inS //= negb_and negb_or.
    case/orP.
    - case/allPn => ? /fimsetP [?]. rewrite inE andbC. case:(isDiaP _) => //= t -> inC -> /= sRs.
      rewrite (fset1U inC). apply gen_AXn. apply: tref_R1 sRs => //.
      suff: fAX t^- \in F. move/sfc_F => ?. by rewrite powersetU RU powersetE fsub1. 
      by apply/powersetP : inC.
    - case/andP => H1 /hasPn H2. 
      constructor.
      case: (boolP (R C \in H)) => HR; first by rewrite (fset1U HR); exact: gen_rep.
      apply: gen_AGh.
      + apply: tref_R1 H1 => //. by rewrite powersetU powersetE fsub1 inF.
      + apply: tref_R0 (RU) _ => D /sepP [D1 D2].
        apply: IH (D1) _; rewrite ?fsubUset ?fsub1 ?fproper1; try bcase. 
        move: (H2 _ D1). by rewrite /rtrans D2.
  Qed.

  Lemma refpred_tref C : ref F C -> tref C.
  Proof. by elim => *; eauto using tref_R1, tref_R2, tref_R3. Qed.

End RefPred.

Lemma supp_S_sat (F : clause) (sfc_F : sf_closed F) C :
  suppS (S F) C -> (exists M : fmodel, sat M C).
Proof.
  move => sC. case/hasP : sC => D inSF sDC.
  have inDD : D \in DD F by rewrite inE inSF.
  exists (model_of (DD F)). exists (SeqSub _ inDD) => s inC.
  apply: supp_eval => /=. exact: (allP sDC).
Qed.

Lemma gen_completeness C : gen (C,aVoid) + (exists M : fmodel, sat M C).
Proof.
  have sfc_F := @closed_sfc C.
  case (boolP (suppS (S (sfc C)) C)) => H.
  - right. exact: supp_S_sat H.
  - left. apply: refpred_tref (sfc_F) _ _. apply: S_refute => //. 
    by rewrite powersetE sub_sfc.
Qed.

Lemma gen_plain_sound C : gen (C, aVoid) -> ~ (exists M : cmodel, sat M C).
Proof.
  move => /gen_def.soundness H.
  suff : ~ (exists M : fmodel, sat M C).
  { move => nF [M] [w] /Kstar_def.satA wC.  apply: nF. 
    case: (@small_models [af C]); first by do 2 eexists.
    move => {M w wC} => M _ [w] wC. 
    exists M. exists w. exact/Kstar_def.satA. }
  case => M. move: H => /(_ M) H1 [w] H2.
  apply: H1. exists w. split => //=. apply/allP => s inC. apply/evalP. exact: H2.
Qed.
  
Corollary gen_correctness C : gen (C,aVoid) <-> ~ (exists M : cmodel, sat M C).
Proof. 
  split; first exact: gen_plain_sound. 
  case: (gen_completeness C) => // [[M MC] H]. exfalso. apply H. by exists M.
Qed.

(*
(* Lemma gen2_gen Ca : gen Ca -> gen_def.gen Ca. *)
(* Proof. by elim => {Ca}; eauto using gen_def.gen. Qed. *)

Lemma supp_lit s C : literal s -> (s \in C) = (C |> s).
Proof. case: s. by case. Qed.

Lemma SP F (sfc_F : sf_closed F) C : 
  reflect (C \in S0 F  /\ exists M : fmodel, sat M C) (C \in S F).
Proof.
  apply: introP => HS.
  - have inS0 : C \in S0 F. move: C HS. apply/subP. exact: prune_sub.
    split => //. exists (model_of (DD F)).
    have inDD : C \in S F `|` T F by rewrite inE;bcase.
    exists (Sub C inDD) => s ls.
    apply: supp_eval => /=. rewrite -supp_lit //.
    by case/sepP : inS0 => _ /andP [/allP /(_ _ ls)].
  - case => inS0. apply: gen_ref_sound.
    apply: refpred_tref => //. 
    apply: coref_S ; by rewrite // inE;bcase.
Qed.

Lemma DDP F (sfc_F : sf_closed F) C : 
  reflect (C \in S0 F  /\ exists M : fmodel, sat M C) (C \in demo.DD F).
Proof.
  apply: introP => HC.
  - have inS0 : C \in S0 F. move: C HC. apply/subP. exact: prune_sub.
    split => //. exists (model_of (demo.DD F)).
    exists (Sub C HC) => s ls.
    apply: supp_eval => /=. rewrite -supp_lit //.
    by case/sepP : inS0 => _ /andP [/allP /(_ _ ls)].
  - case => inS0. apply: gen_ref_sound.
    apply: refpred_tref => //.
    apply: coref_S => //. move/(SP sfc_F C).
Qed.

Lemma S_DD F : sf_closed F -> demo.DD F = S F :> {fset clause}.
Proof. move => sfc_F. apply: fset_ext => C. exact/DDP/SP. Qed.

Theorem gen_correctness C : gen (C,aVoid) <-> ~ (exists M : fmodel, sat M C).
Proof.
  split; first exact: gen_ref_sound.
  move: (@closed_sfc C) => sfc_C H.
  case: (boolP (suppS (S (sfc C)) C)) => [|nS]; first by rewrite -S_DD //; move/E1/E2.
  apply: (@refpred_tref _ sfc_C).
  apply: S_refute => //. by rewrite powersetE sub_sfc.
Qed.
*)
