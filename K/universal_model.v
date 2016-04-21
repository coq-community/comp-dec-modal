(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From libs Require Import edone bcase fset base sltype.
Require Import K_def demo gentzen.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Construction of a Universal Model *)

Implicit Types (C D : clause).

Hint Resolve closed_sfc.

Lemma gen_decP C : reflect (gen C) (gen_dec C).
Proof. exact: sumboolP. Qed.

Lemma gen_lcons C : ~~ gen_dec C -> lcons C.
Proof. apply: contraTT. rewrite negbK => ?. apply/gen_decP. exact: lcons_gen. Qed.

(** Every underivable clause is supported by an underivable clause *)

Lemma genN_supp C : ~~ gen_dec C -> exists2 D:clause, suppC D C & ~~ gen_dec D.
Proof.
  move => H. suff: [some D in (S0 (sfc C)), suppC D C && ~~ gen_dec D].
  { case/hasP => D _ /andP [D1 D2]. by exists D. }
  apply/negPn. rewrite -all_predC. apply: contraNN H => /allP H. apply/gen_decP.
  apply: (ref_R0 (@closed_sfc C)); first by rewrite powersetE sub_sfc.
  move => D /sepP [D1 D2]. move : (H _ D1) => /=. rewrite negb_and D2.
  by case: (gen_dec _).
Qed.

Lemma sat_cons (M : cmodel) (w : M) C : (forall s, s \in C -> eval (interp s) w) -> ~~ gen_dec C.
Proof. move => H. apply/negP => /gen_decP/gen_correctness. apply. by exists M; exists w. Qed.
                                                        
Section UniversalModel.
  Record dmodel := DM { dstate :> choiceType ;
                        dtrans : dstate -> dstate -> bool;
                        dlabel : var -> pred dstate;
                        dbound : dstate -> {fset dstate};
                        dtransP x y : dtrans x y -> y \in dbound x
                      }.

  Fixpoint evald (M : dmodel) s : pred M :=
      match s with
      | fV p => dlabel p
      | fF => xpred0
      | fImp s t => fun w => evald s w ==> evald t w
      | fAX s => fun w => [all v in dbound w, dtrans w v ==> evald s v]
      end.

  Definition ts_of_dmodel (M : dmodel) : ts :=
    {| state := dstate M;
       trans := @dtrans M ;
       label p x := @dlabel M p x |}.

  Lemma evaldP (M : dmodel) (x:M) s : reflect (@eval (ts_of_dmodel M) s x) (evald s x).
  Proof.
    elim: s x => //=.
    - by constructor.
    - move => * ; exact: idP.
    - move => s IHs t IHt w.
      apply: iffP (@implyP _ _) _ _ => ? /IHs ?; apply/IHt; firstorder.
    - move => s IHs w.
      apply: iffP (@all_inP _ _ _ _) _ _ => [H v wv|H v _ wv].
      + apply/IHs. apply: H => //. exact: dtransP.
      + apply/IHs. exact: H.
  Qed.

  Lemma dmodelP (M : dmodel) : ldec (@eval (ts_of_dmodel M)).
  Proof. move => s w. case: (boolP (evald s w)) => /evaldP; tauto. Qed.

  Definition model_of_dmodel (M : dmodel) : cmodel := CModel (@dmodelP M).

  Definition UMType := { C : clause | ~~ gen_dec C }.
  Definition UMLabel (p:var) (C : UMType) := fV p^+ \in val C.

  Lemma UM_default_proof : ~~ gen_dec fset0.
  Proof.
    pose M := FModel [rel x y : unit | false] (fun p => xpred0).
    apply: (@sat_cons M tt) => ?. by rewrite inE.
  Qed.

  Definition UM_default : UMType := Sub fset0 UM_default_proof.

  Lemma UMP s1 s2 C : s1 \in C -> ~~ gen_dec C -> s1 = fAX s2^- ->
     exists x:UMType, suppC (val x) (s2^- |` R C).
  Proof.
    move => inC inDD E. subst s1.
    suff S: ~~ gen_dec (s2^- |` R C). case: (genN_supp S) => D D1 D2. by exists (Sub D D2).
    apply: contraNN inDD => /gen_decP H. rewrite (fset1U inC). apply/gen_decP. by constructor.
  Qed.  

  Definition UM_select (u : sform) (x:UMType) : UMType :=
    (if u \in val x as b return u \in val x = b -> UMType
     then fun b =>
            (if u is fAX s^- as c return u = c -> UMType
             then fun e => (xchoose (UMP b (valP x) e))
             else fun _ => UM_default) erefl
     else fun _ => UM_default) erefl.

  Lemma UM_select_correct (u : sform) (x : UMType) :
    u \in val x -> isDia u -> suppC (val (UM_select u x)) (body u |` R (val x)).
  Proof.
    move => in_x dia_u. rewrite /UM_select.
    move: (erefl (u \in val x)). rewrite {2 3}in_x => e.
    destruct u as [[|p|s t|s] [|]] => //.
    exact: (xchooseP (UMP e (valP x) (erefl _))).
  Qed.
  
  Definition UM_trans (x y : UMType) := [some u in val x, isDia u && (y == UM_select u x)].

  Definition UM_bound (x : UMType) := [fset UM_select u x | u <- [fset v in val x | isDia v]].

  Lemma UM_trans_bound x y : UM_trans x y -> y \in UM_bound x.
  Proof.
    case/hasP => s s1 /andP[s2 s3]. apply/fimsetP.
    exists s; last exact/eqP. by rewrite inE s1.
  Qed.

  Definition UMd := DM UMLabel UM_trans_bound.

  Definition UM : cmodel := model_of_dmodel UMd.

  Lemma UM_trans_R (x y : UM) : trans x y -> suppC (val y) (R (val x)).
  Proof.
    case/hasP => u u1 /andP [u2 /eqP ->].
    case: (UM_select_correct u1 u2). rewrite suppCU. by bcase.
  Qed.

  Lemma UM_trans_D (x : UM) s : fAX s^- \in val x -> exists2 y : UM, trans x y & val y |> s^-.
  Proof.
    move => H. exists (UM_select (fAX s^-) x). 
    - apply/hasP. by exists (fAX s^-) => //=.
    - case: (UM_select_correct H (erefl _)). by rewrite suppCU suppC1 /=; bcase.
  Qed.

  Lemma supp_eval s (x : UM) : val x |> s -> eval (interp s) x.
  Proof.
    case: s x. elim => [|p|s IHs t IHt|s IHs] [|] x.
    - by rewrite /= (LCF (gen_lcons (valP x))).
    - by rewrite /=. 
    - done.
    - rewrite /= /UMLabel. case: (LCF (gen_lcons (valP x))) => [_ /(_ p)]. 
      by case: (_^+ \in _) => //= ->.
    - rewrite /=. case/orP => [/IHs|/IHt] /=; tauto.
    - rewrite /=. case/andP => [/IHs ? /IHt] /=; tauto.
    - move => inX y xy. apply: (IHs true).
      rewrite -suppC1. apply: suppC_sub (UM_trans_R xy). by rewrite fsub1 RE.
    - rewrite [_ |> _]/= => H. case: (UM_trans_D H) => y xy Hy.
      move/(_ y xy). exact: (IHs false).
  Qed.

  Theorem UM_universal s :
    (exists (M:cmodel) (w:M), eval s w) -> (exists (x:UM), eval s x).
  Proof.
    pose C := [fset s^+].
    move => [M] [w Hw].
    have: ~~ gen_dec C. apply: (@sat_cons M w) => ?. by rewrite in_fset1 => /eqP->.
    case/genN_supp => D /allP D1 D2. exists (Sub D D2).
    rewrite -[s]/(interp (s^+)). apply: supp_eval. apply: D1. exact: fset11.
  Qed.
End UniversalModel.
