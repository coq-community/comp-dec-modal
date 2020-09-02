(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs Require Import edone bcase fset base modular_hilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Generic Lemmas for Literals and Support *)

Record slClass (form:choiceType) :=
  SLClass {
      supp' : {fset form * bool} -> form -> bool -> bool;
      supp_mon C D s : C `<=` D -> supp' C s.1 s.2 -> supp' D s.1 s.2;
      lit'  : form * bool -> bool;
      supp_lit C s b : lit' (s,b) -> supp' C s b = ((s,b) \in C);
      f_weight' : form -> nat;
      sweight_lit s : f_weight' s.1 = 0 <-> lit' s
    }.

Record slType := SLType { sl_form :> choiceType ; sl_class : slClass sl_form }.

Definition lit (form : slType) := lit' (sl_class form).
Definition supp (form : slType) := supp' (sl_class form).
Definition f_weight (form : slType) := f_weight' (sl_class form).

Section SuppC.
Variable form : slType.
Local Notation clause := {fset form * bool}.

Definition suppC (L C : clause) := [all s in C, supp L s.1 s.2].

Definition suppS S C := [some D in S, suppC D C].

Definition base S C := [fset D in S | suppC D C ].

Lemma suppCU L C C' : suppC L (C `|` C') = suppC L C && suppC L C'.
Proof. exact: allU. Qed.

Lemma suppCD L C C' : suppC L C' -> suppC L (C `\` C') -> suppC L C.
Proof. 
  move/allP => S1 /allP S2. apply/allP => s inC.
  case (boolP (s \in C')) => inC'; auto. apply: S2. by rewrite inE; bcase.
Qed.

Lemma suppCWL L1 L2 C : suppC L2 C -> suppC (L1 `|` L2) C.
Proof. apply: sub_all => s. apply: supp_mon; auto with fset. Qed.

Lemma suppC_sub L C C' : C `<=` C' -> suppC L C' -> suppC L C.
Proof. move => H. apply: sub_all_dom. exact/subP. Qed.


Definition s_weight := [fun s : form * bool => f_weight s.1].

Definition weight C := fsum s_weight C.

Definition literalC (L : clause) := [all s in L, lit s].

Lemma suppxx C : literalC C -> suppC C C.
Proof.
  move/allP => lit_C. apply/allP => [[s b]] /= inC.
  rewrite /supp supp_lit //. exact: lit_C.
Qed.

Lemma weight0 L : (weight L = 0) -> literalC L.
Proof. move/fsum_eq0 => H. apply/allP => x /H. by move/sweight_lit. Qed.

Lemma weightS L : (0 < weight L) -> ~~ literalC L.
Proof.
  rewrite lt0n. apply: contra => /allP H. apply/eqP.
  by have/fsum_const : {in L, const 0 s_weight} by move => x /H /sweight_lit.
Qed.

End SuppC.



Arguments s_weight {form} : rename.
Arguments weight [form] C.

Record slpType := SLPType { slp_form :> pSystem ; slp_class : slClass slp_form }.

Definition slType_of (form : slpType) := SLType (slp_class form).
Coercion slType_of : slpType >-> slType.
Canonical local_formSLType (form : slpType) : slType := form.

Section slpTheory.
  Variable form : slpType.
      
  Local Notation sform := (form * bool) %type.
  Local Notation clause := {fset form * bool}.
  Local Notation "s ^-" := (s,false) (at level 20, format "s ^-").
  Local Notation "s ^+" := (s,true) (at level 20, format "s ^+").

  Definition interp (f:slpType) (s : f * bool) := match s with (t,true) => t | (t,false) => ~~: t end.

  Local Notation "[ 'af' C ]" := (\and_(s <- C) interp s) (at level 0, format "[ 'af'  C ]").

  (** Caveat: use of the lemmas below sometimes exposes an invisible (implicit)
  slpType instance (propositional reasoning) and needs to be simplified to the
  underlying formula type before further modal reasoning can be applied *)

  Lemma af1p (s : form) : mprv (s ---> [af [fset s^+]]).
  Proof. apply: bigAI => t. by rewrite !inE => /eqP ->. Qed.

  Lemma afp1 (s : form) : mprv ([af [fset s^+]] ---> s).
  Proof. change s with (interp (s^+)) at 2. apply: bigAE. by rewrite !inE. Qed.
  
  Lemma af1n (s : form) : mprv (Neg s ---> [af [fset s^-]]).
  Proof. apply: bigAI => t. by rewrite !inE => /eqP ->. Qed.

  Lemma afn1 (s : form) : mprv ([af [fset s^-]] ---> Neg s).
  Proof. change (Neg s) with (interp (s^-)). apply: bigAE. by rewrite !inE. Qed.
  
  Local Notation xaf := (fun C : clause => [af C]).

  Variable ssub : sform -> {fset sform}.

  Inductive decomp (s : sform) : Type :=
  | decomp_lit : @lit form s -> decomp s
  | decomp_ab (S : {fset clause}) :
      (forall (D : clause), D \in S -> D `<=` ssub s) ->
      (forall (D : clause), D \in S -> weight D < s_weight s) ->
      (forall (C D : clause), D \in S -> suppC C D -> supp C s.1 s.2) ->
      mprv (interp s ---> \or_(D <- S) [af D])  
      -> decomp s.

  Hypothesis decompP : forall s, decomp s.

  Variable F : {fset sform}.
  Hypothesis ssub_F : forall s, s \in F -> ssub s `<=` F.

  Let LF : {fset clause} := [fset C in powerset F | literalC C].
  
  Lemma supp_aux C : C \in powerset F -> mprv ([af C] ---> \or_(D <- base LF C) [af D]).
  Proof.
    move: C. apply: @nat_size_ind _ _ (@weight _) _ => C IH inU.
    case: (posnP (weight C)) => [/weight0 lC |/weightS wC].
    - apply (bigOI xaf). by rewrite !inE suppxx; bcase.
    - case/allPn : wC => s inC nL.
      case: (decompP s) => [|S S1 S2 S3 S4]; first by rewrite (negbTE nL).
      rewrite -{1}(fsetUD1 inC). rewrite -> andU, bigA1, S4.
      rewrite -> bigODr. apply: bigOE => D inCs. rewrite <- andU.
      rewrite -> IH.
      + apply: bigOE => L'. rewrite !inE -andbA => /and3P [D1 D2 D3].
        apply: (bigOI xaf). rewrite !inE D1 D2 /=.
        move: D3. rewrite suppCU => /andP [D3]. apply: suppCD.
        rewrite /suppC all_fset1. exact: S3 D3.
      + apply: fsum_replace; rewrite ?fsub1 // fsum1. exact: S2.
      + rewrite powersetU  [_ `\` _ \in _](sub_power _ inU) // andbT.
        rewrite powersetE. apply: sub_trans (S1 _ inCs) _. apply ssub_F.
        rewrite powersetE in inU. exact: (subP inU).
  Qed.
End slpTheory.

Notation "[ 'af' C ]" := (\and_(s <- C) interp s) (at level 0, format "[ 'af'  C ]").
Arguments decomp_ab [form ssub s] S : rename.
