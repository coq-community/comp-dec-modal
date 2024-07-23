(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From CompDecModal.libs
 Require Import edone bcase fset base induced_sym modular_hilbert sltype.
From CompDecModal.CTL
 Require Import CTL_def hilbert.
Import IC.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Translation of History Rules to Hilbert Refutations *)

Definition AU_ (u s t : form) := AU (s :/\: u) (t :/\: u).

Lemma AUH_hil (s t u v : form) :
  prv (u :/\: t ---> Bot) ->
  prv (u ---> s ---> ~~: AX (AU_ (~~: u :/\: v) s t)) ->
  prv (u ---> AU_ v s t ---> Bot).
Proof.
  move => H0 H1.
  suff sf: prv (AU_ v s t ---> AU_ (~~: u :/\: v) s t).
  { do 2 Intro.
    Have (~~: t); [Intro; ApplyH H0; by ApplyH axAI| Intro].
    Have ((s :/\: v) :/\: AX (AU_ v s t)).
    + Rev* 1. rewrite /AU_. rewrite -> axAUeq at 1. rewrite /Or.
      Intro. Apply. ApplyH axAcase. do 2 Intro. by Apply* 3.
    + rewrite -> sf at 2. do 2 ApplyH axAcase. do 2 Intro. by ApplyH H1. }
  apply: rAU_ind.
  - rule axAcase. do 2 Intro. ApplyH axAUI. ApplyH axAI. 
    ApplyH axAI. Intro. ApplyH H0. by ApplyH axAI.
  - rule axAcase. do 3 Intro. ApplyH axAUf. ApplyH axAI. 
    ApplyH axAI. Intro. by ApplyH H1.
Qed.

Definition EU_ (H s t : form) := EU (s :/\: H) (t :/\: H).

Lemma ARH_hil (s t C H : form) : 
  prv (t ---> ~~: C) ->
  prv (EX (EU_ (~~: C :/\: H) s t) ---> s ---> ~~: C) ->
  prv (C ---> EU_ H s t ---> fF).
Proof.
  move => H0 H1.
  suff sf: prv (EU_ H s t ---> EU_ (~~: C :/\: H) s t).
  { do 2 Intro.
    Have (~~: t); [Intro; ApplyH H0; by ApplyH axAI| Intro].
    Have ((s :/\: H) :/\: EX (EU_ H s t)).
    + Rev* 1. rewrite /EU_. rewrite -> axEUeq at 1. rewrite /Or.
      Intro. Apply. ApplyH axAcase. do 2 Intro. by Apply* 3.
    + rewrite -> sf at 2. do 2 ApplyH axAcase. do 3 Intro. by ApplyH H1. }
  apply: EU_ind.
  - rule axAcase. do 2 Intro. ApplyH axEUI. ApplyH axAI. 
    ApplyH axAI. Intro. by ApplyH H0. 
  - rule axAcase. do 3 Intro. ApplyH axEUI2. ApplyH axAI. 
    ApplyH axAI. Intro. by ApplyH H1.
Qed.
