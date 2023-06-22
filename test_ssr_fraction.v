From mathcomp Require Import all_ssreflect fraction.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import ssrAC choice tuple bigop ssralg poly polydiv.
From mathcomp Require Import generic_quotient.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Open Scope quotient_scope.

Lemma Ratio0 (R: ringType) x : @Ratio R x 0 = @ratio0 R.
Proof. by rewrite /Ratio /insubd; case: insubP; rewrite //= eqxx. Qed.

(* Lemma numer_Ratio (R: ringType) x y : y != 0 -> (@Ratio R x y).1 = x. *)
(* Proof. by move=> ny0; rewrite /Ratio /insubd insubT. Qed. *)

(*Lemma Ratio0 (R: ringType) x : Ratio x 0 = ratio0 R.
Proof. by rewrite /Ratio /insubd; case: insubP; rewrite //= eqxx. Qed.
*)
