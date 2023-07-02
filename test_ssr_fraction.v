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

Import FracField.

Variable R : idomainType.
Local Notation tofrac := (@FracField.tofrac R).

Lemma tofrac_is_multiplicative : multiplicative tofrac.
Proof.
split=> [p q|//]; unlock tofrac; rewrite -[X in _ = X]pi_mul.
by rewrite /mulf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

