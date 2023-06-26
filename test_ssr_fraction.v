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

Lemma RatioP (R: ringType) n d : Ratio_spec n d (@Ratio R n d) n d.
Proof.
  rewrite /Ratio /insubd; case: insubP=> /= [x /= d_neq0 hx|].
  have ->: x = @mkRatio R (n, d) d_neq0 by apply: val_inj.
  by constructor.
by rewrite negbK=> /eqP hx; rewrite {2}hx; constructor.
Qed.
