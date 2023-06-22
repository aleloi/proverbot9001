From mathcomp Require Import all_ssreflect ssralg.

(* 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
*)

Open Scope ring_scope.
Import GRing.
Lemma prodf_eq0 (R: idomainType) (I : finType) (P : pred I) (F : I -> R) :
  reflect (exists2 i, P i & (F i == 0)) (\prod_(i | P i) F i == 0).
Proof.
apply: (iffP idP) => [|[i Pi /eqP Fi0]]; last first.
Search left_zero.
  by rewrite (bigD1 i) //= Fi0 mul0r.
elim: (index_enum _) => [|i r IHr]; first by rewrite big_nil oner_eq0.
rewrite big_cons /=; have [Pi | _] := ifP; last exact: IHr.
by rewrite mulf_eq0; case/orP=> // Fi0; exists i.
Qed.
