Lemma hej: forall (A B C: Prop), (A -> B -> C) -> A -> B -> C.
Proof.
  intros A B C abc_fun a b; apply abc_fun. exact a. exact b.
Qed.
