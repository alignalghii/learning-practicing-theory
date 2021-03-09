Section my_first_explicite_proof_objects.

Variables A B: Prop.

Definition commutativity_proof (aAndB_proof: A /\ B) :=
  match aAndB_proof with
    conj a b => conj b a
  end.

(*
commutativity_proof (aAndB_proof: A /\ B) :=
  and_ind
  (fun a b => conj b a)
  aAndB_proof.
*)

Lemma commutativity: A /\ B -> B /\ A.
Proof.
  apply commutativity_proof.
Qed.

Print commutativity_proof.
Check conj.
Check pair.

Check and_ind.
Check and_rec.
