(** Construct a proof object for the following theorem: A /\ B -> B /\ A, where A and B are propositions! *)

Section my_first_explicite_proof_object.

	Variables A B: Prop.

	(** A proof object is a lambda expression whose inhabited type is the theorem to be proven: *)
	Definition commutativity_proof (aAndB_proof: A /\ B) :=
	  match aAndB_proof with
	    conj a b => conj b a
	  end.

	(** An alternative, but equivalent form of a proof object that can prove the same theorem: *)
	Definition commutativity_proof_2 (aAndB_proof: A /\ B) :=
	  and_ind
	  (fun a b => conj b a)
	  aAndB_proof.

	(** The commutativity theorem itself, which is proven by the above proof objects: *)
	Lemma commutativity: A /\ B -> B /\ A.
	Proof.
	  apply commutativity_proof.
	Qed.

	(** Experiment interactively with the representation proof objects: *)
	Print commutativity_proof.
	Check conj.
	Check pair.

	Check and_ind.
	Check and_rec.
End my_first_explicite_proof_object.
