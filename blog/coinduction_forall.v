Require Import Streams.
Require Import canonical_names abstract_algebra.

Section fi.

Variable A : Type.
Variable P Q : Stream A -> Prop.
Variable Pt_Qt : forall t, P t -> Q t.

Lemma forall_impl : forall t,  ForAll P t -> ForAll Q t.
 cofix G. 
 split.
 apply (Pt_Qt t). 
 destruct H as [H0 _]. 
 exact H0.
 destruct H as [_ H1].
 apply (G (tl t) H1).
Qed.

End fi.


