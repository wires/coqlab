Require Import Streams.
Require Import Unicode.Utf8.

CoFixpoint iterate {A} (f:A → A) (a:A) : Stream A :=
  Cons a (iterate f (f a)).

(** 1,2,3,... and 2,4,6,... *)
Definition positives := iterate (plus 1) 1.
Definition evens     := iterate (plus 2) 2.

Section fa.
 Let incr_2 {xs} : Prop := 2 + (hd xs) = (hd (tl xs)).

Lemma ohreally : ForAll (incr_2) (evens).
Proof.
  unfold evens.
  generalize 2 at 2 as p.
  cofix H.
  constructor.
   unfold incr_2. easy.
  now apply (H (2 + p)).
Qed.

End fa.

Section exist_1.

Let is_one {xs} : Prop := (Streams.hd xs) = 1.
Lemma foo: Streams.Exists is_one positives.
Proof.
  rewrite unfold_Stream; simpl.
  now constructor 1.
Qed.

End exist_1.

Section exist_3.

 Let big_nr {xs} : Prop := Streams.hd xs > 3.
 Lemma gets_big : Streams.Exists big_nr positives.
 Proof. 
   do 3 (constructor 2; rewrite unfold_Stream; simpl).
   constructor 1.
   now compute.
 Qed.

End exist_3.

Require Arith.

Lemma lt_le : ∀ n p:nat, n < p → n ≤ p.
  auto with arith.
Qed.

Lemma le_l_cancel (n m p:nat) (H: n ≥ m) : p + n ≥ p + m.
  auto with arith.
Qed.


Lemma le_l_cancel_S (n m:nat) : n ≤ m → S n ≤ S m.
  auto with arith.
(*  
At this point the [omega] tactic also works. You need to [Require Import Omega.],
but it gives quite an ugly proof term, which you can check with [Print le_n_S]:
 
 le_n_S = 
   λ (n m : nat) (H : n ≤ m),
   le_ind n (λ m0 : nat, S n ≤ S m0) (le_n (S n))
    (λ (m0 : nat) (_ : n ≤ m0) (IHle : S n ≤ S m0), le_S (S n) (S m0) IHle) m H
       : ∀ n m : nat, n ≤ m → S n ≤ S m
  
*)
Qed.


Section exists_n.

 Definition bigger_than (n:nat) (xs:Stream nat) : Prop := hd xs > n.
 
 Lemma gets_arbitry_big {n} : Exists (bigger_than n) positives.
 Proof.
   induction n.
    constructor 1; now compute.
  
Check Exists_ind.
(* Exists_ind
     : ∀ (A : Type) (P P0 : Stream A → Prop),
       (∀ x : Stream A, P x → P0 x)
       → (∀ x : Stream A, Exists P (tl x) → P0 (tl x) → P0 x)
         → (∀ x : Stream A, Exists P x → P0 x)
*)
 

d constructor 2. compute. constructor 1. simple.
   case IHn. intro. constructor 1. compute. auto with arith.
  intros. constructor 1. elim H.
   constructor 1.
   unfold big_nr.
   simpl. easy.
 Qed.


 Lemma gets_big : Streams.Exists big_nr evens.
  constructor 2.

End exist.

Section lazy.

Inductive LazyExists {A} (P : Stream A -> Prop) (xs : Stream A) : Prop :=
  | LazyHere : P xs -> LazyExists P xs
  | LazyFurther : P (Streams.tl xs) -> LazyExists P xs.


End lazy.
