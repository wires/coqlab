Require Import abstract_algebra.

(** * Formalizing categories *)

(** ** Monoids

 We start with the natural numbers formalized as
 a degenerate monoid, with one object and an arrow
 for each n ∈ ℕ. Arrow composition is defined as plus.

 The category has one object, so the type of
 the objects in the category is appropriatly described
 by the [unit] type, which has only one value [()].

*)

Instance mon_arrows: Arrows unit := λ _ _, nat.

Instance mon_id: CatId unit := λ _, (0 % nat).

Instance mon_comp: CatComp unit := λ _ _ _ a b, (a + b) % nat.

Instance mon_equiv: ∀ x y, Equiv (x ⟶ y) := λ _ _ f g, f ≡ g.

(*
Instance foo: ∀ x y, Equiv (x ⟶ y).
Proof.
  intros ? ? f g.
  apply (λ x y : nat, eq x y).
  exact f. exact g.
Defined.
Print foo.
*)


(*Set Printing Implicit.
Unset Printing Notations.
*)
Require Import Arith.
Instance nat_as_Monoid : Category unit.
  repeat try constructor; try apply _.
   intros; now exact Plus.plus_assoc.
  compute; intros; now easy.
Qed.

(*

Class Graph N `{Arrows N} `{∀ x y : N, Equiv (x ⟶ y)} : Prop :=
  arrow_equiv :> ∀ x y, Setoid (x ⟶ y).
*)
