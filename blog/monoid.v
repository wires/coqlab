Require Import abstract_algebra.

(** * Formalizing categories *)

Require Import theory.categories.

(** basic properties *)
Section basics.
Context `{Category A}.

(* An arrow [f:a ⟶ b] is an isomorphism when there is an arrow
 [g:b ⟶ a] such that $g ∘ f = 1_a$ and $f ∘ g = 1_b$. In math-classes
 this is defined as ([theory.categories]):

     Definition iso_arrows {x y: X} (a: x ⟶ y) (b: y ⟶ x): Prop
      := a ◎ b = cat_id ∧ b ◎ a = cat_id. (* todo: product *)

 Lets proof that if [g] and [g'] are both inverses of [f], then [g = g'].
*)


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
