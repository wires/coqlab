Require Import Unicode.Utf8.
Require Import abstract_algebra.

Parameter A B : Type.
Parameter star: (A → B) → A → B → Prop.

Notation "a - f -* b" := (star f a b) (at level 50) : star_scope.

Open Scope star_scope.

(* Definition termstar `{f: x ⟶ y} (a: A) (t: B) := a - f -* t. *)

Parameter C : Type.

Check (A * B * C) % type.


Require Import Arith.

Notation "p $ q" := (p q) (at level 40).

Definition foo := (A * B * C) % type.



