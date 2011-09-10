Require Import Program.


Program Definition foo x : Type := x.

Print sig.

SearchAbout sig.

Program Definition foo2 (x: {y | y < 4}) : nat := x.

Print Scopes.
(* nonneg_semiring_elements.v *)
(* decision.v option_eq_dec, or_dec *)

Require Import Omega.

Program Fixpoint pred (n: {x | x > 0}) : {y | S y = n} :=
  match n with
    | O => _
    | S x => x
  end.
Next Obligation..
