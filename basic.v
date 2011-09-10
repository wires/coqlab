Require Import Unicode.Utf8.

Lemma meh : ∃(n:nat), n < 4.
Proof.
 apply ex_intro with (x := 2).
 auto.
Qed.

Lemma trans P Q R : (P → Q) → (Q → R) → (P → R).
 firstorder.
Qed.
