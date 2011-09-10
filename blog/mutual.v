

Inductive tree : Type :=
  | leaf : tree
  | node : forest -> tree
with forest : Type :=
  | nil : forest
  | cons : nat -> forest -> forest.
