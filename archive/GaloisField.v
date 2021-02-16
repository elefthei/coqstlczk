Class GaloisField (A : Set) (p: nat):=
  { eqDec: forall a b: A, {a = b} + { a <> b };
    one: A;
    eqb : A -> A -> bool;
    add: A -> A -> A;
    sub: A -> A -> A;
    mul: A -> A -> A;
    inverse: A -> A;
    div: A -> A -> A := fun a b: A => mul a (inverse b);
    eq_refl: forall x: A, x = x;
    eq_trans: forall x y z: A, x = y -> y = z -> x = z;
    eqb_leibniz : forall x y, eqb x y = true -> x = y;
    fromNat: forall n: nat, n < p -> A;
    toNat: A -> nat
  }.

(** Notation *)
Declare Custom Entry fields.
Notation "[[ e ]]" := e (e custom fields at level 99).
Notation "( x )" := x (in custom fields, x at level 99).
Notation "x" := x (in custom fields at level 0, x constr at level 0).
Notation "a + b" := (GaloisField.add a b) (in custom fields at level 40, left associativity).
Notation "a - b" := (GaloisField.sub a b) (in custom fields at level 40, left associativity).
Notation "a * b" := (GaloisField.mul a b) (in custom fields at level 40, left associativity).
Notation "a / b" := (GaloisField.div a b) (in custom fields at level 40, left associativity).

