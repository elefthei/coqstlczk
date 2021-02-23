Require Import Metalib.Metatheory.
From STLCZK Require Import Stlc.


Section Foo.
  Variable A: nat.
  Definition bar(a: nat): Prop := a > A.
  
  Lemma L: exists n, bar n.
  Proof.
    exists (S A).
    unfold bar.
    auto.
  Qed.

End Foo.

Check bar.


Module Gadgets.

  Definition X : atom := fresh nil.
  Definition Y : atom := fresh (X :: nil).
  
  (** Notation on Stlc_Ott *)
  Coercion tm_var_f: expvar >-> exp.
  Coercion const_field: nat >-> constant.
  Coercion tm_constant: constant >-> exp.
  
  Declare Custom Entry stlc_ty.
  Declare Custom Entry stlc.
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
  Notation "S -> T" := (ty_arrow S T) (in custom stlc_ty at level 50, right associativity).
  Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
  Notation "\_ : t , y" :=
    (tm_abs t y) (in custom stlc at level 90,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
  Notation "# n" := (tm_var_b n) (in custom stlc at level 1).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).

  Notation "'Field'" := ty_field (in custom stlc_ty at level 0).
  Notation "'Bool'" := ty_bool (in custom stlc_ty at level 0).

  Notation "x + y" := (tm_binop x op_add y) (in custom stlc at level 2,
                                                left associativity).
  Notation "x - y" := (tm_binop x op_sub y) (in custom stlc at level 2,
                                                left associativity).

  Notation "x * y" := (tm_binop x op_mul y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x / y" := (tm_binop x op_div y) (in custom stlc at level 1,
                                                left associativity).
  Notation "x && y" := (tm_binop x op_and y) (in custom stlc at level 2,
                                                 left associativity).
  Notation "x || y" := (tm_binop x op_or y) (in custom stlc at level 2,
                                               left associativity).
  Notation "x == y" := (tm_eq x y) (in custom stlc at level 1,
                                       left associativity).
  Notation "! x " := (tm_not x) (in custom stlc at level 1).

  Notation "'if' x 'then' y 'else' z" :=
    (tm_ifthenelse x y z) (in custom stlc at level 89,
                              x custom stlc at level 99,
                              y custom stlc at level 99,
                              z custom stlc at level 99,
                              left associativity).

  Notation "'let _' '=' t1 'in' t2" :=
    (tm_let t1 t2) (in custom stlc at level 0).

  (** TR closure *)
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

  Notation " t '-->*' t' " := (multi step t t') (at level 40).
  
  Definition circuit_equiv(c: exp) (c': exp): Prop :=
    forall (n: nat), exists (ans: nat),
        <{ c' n ans }> -->* const_true <->
        <{ c n }> -->* ans.
   
  Notation "a '~' b" := (circuit_equiv a b) (at level 50).

  (** Example 1: Division *)
  Definition div :=
    <{ \_: Field, (1 / #1) }>.

  Definition div_check :=
    <{ \_: Field,
           (\_: Field,
                #1 * #2 == 1)
     }>.

  Ltac invert H := inversion H; subst; clear H.
  Ltac solve := repeat match goal with
                       | [ H: step _ _ |- _ ] => inversion H; subst; clear H
                       | [ H: <{ (open_exp_wrt_exp _ _) }> -->* _ |- _ ] => cbn in H
                       | [ H: ?P1 -->* ?P2 |- _ ] => inversion H; subst; clear H
                       end.
  
  Theorem div_gadget_equiv: div ~ div_check.
  Proof.
    unfold circuit_equiv, div, div_check.
    intros.
    induction n.
    - exists 0.
      split; intro H; solve.
    - exists 0. (** This is wrong in F_p but works in nat *)
      split; intro H'; solve.
  Qed.

  Fixpoint constant_to_boolnat(c: constant) : nat :=
    match c with
    | const_true => 1
    | const_false => 0
    | const_field 0 => 0
    | const_field (S n) => 1
    end.
  
  (** Example 2: Conditional *)
  Definition ite(c: constant):=
    <{ \_: Field,
           (\_: Field,
                if c then #2 else #3
           )
     }>.
  
  Definition ite_check(c: constant) :=
    <{ \_: Field,
           (\_: Field,
                (\_: Field,
                     (#3 == #1 + {constant_to_boolnat c} * (#2 - #1))
                )
           )
     }>.

  Theorem ite_equiv: forall c, ite c ~ ite_check c.
  Proof.
    destruct 0 eqn:Hc;
      unfold circuit_equiv, ite, ite_check; induction 0; exists 0; split; intro H; solve.
  Qed.

End Gadgets.     
