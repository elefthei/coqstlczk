From STLCZK Require Import Stlc_Ott.
Require Import Metalib.Metatheory.

Parameter X : expvar.
Parameter Y : expvar.

Definition n_to_expr(a: n) := tm_const (const_field a).

Coercion const_field: n >-> Stlc_Ott.const.
Coercion tm_const: Stlc_Ott.const >-> Stlc_Ott.exp.
Coercion n_to_expr: n >-> Stlc_Ott.exp.

Definition div_compute(a: nat) :=
  open_exp_wrt_exp (tm_abs ty_field (tm_binop (const_field 100) tm_div (tm_var_f X))) (tm_var_f X).

Definition div_check (a w: nat) :=
  open_exp_wrt_exp (
      open_exp_wrt_exp (
          tm_abs ty_field (
                   open_exp_wrt_exp (
                       tm_abs ty_field (tm_binop (tm_var_f X) tm_mul (tm_var_f Y)))
                              (tm_var_f Y)
                     )
                 )
          (tm_var_f Y)
    ) (tm_var_f X).


Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Inductive circuit_equiv(c: exp -> exp) (c': exp -> exp -> exp): Prop :=
| Eq_Sound:
    forall (v: exp) value v ->
    exists (w: exp),
      c x = const_field w ->
      c' x w = const_true ->
      circuit_equiv c c'.
