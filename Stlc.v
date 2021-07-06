(* generated by Ott 0.31, locally-nameless from: Stlc.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Ott.ott_list_core.

(** For F_p *)
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinInt.

From STLCZK Require Import GaloisField.

Module Stlc_Ott(Import PF: GaloisField.GaloisField).
  Import PF.
  
  (** syntax *)  
  Definition expvar : Set := var.
  
  Inductive op : Set := 
  | op_add : op
  | op_sub : op
  | op_mul : op
  | op_div : op
  | op_and : op
  | op_or : op.
  
  Inductive typ : Set := 
  | ty_bool : typ
  | ty_field : typ
  | ty_arrow (T1:typ) (T2:typ).
  
  Inductive constant : Set := 
  | const_bool (b5:bool)
  | const_field (n5:Fp).

  (* exp -> anfexp -> (normalization) -> anfexp *)
  Inductive exp : Set := 
  | tm_var_b (_:nat)
  | tm_var_f (x:expvar)
  | tm_abs (T:typ) (e:exp)
  | tm_app (e1:exp) (e2:exp)
  | tm_let (e1:exp) (e2:exp)
  | tm_constant (constant5:constant)
  | tm_binop (e1:exp) (op5:op) (e2:exp)
  | tm_eq (e1:exp) (e2:exp)
  | tm_not (e:exp)
  | tm_ifthenelse (e:exp) (e1:exp) (e2:exp).

  Definition typing_env : Set := list (atom*typ).
  Lemma eq_op: forall (x y : op), {x = y} + {x <> y}.
  Proof.
    decide equality; auto with ott_coq_equality arith.
  Defined.
  Hint Resolve eq_op : ott_coq_equality.
  Hint Resolve eq_field: ott_coq_equality.
  Lemma eq_bool: forall (x y: bool), {x = y} + {x <> y}.
  Proof.
    decide equality; auto.
  Qed.
  Hint Resolve eq_bool: ott_coq_equality.
  Lemma eq_typ: forall (x y : typ), {x = y} + {x <> y}.
  Proof.
    decide equality; auto with ott_coq_equality arith.
  Defined.
  Hint Resolve eq_typ : ott_coq_equality.
  Lemma eq_constant: forall (x y : constant), {x = y} + {x <> y}.
  Proof.
    decide equality; auto with ott_coq_equality arith.
  Defined.
  Hint Resolve eq_constant : ott_coq_equality.
  Lemma eq_exp: forall (x y : exp), {x = y} + {x <> y}.
  Proof.
    decide equality; auto with ott_coq_equality arith.
  Defined.
  Hint Resolve eq_exp : ott_coq_equality.
  
  (* EXPERIMENTAL *)
  (** auxiliary functions on the new list types *)
  (** library functions *)
  (** subrules *)
  Definition is_value_of_exp (e_5:exp) : bool :=
    match e_5 with
    | (tm_var_b nat) => false
    | (tm_var_f x) => false
    | (tm_abs T e) => (true)
    | (tm_app e1 e2) => false
    | (tm_let e1 e2) => false
    | (tm_constant constant5) => (true)
    | (tm_binop e1 op5 e2) => false
    | (tm_eq e1 e2) => false
    | (tm_not e) => false
    | (tm_ifthenelse e e1 e2) => false
    end.
  
  (** arities *)
  (** opening up abstractions *)
  Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
    match e__6 with
    | (tm_var_b nat) => if (k === nat) then e_5 else (tm_var_b nat)
    | (tm_var_f x) => tm_var_f x
    | (tm_abs T e) => tm_abs T (open_exp_wrt_exp_rec (S k) e_5 e)
    | (tm_app e1 e2) => tm_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (tm_let e1 e2) => tm_let (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec (S k) e_5 e2)
    | (tm_constant constant5) => tm_constant constant5
    | (tm_binop e1 op5 e2) => tm_binop (open_exp_wrt_exp_rec k e_5 e1) op5 (open_exp_wrt_exp_rec k e_5 e2)
    | (tm_eq e1 e2) => tm_eq (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (tm_not e) => tm_not (open_exp_wrt_exp_rec k e_5 e)
    | (tm_ifthenelse e e1 e2) => tm_ifthenelse (open_exp_wrt_exp_rec k e_5 e) (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    end.
  
  Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

  (** terms are locally-closed pre-terms *)
  (** definitions *)
  
  (* defns LC_exp *)
  Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
  | lc_tm_var_f : forall (x:expvar),
      (lc_exp (tm_var_f x))
  | lc_tm_abs : forall (L:vars) (T:typ) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (tm_var_f x) )  )  ->
      (lc_exp (tm_abs T e))
  | lc_tm_app : forall (e1 e2:exp),
      (lc_exp e1) ->
      (lc_exp e2) ->
      (lc_exp (tm_app e1 e2))
  | lc_tm_let : forall (L:vars) (e1 e2:exp),
      (lc_exp e1) ->
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (tm_var_f x) )  )  ->
      (lc_exp (tm_let e1 e2))
  | lc_tm_constant : forall (constant5:constant),
      (lc_exp (tm_constant constant5))
  | lc_tm_binop : forall (e1:exp) (op5:op) (e2:exp),
      (lc_exp e1) ->
      (lc_exp e2) ->
      (lc_exp (tm_binop e1 op5 e2))
  | lc_tm_eq : forall (e1 e2:exp),
      (lc_exp e1) ->
      (lc_exp e2) ->
      (lc_exp (tm_eq e1 e2))
  | lc_tm_not : forall (e:exp),
      (lc_exp e) ->
      (lc_exp (tm_not e))
  | lc_tm_ifthenelse : forall (e e1 e2:exp),
      (lc_exp e) ->
      (lc_exp e1) ->
      (lc_exp e2) ->
      (lc_exp (tm_ifthenelse e e1 e2)).
  (** free variables *)
  Fixpoint fv_exp (e_5:exp) : vars :=
    match e_5 with
    | (tm_var_b nat) => {}
    | (tm_var_f x) => {{x}}
    | (tm_abs T e) => (fv_exp e)
    | (tm_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
    | (tm_let e1 e2) => (fv_exp e1) \u (fv_exp e2)
    | (tm_constant constant5) => {}
    | (tm_binop e1 op5 e2) => (fv_exp e1) \u (fv_exp e2)
    | (tm_eq e1 e2) => (fv_exp e1) \u (fv_exp e2)
    | (tm_not e) => (fv_exp e)
    | (tm_ifthenelse e e1 e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
    end.

  (** substitutions *)
  Fixpoint subst_exp (e_5:exp) (x5:expvar) (e__6:exp) {struct e__6} : exp :=
    match e__6 with
    | (tm_var_b nat) => tm_var_b nat
    | (tm_var_f x) => (if eq_var x x5 then e_5 else (tm_var_f x))
    | (tm_abs T e) => tm_abs T (subst_exp e_5 x5 e)
    | (tm_app e1 e2) => tm_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
    | (tm_let e1 e2) => tm_let (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
    | (tm_constant constant5) => tm_constant constant5
    | (tm_binop e1 op5 e2) => tm_binop (subst_exp e_5 x5 e1) op5 (subst_exp e_5 x5 e2)
    | (tm_eq e1 e2) => tm_eq (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
    | (tm_not e) => tm_not (subst_exp e_5 x5 e)
    | (tm_ifthenelse e e1 e2) => tm_ifthenelse (subst_exp e_5 x5 e) (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
    end.


  (** definitions *)

  (* defns Jtyping *)
  Inductive typing : typing_env -> exp -> typ -> Prop :=    (* defn typing *)
  | typing_var : forall (G:typing_env) (x:expvar) (T:typ),
      binds ( x ) ( T ) ( G )  ->
      uniq ( G )  ->
      typing G (tm_var_f x) T
  | typing_abs : forall (L:vars) (G:typing_env) (T1:typ) (e:exp) (T2:typ),
      ( forall x , x \notin  L  -> typing  ((one (pair  x   T1 )) ++  G )   ( open_exp_wrt_exp e (tm_var_f x) )  T2 )  ->
      typing G (tm_abs T1 e) (ty_arrow T1 T2)
  | typing_app : forall (G:typing_env) (e1 e2:exp) (T2 T1:typ),
      typing G e1 (ty_arrow T1 T2) ->
      typing G e2 T1 ->
      typing G (tm_app e1 e2) T2
  | typing_true : forall (G:typing_env),
      typing G (tm_constant (const_bool  true )) ty_bool
  | typing_false : forall (G:typing_env),
      typing G (tm_constant (const_bool  false )) ty_bool
  | typing_field : forall (G:typing_env) (n5:Fp),
      typing G (tm_constant (const_field n5)) ty_field
  | typing_boolop : forall (G:typing_env) (e1:exp) (op5:op) (e2:exp),
      typing G e1 ty_bool ->
      typing G e2 ty_bool ->
      typing G (tm_binop e1 op5 e2) ty_bool
  | typing_boolnot : forall (G:typing_env) (e:exp),
      typing G e ty_bool ->
      typing G (tm_not e) ty_bool
  | typing_fieldop : forall (G:typing_env) (e1:exp) (op5:op) (e2:exp),
      typing G e1 ty_field ->
      typing G e2 ty_field ->
      typing G (tm_binop e1 op5 e2) ty_field
  | typing_eqop : forall (G:typing_env) (e1 e2:exp) (T:typ),
      typing G e1 T ->
      typing G e2 T ->
      typing G (tm_eq e1 e2) ty_bool
  | typing_if : forall (G:typing_env) (e e1 e2:exp) (T:typ),
      typing G e ty_bool ->
      typing G e1 T ->
      typing G e2 T ->
      typing G (tm_ifthenelse e e1 e2) T
  | typing_let : forall (L:vars) (G:typing_env) (e1 e2:exp) (T2 T1:typ),
      typing G e1 T1 ->
      ( forall x , x \notin  L  -> typing  ((one (pair  x   T1 )) ++  G )   ( open_exp_wrt_exp e2 (tm_var_f x) )  T2 )  ->
      typing G (tm_let e1 e2) T2.

  (* defns Jop *)
  Inductive step : exp -> exp -> Prop :=    (* defn step *)
  | step_app_1 : forall (e1 e2 e1':exp),
      lc_exp e2 ->
      step e1 e1' ->
      step (tm_app e1 e2) (tm_app e1' e2)
  | step_app_2 : forall (e2 e2' v1:exp),
      Is_true (is_value_of_exp v1) ->
      lc_exp v1 ->
      step e2 e2' ->
      step (tm_app v1 e2) (tm_app v1 e2')
  | step_beta : forall (T:typ) (e1 v2:exp),
      Is_true (is_value_of_exp v2) ->
      lc_exp (tm_abs T e1) ->
      lc_exp v2 ->
      step (tm_app  ( (tm_abs T e1) )  v2)  (open_exp_wrt_exp  e1   v2 ) 
  | step_if_cog : forall (e1 e2 e3 e1':exp),
      lc_exp e2 ->
      lc_exp e3 ->
      step e1 e1' ->
      step (tm_ifthenelse e1 e2 e3) (tm_ifthenelse e1' e2 e3)
  | step_if_true : forall (e1 e2:exp),
      lc_exp e2 ->
      lc_exp e1 ->
      step (tm_ifthenelse (tm_constant (const_bool  true )) e1 e2) e1
  | step_if_false : forall (e1 e2:exp),
      lc_exp e1 ->
      lc_exp e2 ->
      step (tm_ifthenelse (tm_constant (const_bool  false )) e1 e2) e2
  | step_not_true : 
      step (tm_not (tm_constant (const_bool  true ))) (tm_constant (const_bool  false ))
  | step_not_false : 
      step (tm_not (tm_constant (const_bool  false ))) (tm_constant (const_bool  true ))
  | step_and_1 : forall (e:exp),
      lc_exp e ->
      step  ( (tm_binop e op_and (tm_constant (const_bool  true ))) )  e
  | step_and_2 : forall (e:exp),
      lc_exp e ->
      step  ( (tm_binop (tm_constant (const_bool  true )) op_and e) )  e
  | step_and_3 : forall (e:exp),
      lc_exp e ->
      step  ( (tm_binop e op_and (tm_constant (const_bool  false ))) )  (tm_constant (const_bool  false ))
  | step_and_4 : forall (e:exp),
      lc_exp e ->
      step  ( (tm_binop (tm_constant (const_bool  false )) op_and e) )  (tm_constant (const_bool  false ))
  | step_or_1 : forall (e1:exp),
      lc_exp e1 ->
      step  ( (tm_binop e1 op_or (tm_constant (const_bool  true ))) )  (tm_constant (const_bool  true ))
  | step_or_2 : forall (e1:exp),
      lc_exp e1 ->
      step  ( (tm_binop (tm_constant (const_bool  true )) op_or e1) )  (tm_constant (const_bool  true ))
  | step_or_3 : forall (e1:exp),
      lc_exp e1 ->
      step  ( (tm_binop e1 op_or (tm_constant (const_bool  false ))) )  e1
  | step_or_4 : forall (e1:exp),
      lc_exp e1 ->
      step  ( (tm_binop (tm_constant (const_bool  false )) op_or e1) )  e1
  | step_let_v : forall (e2 v1:exp),
      Is_true (is_value_of_exp v1) ->
      lc_exp (tm_let v1 e2) ->
      lc_exp v1 ->
      step (tm_let v1 e2)  (open_exp_wrt_exp  e2   v1 ) 
  | step_let_cog : forall (e1 e2 e1':exp),
      lc_exp (tm_let e1 e2) ->
      step e1 e1' ->
      step (tm_let e1 e2) (tm_let e1' e2)
  | step_binop_cog_1 : forall (e1:exp) (op5:op) (e2 e1':exp),
      lc_exp e2 ->
      step e1 e1' ->
      step (tm_binop e1 op5 e2) (tm_binop e1' op5 e2)
  | step_binop_cog_2 : forall (c1:constant) (op5:op) (e2 e2':exp),
      step e2 e2' ->
      step (tm_binop (tm_constant c1) op5 e2) (tm_binop (tm_constant c1) op5 e2')
  | step_add_const : forall (n1 n2:Fp),
      step (tm_binop (tm_constant (const_field n1)) op_add (tm_constant (const_field n2))) (tm_constant (const_field  (pkplus  n1   n2 ) ))
  | step_sub_const : forall (n1 n2:Fp),
      step (tm_binop (tm_constant (const_field n1)) op_sub (tm_constant (const_field n2))) (tm_constant (const_field  (pksub  n1   n2 ) ))
  | step_mul_const : forall (n1 n2:Fp),
      step (tm_binop (tm_constant (const_field n1)) op_mul (tm_constant (const_field n2))) (tm_constant (const_field  (pkmul  n1   n2 ) ))
  | step_div_const : forall (n1 n2:Fp),
      (const_field n2)  <>  (const_field  0:%p )  ->
      step (tm_binop (tm_constant (const_field n1)) op_div (tm_constant (const_field n2))) (tm_constant (const_field  (pkdiv  n1   n2 ) ))
  | step_eq_cog_1 : forall (e1 e2 e1':exp),
      lc_exp e2 ->
      step e1 e1' ->
      step (tm_eq e1 e2) (tm_eq e1' e2)
  | step_eq_cog_2 : forall (c1:constant) (e2 e2':exp),
      step e2 e2' ->
      step (tm_eq (tm_constant c1) e2) (tm_eq (tm_constant c1) e2')
  | step_eq_refl : forall (c:constant),
      step (tm_eq (tm_constant c) (tm_constant c)) (tm_constant (const_bool  true ))
  | step_eq_neq : forall (c1 c2:constant),
      c1  <>  c2  ->
      step (tm_eq (tm_constant c1) (tm_constant c2)) (tm_constant (const_bool  false )).

  (** infrastructure *)
  Hint Constructors typing step lc_exp : core.

End Stlc_Ott. 

Module Stlc(PF: GaloisField).
  Import PF.
  Include Stlc_Ott PF.

  Coercion tm_var_f: expvar >-> exp.
  Coercion tm_constant: constant >-> exp.
  Declare Custom Entry stlc_ty.
  Declare Custom Entry stlc.
  
  Notation "'fp' n" := (tm_constant (const_field n)) (in custom stlc at level 0).
  Notation "'true'"  := true (at level 1).
  Notation "'true'" := (tm_constant (const_bool true)) (in custom stlc at level 0).
  Notation "'false'"  := false (at level 1).
  Notation "'false'" := (tm_constant (const_bool false)) (in custom stlc at level 0).
  Notation "<{ e }>" := e (e custom stlc at level 99).
  Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
  Notation "( x )" := x (in custom stlc, x at level 99).
  Notation "( x )" := x (in custom stlc_ty, x at level 99).
  Notation "x" := x (in custom stlc at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).  
  Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
  Notation "\_ : t , y" :=
    (tm_abs t y) (in custom stlc at level 90,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 80,
                     left associativity).
  Notation "# n" := (tm_var_b n%nat) (in custom stlc at level 0).
  Notation "{ x }" := x (in custom stlc at level 1, x constr).
  Notation "S -> T" := (ty_arrow S T) (in custom stlc_ty at level 2, right associativity).
  Notation "Gamma '|-' t '::' T" := (typing Gamma t T) (in custom stlc_ty at level 40, t custom stlc, T custom stlc_ty at level 1).
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
  Notation "x && y" := (tm_binop x op_and y) (in custom stlc at level 4,
                                                 left associativity).
  Notation "x || y" := (tm_binop x op_or y) (in custom stlc at level 4,
                                                left associativity).
  Notation "x == y" := (tm_eq x y) (in custom stlc at level 3,
                                       left associativity).
  Notation "! x " := (tm_not x) (in custom stlc at level 3).

  Notation "'if' x 'then' y 'else' z" :=
    (tm_ifthenelse x y z) (in custom stlc at level 89,
                              x custom stlc at level 99,
                              y custom stlc at level 99,
                              z custom stlc at level 99,
                              left associativity).
  Notation "'let' t1 'in' t2" :=
    (tm_let t1 t2) (in custom stlc at level 88,
                       t1 custom stlc at level 99,
                       t2 custom stlc at level 99,
                       left associativity).
 
  (** Equality projections *)
  Lemma eq_stlc_fp: forall n w, <{ fp n }> = <{ fp w }> <-> n = w.
  Proof.
    intros; split; intros; (inversion H || rewrite H); reflexivity.
  Qed.

  Lemma neq_stlc_fp: forall n w, <{ fp n }> <> <{ fp w }> <-> n <> w.
  Proof.
    intros.
    split.
    intros;intro.
    apply eq_stlc_fp in H0.
    contradiction.
    intros; intro.
    apply eq_stlc_fp in H0.
    contradiction.
  Qed.
  Hint Resolve eq_stlc_fp: pk.
  Hint Resolve neq_stlc_fp: pk.
  
End Stlc.


