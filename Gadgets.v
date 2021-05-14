Require Import Metalib.Metatheory.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Stlc.
From STLCZK Require Import R1cs.
From STLCZK Require Import Ltac.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Vectors.VectorDef.

Module Gadget(PF: GaloisField).
  Import PF.
  Include R1CS PF.
  Include Stlc PF.

  (** TR closure *)
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.
  Notation " t '-->*' t' " := (multi step t t') (at level 40).

  (** TRC with step count *)
  Inductive multi_k {X: Type} (R: relation X) : nat -> relation X :=
  | multi_k_refl: forall e,
      multi_k R 0 e e
  | multi_k_trans: forall a b c n,
      R a b ->
      multi_k R n b c ->
      multi_k R (S n) a c.
  Notation " t '==>*' k t' " := (multi_k step k t t') (at level 40).

  Definition circuit_equiv(c: exp) (c': exp): Prop :=
    forall (n: Fp), forall (w: Fp),
        (<{ c' (fp n) (fp w) }> -->* <{ true }> <->
        <{ c (fp n) }> -->* <{ fp w }>). 
  Notation "a '~~' b" := (circuit_equiv a b) (at level 50).

  Fixpoint normalize(e: exp) :=
    match e with
    | tm_app (tm_abs T e1) v1 =>
      open_exp_wrt_exp (normalize e1) (normalize v1)
    | tm_abs T e => tm_abs T e
    | tm_app e1 e2 => tm_app (normalize e1) (normalize e2)
    | tm_let e1 e2 =>
      open_exp_wrt_exp (normalize e2) (normalize e1)
    | tm_binop a op b =>
      tm_binop (normalize a) op (normalize b)
    | tm_eq e1 e2 =>
      tm_eq (normalize e1) (normalize e2)
    | tm_not e1 => tm_not (normalize e1)
    | tm_ifthenelse e e1 e2 =>
      tm_ifthenelse (normalize e) (normalize e1) (normalize e2)
    | e => e
    end.

  Fixpoint normalizer(e: exp)(gas: nat): exp :=
    match gas with
    | 0%nat => e
    | S g' => normalizer (normalize e) g'
    end.

  Definition normalization_lemma: forall e e', (exists G, normalizer e G = e') <-> e -->* e'.
  Admitted.  

  (** Evaluate closures *)
  Inductive fo_type: typ -> Prop :=
  | fo_field: fo_type <{{ Field }}>
  | fo_bool: fo_type <{{ Bool }}>.

  Inductive r1cs_type: typ -> Prop :=
  | ro_unary: forall t, fo_type t -> r1cs_type t
  | ro_pair: forall t b,
      fo_type t ->
      r1cs_type b ->
      r1cs_type <{{ t * b }}>.

  Inductive fo_exp: exp -> Fp -> Prop :=
  | fo_fp: forall p, fo_exp <{ fp p }> p
  | fo_true: fo_exp <{ true }> (1:%p)
  | fo_false: fo_exp <{ false }> (0:%p).
  
  Import VectorNotations.  
  Inductive cannonical: forall n, exp -> typ -> Vfp n -> Prop :=
  | ev_field: forall f, cannonical 1 <{ fp f }> <{{ Field }}> [f]
  | ev_true: cannonical 1 <{ true }> <{{ Bool }}> [1:%p]
  | ev_false: cannonical 1 <{ false }> <{{ Bool }}> [0:%p]
  | ev_pair_true: forall m v e t, 
      cannonical m e t v ->
      <{{ Datatypes.nil |- e :: t }}> ->
      cannonical (S m) <{ {true , e} }> <{{ Bool * t }}> (1:%p :: v)
  | ev_pair_false: forall m v e t,
      cannonical m e t v ->
      <{{ Datatypes.nil |- e :: t }}> ->
      cannonical (S m) <{ {false , e} }> <{{ Bool * t }}> (0:%p :: v)
  | ev_pair_field: forall m f v e t,
      cannonical m e t v ->
      <{{ Datatypes.nil |- e :: t }}> ->
      cannonical (S m) <{ {fp f, e} }> <{{ Field * t }}> (f :: v).
     
  Local Open Scope nat_scope.
  Fixpoint num_arg(e: exp): nat :=
    match e with
    | <{ \_: t, _}> =>
      (fix num_telems t :=
      match t with 
      | <{{ Field * b }}> => 1 + num_telems b
      | <{{ Bool * b }}> => 1 + num_telems b
      | <{{ Field }}> => 1
      | <{{ Bool }}> => 1
      | _ => 0
      end) t
    | _ => 0
    end.

  Fixpoint num_ret(e: exp): nat :=
    match e with
    | <{ a b }> => num_ret a
    | <{ \_: _, b }> => num_ret b
    | <{ {a, b} }> => 1 + num_ret b
    | tm_binop a _ b => 1
    | <{ fst a }> => 1
    | <{ snd b }> => num_ret b - 1
    | <{ if _ then a else _ }> => num_ret a
    | _ => 1
    end.

  Close Scope vector_scope.
  Import ListNotations.
  Definition r1cs_lambda_equiv{n v}(e: exp)
             (cs: @r1cs n (num_arg e) (num_ret e) v): Prop :=
    forall (args: exp)
      (result: exp)
      (inps: Vfp (num_arg e))
      (outs: Vfp (num_ret e))
      (vars: Vfp v) t t'
      (** axioms *)
      (HeT: <{{ [] |- e :: (t -> t') }}>)
      (HcannonIn: cannonical (num_arg e) args t inps)
      (HcannonOut: cannonical (num_ret e) result t' outs),
      (** equivalence relation *)
      <{ e args }> -->* <{ result }> <->
      correct cs inps outs vars.

  Notation "e <=*=> r" := (r1cs_lambda_equiv e r) (at level 50).
  
  Close Scope list_scope.
  Open Scope vector_scope.

  Lemma cannonical_forms_bool_bool: forall e a b,
      cannonical 2 e <{{ Bool * Bool }}> [a; b] ->
      ((e = <{ {true, true} }> /\ a = 1:%p /\ b = 1:%p) \/
       (e = <{ {true, false} }> /\ a = 1:%p /\ b = 0:%p) \/
       (e = <{ {false, true} }> /\ a = 0:%p /\ b = 1:%p) \/
       (e = <{ {false, false} }> /\ a = 0:%p /\ b = 0:%p)).
  Proof.
    intros e a b Hc.
    invert Hc; invert H4; devec1 v; invert H3; invert H. 
    - left; intuition auto.
    - right; left; intuition auto.      
    - right; right; left; intuition auto.
    - right; right; right; intuition auto.
  Qed.

  Lemma cannonical_forms_bool: forall e a,
      cannonical 1 e <{{ Bool }}> [a] ->
      ((e = <{ true }> /\ a = 1:%p) \/ (e = <{ false }> /\ a = 0:%p)).
  Proof.
    intros e a Hc.
    invert Hc. 
    - left; split; reflexivity.
    - right; split; reflexivity.
  Qed.

  Lemma cannonical_forms_field: forall e a,
      cannonical 1 e <{{ Field }}> [a] ->
      e = <{ fp a }>.
  Proof. intros e a Hc; invert Hc; reflexivity. Qed.

  Lemma cannonical_forms_field_bool_bool: forall e a p,
      cannonical 3 e <{{ Field * Bool * Bool }}> [n;b;c] ->
      ((e = <{ {fp p, true, true} }> /\ n = p /\ a = 1:%p /\ b = 1:%p) \/
       (e = <{ {fp p, true, false} }> /\ n = p /\ a = 1:%p /\ b = 0:%p) \/
       (e = <{ {fp p, false, true} }> /\ n = p /\ a = 0:%p /\ b = 1:%p) \/
       (e = <{ {fp p, false, false} }> /\ n = o /\ a = 0:%p /\ b = 0:%p)).
  (**
  Lemma cannonical_forms_ind_prin: forall n a b f bt ts o,
      cannonical (S (S n)) <{ {a,b} }>  <{{ Field * bt }}> (f :: ts) ->
      e = <{ {fp f, a} }> /\ cannonical (S n) o b ts.
  Proof.
    intros n.
    intros.
    remember e as exp.
    induction H.
    induction n; intros; split. 
    - destruct b; invert H; pose proof (vec1_proj v); exists_inverter;deconj; subst.
      + pose proof (cannonical_forms_bool e0 a H5); clear H5; deconj.
        
    intros e b n f ts o H.
    
    induction H.
    split.
    - induction H.
   *)
  Ltac solve_stlc :=
    repeat lazymatch goal with
           | [ |- step (tm_eq ?a ?b) _ ] =>
             apply step_eq_refl || apply step_eq_cog_1 || apply step_eq_cog_2
           | [ |- step (tm_binop _ op_mul _) _ ] => apply step_mul_const
           | [ |- step (tm_app ((tm_abs _ _))  _) _] => eapply step_beta
           | [ H: step ?a ?b |- ?g ] => inversion H; subst; clear H
           | [ H: ?a -->* ?b |- _ ] => idtac "invert -->*";inversion H; subst; clear H
           | [ |- Is_true _ ] => idtac "is_true"; constructor
           | [ H: ?x `notin` ?L |- lc_exp <{ \_: _, _ }> ] =>
             idtac "intro binders"; apply (lc_tm_abs (AtomSetImpl.add ?x ?L)); intros
           | [ |- lc_exp <{ \_ : _, _ }> ] =>
             idtac "empty binders"; apply (lc_tm_abs empty); intros
           | [ |- lc_exp _ ] => idtac "lc_exp"; constructor
           | [ H: context[open_exp_wrt_exp _ _] |- _] => cbn in H
           | [ |- context[open_exp_wrt_exp _ _] ] => cbn
           | [ H: ?a |- ?a ] => exact H
           | [ |- _ -->* _ ] => idtac "forward -->*" ; econstructor; fail
           end.

  Ltac beta :=
    eapply step_beta;
    solve [
        econstructor
      | repeat lazymatch goal with
               | [ H: ?x `notin` ?L |- lc_exp <{ \_: _, _ }> ] =>
                 idtac "intro binders"; apply (lc_tm_abs (AtomSetImpl.add ?x ?L)); intros
               | [ |- lc_exp <{ \_ : _, _ }> ] =>
                 idtac "empty binders"; apply (lc_tm_abs empty); intros
               end
      | repeat econstructor]; repeat econstructor.
  
  Ltac invert_types :=
    lazymatch goal with
           | [ H: ?x `notin` ?L |- lc_exp <{ \_: _, _ }> ] =>
             idtac "intro binders"; apply (lc_tm_abs (AtomSetImpl.add ?x ?L)); intros
           | [ H: context[open_exp_wrt_exp _ _] |- _] => cbn in H
           | [ H: ?a |- ?a ] => exact H
           | [H: <{{ ?G |- ?e :: ?t }}> |- _] => idtac "TYPE" t; inversion H; subst; clear H
           | [H: binds ?x ?t ?G |- _] => idtac "TYPE BINDS" t; inversion H; subst; clear H
           | [H: (?x, ?t) = (?x, ?t') |- _] => match type of t with
                                             | typ => idtac "TYPE EQ"; inversion H; clear H
                                             end
           | [H: List.In (?x, ?t) ?L |- _] => match type of t with
                                            | typ => idtac "TYPE ENV"; inversion H; clear H
                                            end
    end.

  Ltac step_handler P H :=
    lazymatch P with
    | <{ (\_ : ?t, ?b) (?v) }> => idtac "beta [" v "/" b "]"; inversion H; clear H
    | tm_constant ?c => idtac "const" c; inversion H; clear H 
    | <{ if ?c then _ else _ }> => idtac "ite"; inversion H; clear H
    | tm_binop ?a ?x ?b => idtac a x b; inversion H; clear H
    | <{ \_ : ?t, ?b }> => idtac "abs \_: " t "," b; inversion H; clear H
    | <{ {?a, ?b} }> => idtac "pair {" a "," b "}"; inversion H; clear H
    | <{ fst ?a }> => idtac "fst {" a "}"; inversion H; clear H
    | <{ snd ?a }> => idtac "snd {" a "}"; inversion H; clear H
    | ?e => idtac "NO MATCH" e; fail 2
    end; subst.
  
  Ltac invert_stlc :=
    lazymatch goal with
    | [ H: ?x `notin` ?L |- lc_exp <{ \_: _, _ }> ] =>
      idtac "intro binders"; apply (lc_tm_abs (AtomSetImpl.add ?x ?L)); intros
    | [ H: context[open_exp_wrt_exp _ _] |- _] => cbn in H
    | [ H: ?a |- ?a ] => exact H
    | [ H: step ?f ?b |- _] => idtac f "-->" b; step_handler f H
    | [ H: ?f -->* ?b |- _] => idtac f "-->*" b; step_handler f H
    end.


End Gadget.     
