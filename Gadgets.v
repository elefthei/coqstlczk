Require Import Metalib.Metatheory.
Require Import Bool.
From STLCZK Require Import GaloisField.
From STLCZK Require Import R1cs.
From STLCZK Require Import Ltac.

Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Vectors.VectorDef.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.

Generalizable All Variables.

Module Gadget(PF: GaloisField).
  Import PF.
  Include R1CS PF.

  Import MonadNotation.
  Open Scope monad_scope.
  Open Scope nat_scope.

  Inductive r1cs_equiv: forall i v, exp -> @r1cs i v -> Prop :=
  | BaseTrue: forall e v (r: @r1cs 0 v) (vars: Vfp v),
      <{ e }> -->* <{ true }> ->
      correct r (Vector.nil Fp) vars (1:%p) ->
      r1cs_equiv 0 v e r
  | BaseFalse: forall v e (r: @r1cs 0 v) (vars: Vfp v),
      <{ e }> -->* <{ false }> ->
      correct r (Vector.nil _) vars (0:%p) ->
      r1cs_equiv 0 v e r
  | BaseField: forall v e (r: @r1cs 0 v) (vars: Vfp v) p,
      <{ e }> -->* <{ fp p }> ->
      correct r (Vector.nil _) vars p ->
      r1cs_equiv 0 v e r
  | Step: forall v i e (r: @r1cs (S i) v) t t' (vars: Vfp v),
      <{{ [] |- e :: (t -> t') }}> ->
      fo_type t ->
      (forall (inputs: Vfp (S i)) arg,
          fo_value arg t (hd inputs) ->
          r1cs_equiv (S i-1) v <{ e arg }> (substitute_r1cs r (hd inputs))) -> 
      r1cs_equiv (S i) v e r.

  Arguments r1cs_equiv {i} {v}.
  Notation "e <=*=> r" := (r1cs_equiv e r) (at level 50).

  Fixpoint max_closed(m:nat)(e: exp): nat :=
    match e with
    | tm_var_b n => Nat.max m n
    | tm_let e1 e2 => Nat.max (max_closed m e1) (max_closed m e2)
    | tm_binop e1 _ e2 => Nat.max (max_closed m e1) (max_closed m e2)
    | tm_eq e1 e2 => Nat.max (max_closed m e1) (max_closed m e2)
    | tm_not e => max_closed m e
    | tm_ifthenelse e e1 e2 =>
      Nat.max (max_closed m e) (Nat.max (max_closed m e1) (max_closed m e2))
    | _ => m
    end.

  
  Fixpoint letfix(e: exp): state nat exp :=
    _ <- put (S (max_closed 0%nat e)) ;;
    match e with
    | tm_abs t e =>
      e' <- letfix e ;;
      ret (tm_abs t e')
    | tm_app e1 e2 =>
      e1' <- letfix e1 ;;
      e2' <- letfix e2 ;;
      ret (tm_app e1' e2')
    | tm_let e1 e2 =>
      e1' <- letfix e1 ;;
      e2' <- letfix e2 ;;
      ret (tm_let e1' e2')
    | tm_binop e1 op e2 =>
      e1' <- letfix e1 ;;
      e2' <- letfix e2 ;;
      m <- get ;;
      _ <- put (S m) ;;
      ret <{ let {tm_binop e1' op e2'} in {tm_var_b (S m)} }>
    | tm_ifthenelse e e1 e2 =>
      e' <- letfix e ;;
      e1' <- letfix e1 ;;
      e2' <- letfix e2 ;;
      m <- get ;;
      _ <- put (S m) ;;
      ret <{ let (if e' then e1' else e2') in {tm_var_b m} }>
    | tm_not e =>
      e' <- letfix e ;;
      m <- get ;;
      _ <- put (S m) ;;
      ret <{ let {tm_not e'} in {tm_var_b m} }>
    | tm_eq e1 e2 =>
      e1' <- letfix e1 ;;
      e2' <- letfix e2 ;;
      m <- get ;;
      _ <- put (S m) ;;
        ret <{ let {tm_eq e1' e2'} in {tm_var_b m} }>
    | _ => ret e
    end.

  Eval cbn in (evalState (letfix
                          <{ \_: Bool, \_: Bool,
                                           #0 && #1 || #0 }>) (0%nat)). 

  (** e: <{{ G |- e :: Field -> Field -> Field }}> 
      <{ \_: Field, \_: Field, let #0 + #1 in #0 }>
      num_inputs: 2,
      num_vars: 1

    e: <{{ G |- e :: Bool -> Field -> Field -> Field }}> 
      <{ \_: Field, \_: Field, let #0 + #1 in #0 }>
      num_inputs: 2,
      num_vars: 1

  Definition fo_compile(e: exp): @r1cs (num_inputs e) (num_vars e) :=
    match e with
    | <{ if a then b else c }> =>  <[ { (1i[0]) * (1i[2] + -1i[1]) == (1v + -1i[1]) } ]>.
    
  Fixpoint compile(e: exp) : (@r1cs (num_inputs e) (num_vars e) * var e) :=
    match e with
    | <{\_: t, e }> =>
    | <{ let a in b }> =>
      let (ra, va) := compile a in
        let (rb, vb) := compile b in
        (r1cs_compose va ra rb, vb)
    | <{ if a then b else c }> =>
      let (ra, va) := compile a in
      let (rb, vb) := compile b in
      let (rc, vc) := compile c in
      let vd := fresh in
      
      (<[ { (1va) * (1vc + -1vb) == (1vd + -1vb) } ]>, vd)

*)
        
  (** Useful Ltac scripts *)
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

  
  Ltac typer :=
    lazymatch goal with
    | [|- <{{ _ |- <{ \_ : _, _ }> :: _}}>] => eapply typing_abs; intros; cbn
    | [|- <{{ _ |- <{ if _ then _ else _ }> :: _ }}>] => eapply typing_if; constructor; cbn
    | [|- (?x, ?T) = (?x, ?T) \/ _] => left; reflexivity
    | [|- _ \/ (?x, ?T) = (?x, ?T) ] => right; reflexivity
    | [|- _ \/ (?x1, ?T1) = (?x2, ?T2) ] => left
    | [|- (?x1, ?T1) = (?x2, ?T2) \/ _ ] => right
    | [|- uniq _ ] => repeat constructor; eassumption
    end.
  
End Gadget.     
