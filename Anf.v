Require Import Metalib.Metatheory.
Require Import Bool.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Stlc.
From STLCZK Require Import R1cs.
From STLCZK Require Import Ltac.

Require Import Coq.Vectors.VectorDef.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import Coq.Init.Nat.


Generalizable All Variables.

Module Anf(PF: GaloisField).
  Import PF.
  Include Stlc PF.
  Import ListNotations.
  Local Open Scope nat_scope.

  Definition var := nat.
  
  Inductive anfexp : Set :=
  | Let(n: var)(l: cexp)(e: exp)
  | Cexp(e: cexp)
  | Aexp(e: aexp)
  with cexp: Set :=
  | App(f: aexp)(v: aexp)
  | If(c: aexp)(t: cexp)(e: cexp)
  with aexp: Set :=
  | Num(f: Fp)
  | Boolean(b: bool)
  | Var(v: var)
  | Primop(o: op) (l: aexp) (r: aexp)
  | Eq(l: aexp)(r: aexp)
  | Not(l: aexp)
  | Lambda(i: nat) (e: exp).

  Definition is_primop(e: exp): bool :=
    match e with
    | tm_binop a op b =>
      if is_value_of_exp a && is_value_of_exp b then
        true
      else
        false
    | tm_eq a b =>
      if is_value_of_exp a && is_value_of_exp b then
        true
      else
        false
    | _ => false
    end.

  Definition max_binder(e: exp): nat :=
    let fix max_binder_list e' :=
      match e' with
      | tm_var_b n => [n]
      | tm_var_f x => []
      | tm_abs _ e => max_binder_list e
      | tm_app l r => max_binder_list l ++ max_binder_list r
      | tm_let l r => max_binder_list l ++ max_binder_list r
      | tm_constant _ => []
      | tm_binop l _ r => max_binder_list l ++ max_binder_list r
      | tm_eq l r => max_binder_list l ++ max_binder_list r
      | tm_not e => max_binder_list e
      | tm_ifthenelse e l r =>
        max_binder_list e ++ max_binder_list l ++ max_binder_list r
      end in
    let fix list_max l n := match l with
                            | [] => n
                            | h:: ts => if n <? h then list_max ts h else list_max ts n
                            end in
    list_max (max_binder_list e) 0.
  
  Fixpoint normalize (e: exp)(k: anfexp -> anfexp): anfexp :=
    match e with
    | tm_abs _ body => k (Lambda (max_binder body) (normalize-term body))
    | tm_let m1 m2 =>
      normalize m1
                (fun n1 =>
                   Let (max_binder e) n1 (normalize m2 k))
    | tm_ifthenelse m1 m2 m3 =>
      normalize-name m1 (fun t =>
                           k (If t (normalize-term m2) (normalize-term m3)))
    | tm_binop m1 op m2 =>
      if is_primop e then
        normalize-name m1 (fun t1 =>
                             normalize-name m2 (fun t2 =>
                                                  k (Primop op t1 t2)))
      else
        normalize m1 (fun t1 =>
                        normalize m2 (fun t2 =>
                                        k (Primop t1 t2))) (** TODO: This is not an aexp *)
    | tm_app m1 m2 =>
      normalize m1 (fun t1 =>
                      normalize m2 (fun t2 =>
                                      k (App t1 t2)))
    | tm_eq m1 m2 =>
       if is_primop e then
        normalize-name m1 (fun t1 =>
                             normalize-name m2 (fun t2 =>
                                                  k (Eq op t1 t2)))
      else
        normalize m1 (fun t1 =>
                        normalize m2 (fun t2 =>
                                        k (Eq t1 t2))) (** TODO: This is not an aexp *)
    | tm_not e => normalize e (fun t =>
                                k (Not t))
    | value => k (
      
        
                    
                             
                                                               
                                          
