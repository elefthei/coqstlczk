Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Strings.String.
Require stdpp.stringmap.
Require Coq.setoid_ring.Ncring.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.setoid_ring.Algebra_syntax.

From STLCZK Require Import Maps.
From STLCZK Require Import StlcRing.
Import StlcRing.StlcRing.

Print StlcRing.

Module StlcGadget.
  
  Definition ty := StlcRing.ty.
  Definition Ty_Arrow := StlcRing.Ty_Arrow.
  Definition Ty_Ring := StlcRing.Ty_Ring.
  
  Local Open Scope string_scope.
  Context {R: Type}`{Coq.setoid_ring.Ncring.Ring_ops R}.

  Print StlcRing.
  Set Implicit Arguments.
  Inductive tm {a:Set} : Type :=
  (* pure STLC *)
  | tm_var : a -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* Bool algebra *)
  |tm_boolc: bool -> tm
  | tm_and : tm -> tm -> tm
  | tm_or : tm -> tm -> tm
  | tm_neg: tm -> tm                        
  (* Ring algebra *)
  |tm_rc: R -> tm
  |tm_opp: tm -> tm
  |tm_add: tm -> tm -> tm
  |tm_mul: tm -> tm -> tm
  |tm_eq: tm -> tm -> tm
  |tm_if: tm -> tm -> tm -> tm
  (* GADGET MACRO *)
  |tm_gadget: string -> tm -> tm -> tm -> tm.

  Declare Custom Entry stlc_gadget.
  Declare Custom Entry stlc_gadget_ty.

  Notation "<[ e ]>" := e (e custom stlc_gadget at level 99).
  Notation "<[[ e ]]>" := e (e custom stlc_gadget_ty at level 99).
  Notation "( x )" := x (in custom stlc_gadget, x at level 99).
  Notation "( x )" := x (in custom stlc_gadget_ty, x at level 99).
  Notation "x" := x (in custom stlc_gadget at level 0, x constr at level 0).
  Notation "x" := x (in custom stlc_gadget_ty at level 0, x constr at level 0).
  Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_gadget_ty at level 50, right associativity).
  Notation "x y" := (tm_app x y) (in custom stlc_gadget at level 1, left associativity).
  Notation "\ x : t , y" :=
    (tm_abs x t y) (in custom stlc_gadget at level 90, x at level 99,
                       t custom stlc_gadget_ty at level 99,
                       y custom stlc_gadget at level 99,
                       left associativity).
  Coercion tm_var : string >-> tm.
  
  Notation "{ x }" := x (in custom stlc_gadget at level 1, x constr).

  Notation "'Ring'" := Ty_Ring (in custom stlc_gadget_ty at level 0).
  Notation "'Bool'" := Ty_Ring (in custom stlc_gadget_ty at level 0).
  Notation "x && y" := (tm_and x y) (in custom stlc_gadget at level 2,
                                        left associativity).
  Notation "x || y" := (tm_or x y) (in custom stlc_gadget at level 2,
                                        left associativity).
  Notation "'opp' x" := (tm_opp x) (in custom stlc_gadget at level 0,
                                        x custom stlc_gadget at level 0).
  Notation "'neg' x" := (tm_neg x) (in custom stlc_gadget at level 0,
                                       x custom stlc_gadget at level 0).
  Notation "x + y" := (tm_add x y) (in custom stlc_gadget at level 2,
                                        left associativity).
  Notation "x * y" := (tm_mul x y) (in custom stlc_gadget at level 2,
                                        left associativity).
  Notation "x == y" := (tm_eq x y) (in custom stlc_gadget at level 1,
                                        left associativity).
  Notation "'if' x 'then' y 'else' z" :=
    (tm_if x y z) (in custom stlc_gadget at level 89,
                       x custom stlc_gadget at level 99,
                       y custom stlc_gadget at level 99,
                       z custom stlc_gadget at level 99,
                       left associativity).
  (* GADGET MACRO binder *)
  (* w= f(x) <-> c(x, w) = true *)
  Notation "'let' w ':=' f 'with' x 'in' c" :=
    (tm_gadget w f x c) (in custom stlc_gadget at level 89,
                          w at level 99,
                          f custom stlc_gadget at level 99,
                          x custom stlc_gadget at level 99,
                          c custom stlc_gadget at level 99,
                          left associativity).
  Coercion tm_rc : R >-> tm.
  Coercion tm_boolc : bool >-> tm.

  Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_gadget at level 20, x constr).
  
  Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    (* pure STLC_GADGET *)
    | tm_var y =>
      if eqb_string x y then s else t
    | <[\y:T, t1]> =>
      if eqb_string x y then t else <[\y:T, [x:=s] t1]>
    | <[t1 t2]> =>
      <[([x:=s] t1) ([x:=s] t2)]>
    (* booleans *)
    | tm_boolc _ => t
    | <[neg t]> => <[ neg ([x:=s] t) ]>
    | <[t1 && t2]> => <[ ([x:=s]t1) && ([x:=s]t2) ]>
    | <[t1 || t2]> => <[ ([x:=s]t1) || ([x:=s]t2) ]>
    (* numbers *)
    | tm_rc _ => t
    | <[opp t]> => <[opp ([x:=s] t)]>
    | <[t1 + t2]> =>
      <[ ([x := s] t1) + ([x := s] t2)]>
    | <[t1 * t2]> =>
      <[ ([x := s] t1) * ([x := s] t2)]>
    | <[t1 == t2]> =>
      <[ ([x := s] t1) == ([x := s] t2)]>
    | <[if t1 then t2 else t3]> =>
      <[if [x := s] t1 then [x := s] t2 else [x := s] t3]>
    | <[let w := f with a in c]> =>
      if eqb_string x w then t else
        <[let w := [x := s]f with [x:=s]a in [x:=s]c]>
    end
  where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_gadget).

  Inductive mode := Verifier(w: StlcRing.tm) | Prover.

  Reserved Notation "t '=' m '=>' t'" (at level 40).
  
  Inductive macro_expand : mode -> tm -> StlcRing.tm -> Prop :=
  (* pure STLC *)
  | M_Abs : forall m x T2 t1 t1' v2 v2',
      t1 =m=> t1' ->
      v2 =m=> v2' ->
      <[ (\x:T2, t1) v2 ]> =m=> <{ (\x:T2, t1') v2' }>
  | ST_App : forall m t1 t2 t1' t2',
      t1 =m=> t1' ->
      t2 =m=> t2' ->
      <[t1 t2]> =m=> <{t1' t2'}>
  (* Bools *)
  |ST_And: forall m b1 b2 b1' b2',
      b1 =m=> b1' ->
      b2 =m=> b2' ->
      <[b1 && b2]> =m=> <{b1' && b2'}>
  |ST_Or: forall m b1 b2 b1' b2',
      b1 =m=> b1' ->
      b2 =m=> b2' ->
      <[b1 || b2]> =m=> <{b1' || b2'}>
  |ST_Neg: forall m b b',
      b =m=> b' ->
      <[ neg b ]> =m=> <{ neg b' }>
  (* Numbers *)
  |ST_Add: forall m n1 n2 n1' n2',
      n1 =m=> n1' ->
      n2 =m=> n2' ->
      <[n1 + n2]> =m=> <{n1' + n2'}>
  |ST_Eq: forall m t1 t2 t1' t2',
      t1 =m=> t1' ->
      t2 =m=> t2' ->
      <[t1 == t2]> =m=> <{t1' == t2'}>
  |ST_Mul: forall m n1 n2 n1' n2',
      n1 =m=> n1' ->
      n2 =m=> n2' ->
      <[n1 * n2]> =m=> <{n1' * n2'}>
  |ST_If: forall m t1 t2 t3 t1' t2' t3',
      t1 =m=> t1' ->
      t2 =m=> t2' ->
      t3 =m=> t3' ->   
      <[ if t1 then t2 else t3 ]> =m=> <{ if t1' then t2' else t3' }>
  (* These are the actual macros *)
  |ST_gadget_Prover: forall f w x c f' x',
      f =Prover=> f' ->                                      (** Bring f' to StlcRing *)
      x =Prover=> x' ->                                      (** Bring x' to StlcRing *)
      <[let w := f with x in c]> =Prover=> <{f' x'}>        (** The prover computes f(x) *)   
  |ST_gadget_Verifier: forall f x c f' x' c',
      f =Verifier(w)=> f' ->                                    (** Bring f' to StlcRing *)
      x =Verifier(w)=> x' ->                                    (** Bring x' to StlcRing *)
      c =Verifier(w)=> c' ->                                    (** Bring c' to StlcRing *)
     
                      (*<{ f' x' }> -->* w' ->                                (** Compute witness w' in Coq proof *)*)
      <[let w := f with x in c]> =Verifier(w)=> <{ if(c' x' w) then w else error }> (** Verifier checks witness c' x' w' *)            
  where "t '=' m '=>' t'" := (macro_expand m t t').
End StlcGadget.

(* A * (Map string R): put (Map String R) -> Writer (Map String R) A
   A -> Map string R : get () -> Reader (Map String R) (Map String R)

{
   forall t: tm, let (o, w) = evalWriter (prove t) in 
      let Some (o') = evalReader w (verify t) in
         o = o'.

   Completeness
   forall w, c(x, w) = true -> f(x) = w
}
{
   Soundness
   forall w, f(x) = w -> c(x, w) = true
}

   Definition prove(in: tm)  : Writer (Map string R) tm
   Definition verify(in: tm) : Reader (Map string R) tm

(* f: forall t, exists o, t -> o
   c: forall t, forall o, t -> o -> Bool

(*

  back-end language: R1CS

  [
    a * b = c,
    c * d = 1, ...]
  
  Frank-Zippel lemma
  --------------------
  (a * b) * d = 1

*)
