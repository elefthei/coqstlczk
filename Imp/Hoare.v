From Coq Require Import Vectors.Fin.
From Coq Require Import Nat.

From ExtLib Require Import
     Data.Map.FMapPositive
     Data.Positive.

Set Implicit Arguments.
Set Strict Implicit.

Definition var := positive.
Inductive const :=
| CNum(n: nat)
| CBool(b: bool).

Definition env := pmap const.

Inductive type :=
| TBool: type
| TNum: type
| TUnit: type.

(* | TArray: nat -> type -> type. *)

Declare Custom Entry hoare_ty.
Notation "<{{ e }}>" := e (e custom hoare_ty at level 99).
Notation "( x )" := x (in custom hoare_ty, x at level 99).
Notation "x" := x (in custom hoare_ty at level 0, x constr at level 0).  
Notation "'Num'" := TNum (in custom hoare_ty at level 0).
Notation "'Bool'" := TBool (in custom hoare_ty at level 0).
(* Notation "t '[' n ']'" := (TArray n t) (in custom hoare_ty at level 90,
                                           t custom hoare_ty). *)

(** Try fin t de-brujn indices *)
Inductive expr: type -> Type :=
| ENum: nat -> expr <{{ Num }}>
| EBool: bool -> expr <{{ Bool }}>
| EVar: forall t, var -> expr t
| EAdd: expr <{{ Num }}> -> expr <{{ Num }}> -> expr <{{ Num }}>
| EEq: expr <{{ Num }}> -> expr <{{ Num }}> -> expr <{{ Bool }}>.


 (* a -> b
   a x b -> bool *)
Inductive com: Type :=
| CAsgn: forall t, var -> expr t -> com
| CSkip: com
| CSeq: com -> com -> com
| CIf: expr <{{ Bool }}> -> com -> com -> com
| CWhile: expr <{{ Bool }}> -> com -> com
(* Non-deterministic check *)
| CNondet: com -> expr <{{ Bool }}> -> com.

Arguments EVar {t}.
Arguments CAsgn {t}.

Declare Scope com_scope.
Declare Custom Entry com.

Notation "'#' v" := (EVar v) (in custom com at level 0).
Notation "'true'"  := true (at level 1).
Notation "'true'" := (EBool true) (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'" := (EBool false) (in custom com at level 0).
Notation "<{ e }>" := e (e custom com at level 99).
Notation "( x )" := x (in custom com, x at level 99).
Notation "x" := x (in custom com at level 0, x constr at level 0).

Notation "a '+' b" := (EAdd a b) (in custom com at level 50, left associativity).
Notation "a '==' b" := (EEq a b) (in custom com at level 50, left associativity).

Notation "'skip'"  :=
  CSkip (in custom com at level 0) : com_scope.

Notation "x := y"  :=
  (CAsgn x y)
    (in custom com at level 0, x constr at level 0,
        y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (CSeq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z" :=
  (CIf x y z)
    (in custom com at level 89, x at level 99,
        y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y" :=
  (CWhile x y)
    (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Notation "'[' y ']' 'with' z" :=
  (CNondet y z)
    (in custom com at level 90,
    y at level 85, z at level 85, no associativity): com_scope.
         
Local Open Scope com_scope.
Coercion ENum: nat >-> expr.
Coercion EBool: bool >-> expr.

Reserved Notation "t '/' st '-e->' t'" (at level 40, st at level 39, t' at level 39).
Inductive estep: forall t, env -> expr t -> expr t -> Prop :=
| EStepVarNum: forall st k n,
    pmap_lookup k st = Some (CNum n) ->
    <{ # k }> / st -e-> <{ n }>
| EStepVarBool: forall st k b,
    pmap_lookup k st = Some (CBool b) ->
    <{ # k }> / st -e-> <{ b }>
| EStepAdd: forall st a b na nb,
    a / st -e-> (ENum na) ->
    b / st -e-> (ENum nb) ->
    <{ a + b }> / st -e-> <{ (na + nb) }>
| EStepEq: forall st a b na nb,
    a / st -e-> (ENum na) ->
    b / st -e-> (ENum nb) ->
    <{ a == b }> / st -e-> (EBool (eqb na nb))
where "t '/' st '-e->' t'" := (estep st t t').

Reserved Notation " t '/' st '-->' t' '/' st' " (at level 40, st at level 39, t' at level 39).
Inductive cstep: (env * com) -> (env * com) -> Prop :=
| CStepAsgnCong: forall x T (t t': expr T) st,
    t / st -e-> t' ->
    <{ x := t }> / st --> <{ x := t' }> / st
| CStepAsgnVal: forall x st (n: nat),
    <{ x := n }> / st --> <{ skip }> / (pmap_insert x (CNum n) st)
| CSkipSeq: forall t st,
    <{ skip; t }> / st --> <{ t }> / st
| CSkipCong: forall t1 t2 t1' st st',
    t1 / st --> t1' / st' ->
    <{ t1 ; t2 }> / st --> <{ t1' ; t2 }> / st'
| CIfTrue: forall c t1 t2 st,
    c / st -e-> <{ true }> ->
    <{ if c then t1 else t2 }> / st --> t1 / st
| CIfFalse: forall c t1 t2 st,
    c / st -e-> <{ false }> ->
    <{ if c then t1 else t2 }> / st --> t2 / st
| CIfCong: forall c c' t1 t2 st,
    c / st -e-> c' ->
    <{ if c then t1 else t2 }> / st --> <{ if c' then t1 else t2 }> / st
| CWhileStep: forall c t st,
    <{ while c do t }> / st --> <{ if c then (while c do t) else skip }> / st
where " t '/' st '-->' t' '/' st' " := (cstep (st,t) (st',t')).

Inductive trsys{A}(r: A -> A -> Prop): A -> A -> Prop :=
| Refl: forall a,
    trsys r a a
| Step: forall a b c,
    r a b ->
    trsys r b c ->
    trsys r a c.
  
Notation "t '/' st '==>' t' '/' st'" :=
  (trsys cstep (t, st) (t', st'))
  (at level 40, st at level 39, t' at level 39).
