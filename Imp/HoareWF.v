From Coq Require Import Vectors.Fin.
From Coq Require Import Nat.
From PLF Require Import Maps.

Inductive type :=
| TBool: type
| TNum: type.
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
| EVar: forall t, nat -> expr t
| EAdd: expr <{{ Num }}> -> expr <{{ Num }}> -> expr <{{ Num }}>
| EEq: expr <{{ Num }}> -> expr <{{ Num }}> -> expr <{{ Bool }}>.

Inductive com: Type :=
| CAsgn: forall t, nat -> expr t -> com
| CSkip: com
| CSeq: com -> com -> com
| CIf: expr <{{ Bool }}> -> com -> com -> com
| CWhile: expr <{{ Bool }}> -> com -> com
(* Gadget *)
| CNDAsng: nat -> com
| CAssert: expr <{{ Bool }}> -> com.


Notation 
Inductive expr t :=
| 
