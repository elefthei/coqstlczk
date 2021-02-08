Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Morph.
Require Import Hask.Control.Impl.
Require Import Hask.Control.Compose.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition WriterT (X : Type) (M : Type -> Type) (Y : Type) : Type :=
  (X * Y) -> M Y.

Definition runWritterT {E M A} (r : WriterT E M A) := r.

