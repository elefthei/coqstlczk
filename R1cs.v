Require Import Metalib.Metatheory.
From STLCZK Require Import GaloisField.
From STLCZK Require Import Ltac.
From STLCZK Require Import NonEmpty.
From Coq Require Import micromega.Lia.
Require Import Coqprime.elliptic.ZEll.
Require Import Coq.Numbers.BinNums.
Require Import Coqprime.elliptic.GZnZ.
Require Import Coq.ZArith.BinIntDef.
Import Z.
Require Import Coq.Init.Nat.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Vectors.Fin.

Set Implicit Arguments.
Set Printing Implicit.

Module R1CS(PF: GaloisField).
  Import PF.
  Import VectorNotations.
  Definition Vfp := Vector.t Fp.

  Inductive term: Set :=
  | input(n: nat): term
  | var(n: nat): term
  | output: term
  | one: term.

  Local Open Scope nat_scope.
  
  Definition term_eq(a b: term): bool :=
    match a,b with
    | input n, input n' => n =? n'
    | var n, var n' => n =? n'
    | output, output => true
    | one, one => true
    | _, _ => false
    end.  
                                 
  Definition additions :=
    NonEmpty (Fp*term).
  
  Inductive constraint: Set :=
  | lc (A: additions) (B: additions) (C: additions).

  Definition r1cs :=
    NonEmpty constraint.

  Class Computable(A : Type)(R: Type) :=
    {
    (** Substitute input i[n] with given term, i[S n] -> i[n] *)
    subst: A -> nat -> term -> A;

    rewrite: A -> term -> term -> A;
    
    (** Get number of free inputs *)
    num_inputs: A -> nat;
    
    (** Get number of free vars *)
    num_vars: A -> nat;

    (** Shift inputs right by n *)
    shift_inputs: A -> nat -> A;

    (** Shift vars right by n *)
    shift_vars: A -> nat -> A;

    (* Well-formed *)
    wf: A -> Prop;
    
    (** Evaluate to a number *)
    eval{i v}(a: A):
                     num_inputs a <= i ->
                     num_vars a <= v -> 
                     Vfp i ->
                     Vfp v ->
                     Fp ->
                     R;
    
    }.
  
  (** syntax *)
  Declare Custom Entry r1cs.

  Notation "<[ a ]>" :=
    (@NE_Sing constraint a) (at level 1, a custom r1cs at level 2).
  
  Notation "<[ a1 ; .. ; a2 ; a3 ]>" :=
    (@NE_Cons constraint a1 .. (@NE_Cons constraint a2 (@NE_Sing constraint a3)) ..)
      (at level 1,
       a1 custom r1cs at level 2,
       a2 custom r1cs at level 2,
       a3 custom r1cs at level 2).
  
  Notation "'{' a '*' b '==' c '}'" :=
    (lc a b c)
      (in custom r1cs at level 2,
          a custom r1cs at level 3,
          b custom r1cs at level 3,
          c custom r1cs at level 3,
          left associativity).

  Notation "( a )" :=
    (@NE_Sing (Fp*term) a) (in custom r1cs at level 3, a custom r1cs at level 4).
  
  Notation "( a1 + .. + a2 + a3 )" :=
    (@NE_Cons (Fp*term) a1 .. (@NE_Cons (Fp*term) a2 (@NE_Sing (Fp*term) a3)) ..)
      (in custom r1cs at level 3,
          a1 custom r1cs at level 4,
          a2 custom r1cs at level 4,
          a3 custom r1cs at level 4).
  
  Notation "z 'i[' n ']'" :=
    ((to_p z), input n%nat)
      (in custom r1cs at level 4,
          n constr,
          z constr).
  
  Notation "z 'o'" :=
    ((to_p z), output)
      (in custom r1cs at level 4,
          z constr).
  
  Notation "z 'v[' n ']'" :=
    ((to_p z), var n%nat)
      (in custom r1cs at level 4,
          n constr,
          z constr).

  Notation "[ z ]" :=
    ((to_p z), one)
      (in custom r1cs at level 4,
          z constr at level 0).

  Definition r1cs_singleton(c: constraint): r1cs :=
    NE_Sing c.
 
  Coercion r1cs_singleton: constraint >-> r1cs.

  Eval cbn in <[
                { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) };
              { (3o + 3i[1]) * (3i[0] + 2v[2]) == ([1]) }  ]>.  

  Lemma Nat_max_lub_if: forall n m p : nat, Nat.max n m <= p -> n <= p /\ m <= p.
  Proof. intros. split; lia. Defined.

  #[refine] Instance term_Computable: Computable term Fp :=
    {
    subst t n k :=
      match t with
      | input n' => match compare n n' with
                     | Eq => k
                     | Gt => t
                     | Lt => input (n' -1)
                     end
      | _ => t
      end;

      rewrite trm t t' := if term_eq t trm then t' else
                            match t, trm with
                            | input a, input b => if a <? b then input (b-1) else trm
                            | var a, var b => if a <? b then var (b-1) else trm
                            | _, _ => trm
                            end;
    
    num_inputs t :=
        match t with
        | input n => S n
        | _ => 0%nat
        end;

    shift_inputs t n :=
          match t with
          | input n' => input (n + n')
          | _ => t
          end;
          
    shift_vars t n :=
          match t with
          | var n' => var (n + n')
          | _ => t
          end;
           
    num_vars t :=
            match t with
            | var n => S n
            | _ => 0%nat
            end;

    wf := fun _ => True
    }.
  intros i v a Hi Hv inps vars out; destruct a eqn:Ha.
  - exact (Vector.nth inps (Fin.of_nat_lt Hi)).
  - exact (Vector.nth vars (Fin.of_nat_lt Hv)).
  - exact out.
  - exact (1:%p).
  Defined.

  #[refine] Instance additions_Computable: Computable additions Fp :=
    {
    subst t n k := NE_map (fun p => match p with
                                 | (f, x) => (f, subst x n k)
                                 end) t;

    rewrite a t t' := NE_map (fun p => match p with
                                    | (f, x) => (f, rewrite x t t')
                                    end) a;
    num_inputs t :=
      NE_max (NE_map (fun p => match p with
                            | (f, x) => num_inputs x
                            end) t);

    num_vars t :=
        NE_max (NE_map (fun p => match p with
                              | (f, x) => num_vars x
                              end) t); 

    shift_inputs t n :=
          NE_map (fun p => match p with
                        | (f, x) => (f, shift_inputs x n)
                        end) t; 
        
    shift_vars t n :=
            NE_map (fun p => match p with
                          | (f, x) => (f, shift_vars x n)
                          end) t;
    wf a := True; 
    }.
  intros i v a; induction a; intros Hi Hv inps vars out.
  - rewrite NE_map_sing in Hi, Hv.
    apply NE_max_sing in Hi.
    apply NE_max_sing in Hv.
    destruct a.
    exact (pkmul f (eval t Hi Hv inps vars out)).
  - rewrite NE_map_cons in Hi, Hv.
    destruct a.
    remember (num_inputs t) as ih.
    remember (NE_map (fun p => match p with
                            | (f, t) => num_inputs t
                            end) a0) as its.
    remember (num_vars t) as vh.
    remember (NE_map (fun p => match p with
                            | (f, t) => num_vars t
                            end) a0) as vts.
    apply NE_max_cons in Hv; destruct Hv.
    apply NE_max_cons in Hi; destruct Hi.
    rewrite Heqvh in H.
    rewrite Heqih in H1.
    exact (pkplus
             (IHa H2 H0 inps vars out)
             (pkmul f (eval t H1 H inps vars out))).
  Defined.

  #[refine] Instance constraint_Computable: Computable constraint Fp :=
    {
    subst t n k :=
      match t with lc a b c => lc (subst a n k) (subst b n k) (subst c n k) end;

    rewrite c t t' :=
      match c with lc a b c => lc (rewrite a t t') (rewrite b t t') (rewrite c t t') end;
        
    num_inputs t :=
      match t with lc a b c => max (num_inputs a) (max (num_inputs b) (num_inputs c)) end;
                
    num_vars t :=
      match t with lc a b c => max (num_vars a) (max (num_vars b) (num_vars c)) end;

    shift_inputs t n :=
      match t with lc a b c => lc (shift_inputs a n) (shift_inputs b n) (shift_inputs c n) end;

    shift_vars t n :=
      match t with lc a b c => lc (shift_vars a n) (shift_vars b n) (shift_vars c n) end;
        
     wf a := True
    }.
  intros i v a H H0 inps vars out; destruct a eqn:Ha; subst.
  destruct (Nat_max_lub_if _ _ H); clear H.
  destruct (Nat_max_lub_if _ _ H0); clear H0.
  destruct (Nat_max_lub_if _ _ H2); clear H2.
  destruct (Nat_max_lub_if _ _ H3); clear H3.
  pose proof (eval A H1 H inps vars out) as RA.
  pose proof (eval B H0 H2 inps vars out) as RB.
  pose proof (eval C H4 H5 inps vars out) as RC.
  exact (pksub (pkmul RA RB) RC).
  Defined.

  #[refine] Instance r1cs_Computable: Computable r1cs Prop :=
    {
    subst t n k := NE_map (fun x => subst x n k) t;

    rewrite r t t' := NE_map (fun x => rewrite x t t') r;
                                      
    num_inputs t :=
      NE_max (NE_map num_inputs t);
        
    num_vars t :=
        NE_max (NE_map num_vars t); 
    shift_inputs t n :=
        NE_map (fun x => shift_inputs x n) t; 
        
    shift_vars t n :=
        NE_map (fun x => shift_vars x n) t;
          
    wf a := True
    }.
  intros i v a; induction a; intros Hi Hv inps vars out.
  - rewrite NE_map_sing in Hi, Hv.
    apply NE_max_sing in Hi.
    apply NE_max_sing in Hv.
    exact (eval a Hi Hv inps vars out = 0:%p).
  - rewrite NE_map_cons in Hi, Hv.
    apply NE_max_cons in Hi.
    apply NE_max_cons in Hv.
    destruct Hi.
    destruct Hv.
    exact (IHa H0 H2 inps vars out /\ eval a H H1 inps vars out = 0:%p).
  Defined.

  Definition correct(r: r1cs)
             (inputs: Vfp (num_inputs r))
             (output: Fp)
             (vars: Vfp (num_vars r)): Prop :=
    @eval r1cs Prop r1cs_Computable
     (@num_inputs r1cs Prop r1cs_Computable r)
     (@num_vars r1cs Prop r1cs_Computable r)
     r
     (Nat.le_refl (@num_inputs r1cs Prop r1cs_Computable r))
     (Nat.le_refl (@num_vars r1cs Prop r1cs_Computable r))
     inputs
     vars
     output.     

  Import VectorNotations.
  Unset Printing Implicit.

  Lemma example_correct1:
    correct <[ { (1i[0]) * (1i[1]) == (1o) } ]> [1:%p; 1:%p] 1:%p [].
  Proof.
    unfold correct.
    cbn.
    autorewrite with pk using trivial.
  Qed.

  (** Take the left circuit,
      make its output o, the nth input of the second circuit:

      @r1cs i v -> @r1cs i' v' -> @r1cs (i +i' -1) (v + v' +1) 
   *)
  Definition compose(a: r1cs)(b: r1cs)(n: nat): r1cs :=
    let b_nvars := num_vars b in
    let a_nvars := num_vars a in
    let cvar := var (b_nvars + a_nvars) in
    NE_app (
        rewrite 
          (shift_vars
             (shift_inputs a (num_inputs b - 1))
             b_nvars
          ) output cvar)
           (rewrite b (input n) cvar).

  Eval cbn in rewrite (<[ {(1 i[ 0]) * (1 i[ 1]) == (1 o)} ]>) (input 0) output.
  Eval cbn in 
    compose
      (<[ {(1 i[ 0]) * (1 i[ 1]) == (1 o)} ]>)                   (* andb i[0] i[1] *)
      (<[ { (1i[0] + [-1]) * ([1] + -1i[1]) == (1o + [-1]) } ]>) (* orb i[0] i[1] *)
      1.

  Definition WF_inputs{i v}(r: r1cs)(inputs: Vfp i)(vars: Vfp v) :=
    num_vars r = v /\ num_inputs r  = i.    

End R1CS.

(*
Section phoas.
  Variable var: Type.

  Inductive exp: Type :=
  | Var: var -> exp
  | Abs: (var -> exp) -> exp
  | App: exp -> exp -> exp.

End phoas.

Definition Exp: Type := forall v: Type, exp v.
*)
  
