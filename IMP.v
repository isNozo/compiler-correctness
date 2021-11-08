From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.

(* Defining state *)

Definition state := string -> nat.

Definition empty_st : state :=
    fun _ => 0.

Definition update_st (st : state) (x : string) (n : nat) : state :=
    fun x' => if (string_dec x x') then n else st x'.

Notation "x '!->' n ';' st" := (update_st st x n)
    (at level 100, n at next level, right associativity).
Notation "x '!->' n" := (x !-> n ; empty_st)
    (at level 100).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(* Defining Syntax for expression *)

Inductive aexp : Type :=
    | ANum : nat -> aexp
    | AId : string -> aexp
    | APlus : aexp -> aexp -> aexp
    | AMinus : aexp -> aexp -> aexp
    | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
    | BTrue : bexp
    | BFalse : bexp
    | BEq : aexp -> aexp -> bexp
    | BLe : aexp -> aexp -> bexp
    | BNot : bexp -> bexp
    | BAnd : bexp -> bexp -> bexp.

(* Defining Notation for expression *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

(* Defining evaluation for expression *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
    match a with
    | ANum n => n
    | AId x => st x
    | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
    | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
    | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
    end.

Fixpoint beval (st : state) (b : bexp) : bool :=
    match b with
    | <{true}> => true
    | <{false}> => false
    | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
    | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
    | <{~ b1}> => negb (beval st b1)
    | <{b1 && b2}> => andb (beval st b1) (beval st b2)
    end.

(* Defining Syntax for command *)

Inductive com : Type :=
    | CSkip : com
    | CAsgn : string -> aexp -> com
    | CSeq : com -> com -> com
    | CIf : bexp -> com -> com -> com
    | CWhile : bexp -> com -> com.

(* Defining Notation for command *)

Notation "'skip'" :=
        CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
        (CAsgn x y)
           (in custom com at level 0, x constr at level 0,
            y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
        (CSeq x y)
          (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
        (CIf x y z)
          (in custom com at level 89, x at level 99,
           y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
        (CWhile x y)
           (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(* Defining evaluation for command as a relation *)

Reserved Notation
    "st '=[' c ']=>' st'"
    (at level 40, c custom com at level 99,
     st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
     | E_Skip : forall st,
         st =[ skip ]=> st
     | E_Asgn : forall st a n x,
         aeval st a = n ->
         st =[ x := a ]=> (x !-> n ; st)
     | E_Seq : forall c1 c2 st st' st'',
         st =[ c1 ]=> st' ->
         st' =[ c2 ]=> st'' ->
         st =[ c1 ; c2 ]=> st''
     | E_IfTrue : forall st st' b c1 c2,
         beval st b = true ->
         st =[ c1 ]=> st' ->
         st =[ if b then c1 else c2 end]=> st'
     | E_IfFalse : forall st st' b c1 c2,
         beval st b = false ->
         st =[ c2 ]=> st' ->
         st =[ if b then c1 else c2 end]=> st'
     | E_WhileFalse : forall b st c,
         beval st b = false ->
         st =[ while b do c end ]=> st
     | E_WhileTrue : forall st st' st'' b c,
         beval st b = true ->
         st =[ c ]=> st' ->
         st' =[ while b do c end ]=> st'' ->
         st =[ while b do c end ]=> st''
     where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
    empty_st
    =[
       X := 2;
       if (X <= 1)
         then Y := 3
         else Z := 4
       end
    ]=>
    (Z !-> 4 ; X !-> 2).
Proof.
    apply E_Seq with (X !-> 2).
    - apply E_Asgn. simpl. reflexivity.
    - apply E_IfFalse.
      + simpl. reflexivity.
      + apply E_Asgn. simpl. reflexivity.
Qed.
