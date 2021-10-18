From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.

Module Maps.

Definition eqb_string (x y : string) : bool :=
    if string_dec x y then true else false.

Theorem eqb_str_ref: forall s : string,
    true = eqb_string s s.
Proof.
    intros s.
    unfold eqb_string.
    destruct (string_dec s s) as [Heq|Hnoteq].
    - reflexivity.
    - unfold not in Hnoteq.
      assert (H:s=s). { reflexivity. }
      apply Hnoteq in H.
      destruct H.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
    intros x y.
    unfold eqb_string.
    destruct (string_dec x y) as [Heq|Hneq].
    - split.
      + intros. apply Heq.
      + intros. reflexivity.
    - split.
      + intros. discriminate H.
      + intros. unfold not in Hneq. apply Hneq in H. destruct H.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
    intros x y.
    unfold eqb_string.
    destruct (string_dec x y) as [Heq|Hneq].
    - split.
      + intros. discriminate H.
      + intros. apply H in Heq. destruct Heq.
    - split.
      + intros. apply Hneq.
      + intros. reflexivity.
Qed.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
    (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
    fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
    (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
    (at level 100, v at next level, right associativity).

End Maps.



Import Maps.

Module AExp.

Definition state := total_map nat.
Definition empty_st := (_ !-> 0).

Inductive aexp : Type :=
    | ANum (n : nat)
    | AId (x : string)
    | APlus (a1 a2 : aexp)
    | AMinus (a1 a2 : aexp)
    | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
    | BTrue
    | BFalse
    | BEq (a1 a2 : aexp)
    | BLe (a1 a2 : aexp)
    | BNot (b : bexp)
    | BAnd (b1 b2 : bexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

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
    | <{~ b}> => negb (beval st b)
    | <{b1 && b2}> => andb (beval st b1) (beval st b2)
    end.

Inductive com : Type :=
    | CSkip
    | CAsign (x : string) (a : aexp)
    | CSeq (c1 c2 : com)
    | CIf (b : bexp) (c1 c2 : com)
    | CWhile (b : bexp) (c : com).

Notation "'skip'" :=
        CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
        (CAsign x y)
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

Definition fact_in_coq : com :=
    <{
    Z := X;
    Y := 1;
    while ~(Z = 0) do
        Y := Y * Z;
        Z := Z - 1
    end
    }>.

End AExp.
