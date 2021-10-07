From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.

Module AExp.

Inductive aexp : Type :=
    | ANum (n : nat)
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

Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

Example test_aeval : 
    aeval (APlus (ANum 1) (AMult (ANum 2) (ANum 3))) = 7.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => (aeval a1) =? (aeval a2)
    | BLe a1 a2 => (aeval a1) <=? (aeval a2)
    | BNot b => negb (beval b)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

Example test_beval : 
    beval (BAnd BTrue (BEq (ANum 2) (ANum 3))) = false.
Proof. reflexivity. Qed.

Fixpoint optimize_0Plus (a:aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) a2 => optimize_0Plus a2
    | APlus a1 a2 => APlus (optimize_0Plus a1) (optimize_0Plus a2)
    | AMinus a1 a2 => AMinus (optimize_0Plus a1) (optimize_0Plus a2)
    | AMult a1 a2 => AMult (optimize_0Plus a1) (optimize_0Plus a2)
    end.

Theorem optimize_0Plus_sound: forall a,
    aeval (optimize_0Plus a) = aeval a.
Proof.
    intros a.
    induction a.
    - simpl. reflexivity.
    - destruct a1.
      + destruct n.
        * simpl. rewrite IHa2. reflexivity.
        * simpl. rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1.
        rewrite IHa1. rewrite IHa2.
        reflexivity.
      + simpl. simpl in IHa1.
        rewrite IHa1. rewrite IHa2.
        reflexivity.
      + simpl. simpl in IHa1.
        rewrite IHa1. rewrite IHa2.
        reflexivity.
    - simpl.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
    - simpl.
      rewrite IHa1. rewrite IHa2.
      reflexivity.
Qed.

End AExp.