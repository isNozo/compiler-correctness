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
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

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

Reserved Notation
    "st '=[' c ']=>' st'"
    (at level 40, c custom com at level 99,
     st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
    | E_Skip : forall st,
        st =[ skip ]=> st
    | E_Asign : forall st a n x,
        aeval st a = n ->
        st =[ x := a ]=> (x !-> n ; st)
    | E_Seq : forall st st' st'' c1 c2,
        st =[ c1 ]=> st' ->
        st' =[ c2 ]=> st'' ->
        st =[ c1 ; c2 ]=> st''
    | E_CIfTrue : forall st st' b c1 c2,
        beval st b = true ->
        st =[ c1 ]=> st' ->
        st =[ if b then c1 else c2 end ]=> st'
    | E_CIfFalse : forall st st' b c1 c2,
        beval st b = false ->
        st =[ c2 ]=> st' ->
        st =[ if b then c1 else c2 end ]=> st'
    | E_WhileFalse : forall st b c,
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
    - apply E_Asign. simpl. reflexivity.
    - apply E_CIfFalse.
      + simpl. reflexivity.
      + apply E_Asign. simpl. reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
    intros c st st1 st2 E1 E2.
    generalize dependent st2.
Abort.

End AExp.


(* memo *)
Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem ev_inv : forall (n:nat),
    ev n ->
    (n=0) \/ (exists m, n=S(S m) /\ ev m).
Proof.
    intros n H.
    destruct H as [| n' H'] eqn:HH.
    - left. reflexivity.
    - right. exists n'. split.
      + reflexivity.
      + apply H'.
Qed.

Theorem ev_minus2 : forall n,
    ev n -> ev (pred (pred n)).
Proof.
    intros n H.
    destruct H as [| n' H'] eqn:HH.
    - simpl. apply ev_0.
    - simpl. apply H'.
Qed.

Theorem evSS_ev : forall n,
    ev (S (S n)) -> ev n.
Proof.
    intros n H.
    apply ev_inv in H.
    destruct H.
    - discriminate H.
    - destruct H as [n' [Hnm Hev]].
      injection Hnm as Heq.
      rewrite Heq.
      apply Hev.
Qed.

Theorem evSS_ev' : forall n,
    ev (S (S n)) -> ev n.
Proof.
    intros n H.
    inversion H as [| n' H'].
    apply H'.
Qed.

(*
rewrite H0 in H.

                              H0:M1=M2, H:P[M2], H':P[M1] |- Q
                              -------------------------------- (->I)
H0:M1=M2, H:P[M2] |- M1=M2    H0:M1=M2, H:P[M2] |- P[M1] -> Q
------------------------------------------------------------- (=E)
H0:M1=M2, H:P[M2] |- P[M2] -> Q                                       H0:M1=M2, H:P[M2] |- P[M2]
------------------------------------------------------------------------------------------------ (->E)
H0:M1=M2, H:P[M2] |- Q
*)
