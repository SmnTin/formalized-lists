Inductive list (A : Type) : Type :=
| nil
| cons (x : A) (xs : list A).

Arguments nil {A}.
Arguments cons {A} x xs.

Notation "[ ]" := nil (format "[ ]").
Infix "::" := cons (at level 60, right associativity).

Section app.
  Variable A : Type.

  Fixpoint app (xs ys : list A) : list A :=
    match xs with
    | [] => ys
    | x :: xs => x :: app xs ys
    end.

  Infix "++" := app (at level 60, right associativity).

  Theorem app_assoc (xs ys zs : list A) :
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
  Proof.
    induction xs as [| x xs IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Theorem app_nil_l (xs : list A) : [] ++ xs = xs.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem app_nil_r (xs : list A): xs ++ [] = xs.
  Proof.
    induction xs as [| x xs IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.
End app.

Arguments app {A} xs ys.

Fixpoint length {A : Type} (xs : list A) : nat :=
  match xs with
  | [] => 0
  | _ :: xs => S (length xs)
  end.

Section nth.
  Variable A : Type.

  Fixpoint nth (n : nat) (xs : list A) (default : A) : A :=
    match n, xs with
    | 0, x :: _ => x
    | _, [] => default
    | S n, _ :: xs => nth n xs default
    end.

  Fixpoint nth_ok (n : nat) (xs : list A) : bool :=
    match n, xs with
    | 0, _ :: _ => true
    | _, [] => false
    | S n, _ :: xs => nth_ok n xs
    end.

  Lemma nth_ok_ok n xs :
    n < length xs -> nth_ok n xs = true.
  Proof.
    generalize dependent n.
    induction xs as [| x xs IH].
    - intros n H. inversion H.
    - intros [| n] H.
      + simpl. reflexivity.
      + simpl in *. apply IH. apply le_S_n. apply H.
  Qed.
End nth.

Arguments nth {A}.
Arguments nth_ok {A}.