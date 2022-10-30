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