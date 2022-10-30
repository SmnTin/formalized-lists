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

Section In.
  Variable A : Type.

  Fixpoint In (a : A) (xs : list A) : Prop :=
    match xs with
    | [] => False
    | x :: xs => x = a \/ In a xs
    end.

  Theorem nth_In n d xs :
    n < length xs -> In (nth n xs d) xs.
  Proof.
    generalize dependent n.
    induction xs as [| x xs IH].
    - intros n H. inversion H.
    - intros [| n] H; simpl.
      + left. reflexivity.
      + right. apply IH. apply le_S_n. apply H.
  Qed.

  Theorem In_nth a xs d :
    In a xs -> exists n, n < length xs /\ nth n xs d = a.
  Proof.
    induction xs as [| x xs IH]; simpl.
    - intros [].
    - intros [H | H].
      + exists 0. split.
        * apply le_n_S. apply le_0_n.
        * simpl. apply H.
      + apply IH in H as [n [H_len H_nth]].
        exists (S n). split.
        * apply le_n_S. apply H_len.
        * simpl. apply H_nth.
  Qed.
End In.

Arguments In {A}.

Section filter.
  Variable A : Type.
  Variable f : A -> bool.

  Fixpoint filter (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => if f x then x :: filter xs else filter xs
    end.

  Theorem filter_In xs :
    forall a, In a (filter xs) -> f a = true.
  Proof.
    intros a. induction xs as [| x xs IH]; simpl.
    - intros [].
    - destruct (f x) eqn:Hfx; simpl.
      + intros [H | H].
        * rewrite <- H. apply Hfx.
        * apply IH. apply H.
      + apply IH.
  Qed.
End filter.