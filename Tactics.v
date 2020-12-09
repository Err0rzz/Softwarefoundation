From LF Require Export Poly.
Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 2 = true ->
     oddb 3 = true.
Proof.
    intros. apply H. apply H0. Qed.
Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H. symmetry. apply H. Qed.
  
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
    intros. rewrite->H. symmetry. apply rev_involutive. Qed.

Definition minustwo (n:nat):nat := n-2.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
    intros. apply trans_eq with m. apply H0. apply H. Qed.
    
Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H. injection H as Hnm. apply Hnm. Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H.
  (* WORKED IN CLASS *)
  intros H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem trans_eq_list : forall (X:Type) (n m o :list X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
    intros. injection H as H1 H2. rewrite H1.
    assert (y::l = z::l) as H. { rewrite H2. rewrite<-H0. reflexivity. }
    injection H as H3. symmetry. apply H3.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
    intros. discriminate H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
    intros n. induction n.
    - intros m eq. destruct m.
    -- reflexivity.
    -- discriminate eq.
    - intros m eq. destruct m.
    -- discriminate eq.
    -- f_equal. apply IHn. simpl in eq. apply eq.
Qed.     

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
    intros n. induction n as [|n' IHn].
    - simpl. intros m eq. destruct m as [|m'].
    -- reflexivity.
    -- discriminate.
    - intros m eq. destruct m as [|m'].
    -- discriminate.
    -- f_equal. simpl in eq. rewrite<-plus_n_Sm in eq.
    rewrite<-plus_n_Sm in eq. injection eq as goal. apply IHn in goal.
    apply goal.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
    intros. generalize dependent n. induction l.
    - intros n. destruct n.
    -- reflexivity.
    -- discriminate.
    - intros. destruct n.
    -- discriminate.
    -- simpl in H. injection H as goal. apply IHl in goal. simpl. apply goal.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem tail_eq : forall (X:Type) (h:X) (t1 t2:list X),
  t1 = t2 -> (h::t1) = (h::t2).
Proof.
  intros. f_equal. apply H.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
    intros X Y l. induction l as [|h t IH].
  - intros. unfold split in H. injection H as H1 H2.
    rewrite<-H1. rewrite<-H2. reflexivity.
  - intros. simpl in H. 
    destruct h. destruct (split t).
    injection H as H1 H2. rewrite<-H1. rewrite<-H2. simpl.
    apply tail_eq. apply IH. reflexivity.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct b eqn:B.
  - destruct (f true) eqn:Ft.
  -- rewrite->Ft. apply Ft.
  -- destruct (f false) eqn:Fl.
  + apply Ft.
  + apply Fl.
  - destruct (f false) eqn:Fl.
  -- destruct (f true) eqn:Ft.
  + apply Ft.
  + apply Fl.
  -- rewrite->Fl. apply Fl.
  Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n. induction n.
  - intros. destruct m. 
  -- reflexivity.
  -- apply zero_nbeq_S. 
  - intros. destruct m.
  -- apply S_nbeq_0. 
  -- simpl. apply IHn.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros. apply eqb_true in H. apply eqb_true in H0. 
  rewrite-> H. rewrite<-H0. rewrite<-eqb_refl. reflexivity.
Qed.

Definition split_combine_statement : Prop:=
  forall (X:Type) (l1 l2: list X),
  length l1 = length l2->
  split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X l1. induction l1 as [|h1 t1 Hl1].
  - intros l2 H. destruct l2.
  -- reflexivity.
  -- simpl. discriminate.
  - intros. destruct l2 as [|h2 t2].
  -- simpl. discriminate.
  -- simpl in H. injection H as H1. apply Hl1 in H1.
  simpl. rewrite-> H1. reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l. induction l as [|h t Hl].
  - intros. discriminate.
  - intros. simpl in H. destruct (test h) eqn:Test .
  -- injection H as H1 H2. rewrite <-H1. apply Test.
  --  apply Hl in H. apply H.
Qed.

Fixpoint forallb {X:Type} (test:X->bool) (l:list X) : bool:=
   match l with
   |[]=>true
   |h::t => (test h) && (forallb test t)
   end.
Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X:Type} (test:X->bool) (l:list X): bool :=
  match l with
  |[] => false
  |h::t => orb (test h) (existsb test t)
  end.
Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X:Type} (test:X->bool) (l:list X):bool:=
  negb (forallb (fun n=> negb (test n) ) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. 
  intros. induction l as [|h t H].
  - reflexivity.
  - simpl. rewrite->H. unfold existsb'. destruct (test h) eqn: Test.
  -- simpl. rewrite->Test. reflexivity.
  -- simpl. rewrite->Test. reflexivity.
Qed.


















 
