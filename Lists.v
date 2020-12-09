From LF Require Export Induction.

Inductive natprod:Type :=
|pair (n1 n2:nat) .

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem  snd_fst_is_swap: forall (p:natprod),
(snd p,fst p) = swap_pair p .
Proof.
    intros p.  destruct p.
    reflexivity.
Qed.

Theorem fst_swap_is_snd: forall p:natprod,
fst (swap_pair p) = snd p .
Proof.
    intros p. destruct p.
    reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist:=
    match l with
    | nil =>nil
    | h::t => (if h=?0 then (nonzeros t) else h::(nonzeros t))
    end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. simpl. reflexivity. Qed.
Fixpoint oddmembers (l:natlist) : natlist:=
    match l with
    | nil => nil
    | h::t => (if evenb h then oddmembers t else h::(oddmembers t))
    end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. simpl. reflexivity. Qed.
Definition countoddmembers (l:natlist) : nat:=
    match l with
    |nil =>O
    |h::t => length (oddmembers (h::t))
    end.
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist:=
    match l1 with
    | nil => l2
    | h::t=> match l2 with
            | nil =>h::t
            | h2::t2 =>h::h2::(alternate t t2)
            end
    end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof. simpl. reflexivity. Qed.

Definition bag := natlist.
Fixpoint count (v:nat) (s:bag):nat:=
    match s with
    |nil =>O
    |h::t =>(if v =?h then S (count v t) else (count v t))
    end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 Proof. reflexivity. Qed.

Definition sum :bag->bag->bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
    Proof. reflexivity. Qed.
Definition add (v : nat) (s : bag) : bag:=
    match s with 
    |nil => [v]
    |h::t => v::h::t
    end.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
    Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
    Proof. reflexivity. Qed.
Definition member (v : nat) (s : bag) : bool:=
    match s with
    | nil =>false
    | h::t => negb ((count v s)=?0)
    end.
Example test_member1: member 1 [1;4;1] = true.
    Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
    Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag:=
  match s with
  | nil => nil
  |h::t => (if h=?v then t else h::(remove_one v t))
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.
Fixpoint remove_all (v:nat) (s:bag) : bag:=
  match s with
  | nil => nil
  | h::t => (if (h=?v) then (remove_all v t) else (h::(remove_all v t)))
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.
Fixpoint subset (s1 : bag) (s2 : bag) : bool:=
    match s1 with
    |nil => true
    |h::t => match s2 with
            | nil => false
            | h2::t2 =>(member h (h2::t2)) && (subset t (remove_one h (h2::t2)))
            end
    end.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
    Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
    Proof. reflexivity. Qed.

Theorem add_inc_count: forall (a:nat) (s:bag),
count a (add a s) = S (count a s) .
Proof.
    intros a s. destruct s.
    - simpl. rewrite<-eqb_refl. reflexivity.
    - simpl. rewrite<-eqb_refl. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l.
  - reflexivity. 
  - simpl. rewrite->IHl. reflexivity.
Qed.

Theorem rev_assoc: forall (a:natlist) (b:natlist) (c:natlist),
(a ++ b) ++ c = a ++ b ++ c .
Proof.
  intros a b c. induction a.
  - reflexivity.
  - simpl. rewrite->IHa. reflexivity. 
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1.
  - simpl. rewrite->app_nil_r. reflexivity.
  - simpl. rewrite->IHl1. rewrite->rev_assoc. reflexivity. 
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite->rev_app_distr. rewrite->IHl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite->rev_assoc. rewrite->rev_assoc. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1.
  - reflexivity.
  - simpl. destruct n.
  -- simpl. rewrite->IHl1. reflexivity.
  -- simpl. rewrite->IHl1. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool:=
  match l1,l2 with
  |nil,nil => true
  |nil,(h::t) => false
  |(h::t),nil => false
  |(h1::t1),(h2::t2) => (if h1=?h2 then eqblist t1 t2 else false)
end.
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. induction n.
  -- simpl. rewrite->IHl. reflexivity.
  -- simpl. rewrite->IHn. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s.
  - reflexivity.
  - simpl. destruct n.
  -- simpl. rewrite->leb_n_Sn. reflexivity.
  -- simpl. rewrite->IHs. reflexivity.
Qed.

Theorem bag_count_sum: forall (l1 l2:bag) (a:nat),
count a (sum l1 l2) = count a l1 + count a l2.
Proof.
  intros l1 l2 a. induction l1 as [|h1 l1' H1].
  - reflexivity.
  - simpl. destruct (eqb a h1).
  -- simpl. rewrite<-H1. reflexivity.
  -- rewrite<-H1. reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
    intros l1 l2 IH.
    rewrite<-rev_involutive,<-IH,->rev_involutive. reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition hd_error (l : natlist) : natoption:=
  match l with
    |nil => None
    |h::t => Some (h)
    end.
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.
