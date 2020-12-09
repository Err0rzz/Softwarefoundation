From LF Require Export Lists.


Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint app {X:Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h1 t1 => cons h1 (app t1 l2)
  end.

Fixpoint rev {X:Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X:Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons h t => 1 + (length t)
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r: forall (X:Type),forall l:list X,
l ++ [] =l .
Proof.
    intros X l. induction l.
    - reflexivity.
    - simpl. rewrite->IHl. reflexivity.
Qed.

Theorem app_assoc: forall A (l m n:list A),
l ++ m ++ n = (l ++ m) ++ n.
Proof.
    intros. induction l.
    - reflexivity.
    - simpl. rewrite->IHl. reflexivity.
Qed.

Theorem app_length: forall (X:Type) (l1 l2 :list X),
length (l1++l2) = length l1 + length l2.
Proof.
    intros. induction l1.
    - reflexivity.
    - simpl. rewrite->IHl1. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros. induction l1.
    - simpl. rewrite->app_nil_r. reflexivity.
    - simpl. rewrite->IHl1. rewrite->app_assoc. reflexivity. 
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
    intros. induction l.
    - reflexivity.
    - simpl. rewrite->rev_app_distr. simpl. rewrite->IHl. reflexivity.
Qed.

Inductive prod (X Y:Type) :Type:=
| pair (x:X) (y:Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y):type_scope.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y)::(combine tx ty)
  end.

Definition  fst {X Y :Type} (l: (X*Y)) : X:=
    match l with
    |(x,y)=>x
    end.

Definition snd {X Y:Type} (l: X * Y) :Y := 
    match l with
    |(x, y) => y
    end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y):=
    match l with
    |[] => ([],[])
    |(x,y)::lt => (x::fst (split lt) , y::snd (split lt))
    end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.
    Inductive option (X:Type) :Type:=
        |Some (x:X)
        |None.
    Arguments Some {X} _.
    Arguments None {X}.

    Definition hd_error {X:Type} (l:list X) : option X:=
        match l with
        |nil => None
        |a::ls => Some a
        end .
    Example test_hd_error1 : hd_error [1;2] = Some 1.
    Proof. reflexivity. Qed.
    Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
    Proof. reflexivity. Qed.
End OptionPlayground.

Fixpoint filter {X:Type} (test:X->bool) (l:list X) : list X :=
    match l with
    |[] => []
    |h::t => if (test h) then h::(filter test t)
                        else (filter test t)
    end.

Definition filter_even_gt7 (l:list nat) :list nat:= 
    match l with
    |[] => []
    |h::t => filter (fun a => (evenb a) && (7<?a)) l
    end.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Fixpoint oddb (a:nat) : bool :=
    match a with
    |O => false
    |S 0 => true
    |S n => ~oddb n 
    end.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X:=
    match l with 
    |[] => pair [] []
    |h::t => pair (filter (fun a => test a) l ) (filter (fun a=>~test a) l)
    end.
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f: X->Y) (l:list X) : (list Y):=
    match l with
    |[] => []
    |h::t => (f h)::(map f t)
    end.

Theorem map_app_distr: forall (X Y:Type) (f:X->Y) (l1 l2:list X),
map f (l1++l2) = (map f l1) ++ (map f l2).
Proof.
    intros. induction l1.
    - reflexivity.
    - simpl. rewrite->IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
    intros. induction l.
    - reflexivity.
    - simpl. rewrite->map_app_distr. rewrite->IHl. reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y):=
    match l with
    |[]=>[]
    |h::t=>(f h) ++ (flat_map f t)
    end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Fixpoint fold {X Y:Type} (f:X->Y->Y) (l:list X) (b:Y): Y:=
    match l with
    |[] => b
    |h::t => f h (fold f t b)
    end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
    intros. induction l.
    - reflexivity.
    - simpl. rewrite<-IHl. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y:=
    fold (fun h t =>(f h)::t) l [].

Theorem fold_map_correct:forall X Y (f:X->Y) (l:list X),
fold_map f l = map f l.
Proof.
    intros. induction l.
    - reflexivity.
    - simpl. rewrite<-IHl. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z:=
  f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p.
  - reflexivity. Qed.

Inductive option (X:Type) :Type:=
    |Some (x:X)
    |None.
Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).
Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X. 
Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.
Definition three : cnat := @doit3times.
Definition succ (n : cnat) : cnat:=
  fun (X:Type) (f:X->X) (x:X) => f (n X f x).
Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x: X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.
Definition mult (n m : cnat) : cnat :=
fun (X : Type) (f : X -> X) => n X (m X f).
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed. 
End Church.