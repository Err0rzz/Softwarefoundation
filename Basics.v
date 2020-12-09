
    (*nandb*)
    Definition neg (b:bool):bool := 
        match b with
        | true => false
        | false => true
        end.
    Notation "~ x" := (neg x).

    Definition orb (b1:bool) (b2:bool) : bool :=
        match b1 with
        | true => true
        | false => b2
    end.
    
    Definition andb (b1:bool) (b2:bool):bool := 
        match b1 with
        | true => b2
        | false => false
        end.
    
    Definition nandb (b1:bool) (b2:bool) :bool := 
        match b1 with
        | false => true
        | true => ~ b2
        end.

    Example testnandb1: (nandb true false)=true.
    Proof. simpl. reflexivity. Qed.
    Example testnandb2: (nandb false false)=true.
    Proof. simpl. reflexivity. Qed.
    Example testnandb3: (nandb false true)=true.
    Proof. simpl. reflexivity. Qed.
    Example testnandb4: (nandb true true)=false.
    Proof. simpl. reflexivity. Qed.

    (*andb3*)
    Definition and (b1:bool) (b2:bool):bool :=
        match b1 with 
        |false => false
        |true => b2
        end.
    Notation "a && b" := (and a b).

    Definition andb3 (b1:bool) (b2:bool) (b3:bool):bool := 
        match b1 with
        |false => false
        |true => b2 && b3
        end.
    Example test_andb31: (andb3 true true true) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_andb32: (andb3 false true true) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_andb33: (andb3 true false true) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_andb34: (andb3 true true false) = false.
    Proof. simpl. reflexivity. Qed.

    (*factorial*)
    Fixpoint evenb (n:nat) :bool:=
        match n with
        |O =>true
        |S O => false
        |S (S n) => evenb n
        end.

    Fixpoint add (n m:nat): nat :=
        match n with 
        |0=>m
        |S n=> S (add n m)
        end.
    Example testadd: add 2 3 = 5.
    Proof. simpl. reflexivity. Qed.
    
    Fixpoint mult (n m:nat) :nat :=
        match n with 
        |0 =>0
        |S n=>add m (mult n m)
        end.
    Example testmult: mult 2 3 = 6.
    Proof. simpl. reflexivity. Qed.

    Fixpoint minus (n m :nat):nat:=
        match n,m with 
        |0 ,_ =>0
        |_ ,0 =>n
        |S n ,S m =>minus n m
        end.
    Example testminus : minus 2 3 =0. 
    Proof. simpl. reflexivity. Qed.
    
    Fixpoint factorial (n:nat):nat :=
        match n with 
        |0 =>1
        |S n' => (S n')*(factorial n')
        end.
    Example test_factorial1: (factorial 3) = 6.
    Proof. simpl. reflexivity. Qed.
    Example test_factorial2: (factorial 5) = (mult 10 12).
    Proof. simpl. reflexivity. Qed.

    Notation "x + y" := (add x y)
                       (at level 50, left associativity)
                       : nat_scope.
    Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
    Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
    
    (*ltb*)
    Fixpoint eqb (n m : nat) : bool :=
        match n with
        | 0=> match m with
            | 0 => true
            | S m' => false
            end
        | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end
    end.
    Fixpoint leb (n m : nat) : bool :=
        match n with
        | 0 =>true
        | S n' =>
            match m with
            | 0 => false
            | S m' => leb n' m'
            end
        end.
    Example test_leb1: leb 2 2 = true.
    Proof. simpl. reflexivity. Qed.
    Example test_leb2: leb 2 4 = true.
    Proof. simpl. reflexivity. Qed.
    Example test_leb3: leb 4 2 = false.
    Proof. simpl. reflexivity. Qed.
    Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
    Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
    Example test_leb3': (4 <=? 2) = false.
    Proof. simpl. reflexivity. Qed.

    Definition ltb (n m:nat):bool := 
        match m with 
        |0=>false
        |S m' => (n<=?m')
        end.    
    Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
    Example test_ltb1: (ltb 2 2) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_ltb2: (ltb 2 4) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_ltb3: (ltb 4 2) = false.
    Proof. simpl. reflexivity. Qed.
    
    Theorem add_id_example: forall n m:nat,
        n=m -> n+n = m+m .
    Proof.
        intros n m.
        intros H.
        rewrite <-H.
        reflexivity.
    Qed.

    Theorem add_id_exercise: forall n m o:nat,
    n = m ->m = o ->n+m=m+o .
    Proof.
        intros n m o.
        intros H.
        intros J.
        rewrite->H.
        rewrite<-J.
        reflexivity.
    Qed.
    
    Theorem mult_n_1: forall p:nat,
    p * 1 = p .
    Proof.
        intros p.
        rewrite<-mult_n_Sm.
        rewrite<-mult_n_O.
        reflexivity.
    Qed.
    
    Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
    Proof.
        intros n. destruct n as [| n'] eqn:E.
        - reflexivity.
        - reflexivity. 
    Qed.

    Theorem andb3_exchange :
        forall b c d, andb (andb b c) d = andb (andb b d) c.
    Proof.
        intros b c d. destruct b eqn:Eb.
        - destruct c eqn:Ec.
            { destruct d eqn:Ed.
            - reflexivity.
            - reflexivity. }
            { destruct d eqn:Ed.
            - reflexivity.
            - reflexivity. }
        - destruct c eqn:Ec.
            { destruct d eqn:Ed.
            - reflexivity.
            - reflexivity. }
            { destruct d eqn:Ed.
            - reflexivity.
            - reflexivity. }
    Qed.

    Theorem andb_true_elim2:forall b c:bool,
    andb b c = true -> c = true .
    Proof.
        intros b c H.
        destruct c eqn:EC.
        - reflexivity.
        - rewrite<-H. destruct b eqn:EB.
            -- reflexivity.
            -- reflexivity.        
    Qed.
    
    Theorem zero_nbeq_plus_1: forall n:nat,
    0 =? (n+1) = false.
    Proof.
        intros n. destruct n.
        - reflexivity.
        - reflexivity.
    Qed.
    
    Theorem identity_fn_applied_twice: 
    forall (f:bool -> bool),
    (forall (x:bool),f x = x)->
    forall (b:bool),f (f b) = b.
    Proof.
        intros H J.
        destruct b eqn:EB. 
        - rewrite->J.  rewrite->J. reflexivity.
        - rewrite->J.  rewrite->J. reflexivity.
    Qed.
    
    Theorem negb_involutive:forall b:bool,
    negb (negb b) = b .
    Proof.
        intros b. destruct b eqn:E.
        - reflexivity.
        -reflexivity.
    Qed.
    

    Theorem negation_fn_applied_twice: 
    forall (f:bool->bool),
    (forall (x:bool),f x = neg x)->
    forall (b:bool), f (f b) = b.
    Proof.
        intros H J.
        destruct b eqn:EB.
        - rewrite->J.  rewrite->J. reflexivity.
        - rewrite->J.  rewrite->J. reflexivity.
    Qed.

    Theorem andb_eq_orb :
    forall (b c : bool),
    (andb b c = orb b c) -> b = c.
    Proof.
        intros b c. destruct b eqn:EB.
        - simpl. intros H. rewrite<-H. reflexivity. 
        - simpl. intros H. rewrite->H. reflexivity.
    Qed.

    Inductive bin: Type:=
    | Z
    | B0 (n:bin)
    | B1 (n:bin).

    Fixpoint incr (m:bin):bin :=
        match m with 
        | Z=>B1 Z
        | B0 n=>B1 n
        | B1 n=>B0 (incr n)
    end.

    Fixpoint bin_to_nat (m :bin) :nat :=
        match m with 
        | Z=>O
        | B0 n => (bin_to_nat n) + (bin_to_nat n)
        | B1 n => S ((bin_to_nat n) + (bin_to_nat n))
    end.
    
    Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
    Proof. simpl. reflexivity. Qed.
    Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
    Proof. simpl. reflexivity. Qed.
    Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
    Proof. simpl. reflexivity. Qed.
    Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
    Proof. simpl. reflexivity. Qed.
    Example test_bin_incr5 :
            bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
    Proof. simpl. reflexivity. Qed.
    Example test_bin_incr6 :
            bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
    Proof. simpl. reflexivity. Qed.

    

