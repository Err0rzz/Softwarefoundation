From LF Require Export Basics.


    Theorem plus_n_O : forall n:nat, n = n + 0.
    Proof.
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *) reflexivity.
    - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.
    
    Theorem minus_n_n : forall n,
    minus n n = 0.
    Proof.
    (* WORKED IN CLASS *)
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity. Qed.  
    
    Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
    Proof.
        intros n. induction n.
        - reflexivity.
        - simpl. rewrite->IHn. reflexivity.
    Qed.

    Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
    Proof.
        intros n m. induction n.
        - simpl. reflexivity.
        - simpl. rewrite->IHn. reflexivity.  
    Qed.

    Theorem plus_comm : forall n m : nat,
    n + m = m + n.
    Proof.
        intros n m. induction n.
        - simpl. rewrite<-plus_n_O. reflexivity.
        - simpl. rewrite->IHn. rewrite->plus_n_Sm. reflexivity.
    Qed.

    Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
    Proof.
        intros n m p. induction n.
        - simpl. reflexivity.
        - simpl. rewrite->IHn. reflexivity.  
    Qed.
    
    Fixpoint double (n:nat) :=
        match n with
        | O => O
        | S n' => S (S (double n'))
        end.

    Lemma double_plus: forall n, double n = n+n .
    Proof.
        intros n . induction n.
        - reflexivity.
        - simpl. rewrite->IHn.  rewrite->plus_n_Sm. reflexivity. 
    Qed.

    Theorem evenb_S : forall n:nat,
    evenb (S n) = negb (evenb n).
    Proof.
        intros n. induction n.
        - simpl. reflexivity.
        - rewrite->IHn. rewrite->negb_involutive. simpl. reflexivity.
    Qed.
    
    Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
    Proof.
        intros n m.
        assert (H: 0 + n = n). { reflexivity. }
        rewrite -> H.
    reflexivity. Qed.
        
    Theorem plus_swap: forall n m p: nat,
    n+ (m+p) = m + (n+p).
    Proof.
        intros n m p.
        rewrite->plus_assoc.
        assert (H: n+m=m+n). { rewrite->plus_comm. reflexivity. }
        rewrite->H.
        rewrite<-plus_assoc. 
        reflexivity.
    Qed.
    
    Theorem mult_plus_distr_1: forall n m:nat,
    n* S m = n + n * m.
    Proof.
        intros n m. induction n.
        - simpl. reflexivity.
        - simpl. rewrite->IHn. rewrite->plus_swap. reflexivity.
    Qed.
    
    Theorem mult_comm: forall m n:nat,
    m*n = n*m .
    Proof.
        intros m n. induction m.
        - simpl. rewrite->mult_0_r. reflexivity.
        - simpl. rewrite->IHm. rewrite->mult_plus_distr_1. reflexivity. 
    Qed.
    

    Theorem leb_refl : forall n:nat,
    true = (n <=? n).
    Proof.
        intros n. induction n.
        - reflexivity.
        - simpl. rewrite<-IHn. reflexivity.
    Qed.

    Theorem zero_nbeq_S : forall n:nat,
    0 =? (S n) = false.
    Proof.
        intros n. reflexivity.
    Qed.
    
    Theorem andb_false_r : forall b : bool,
    andb b false = false.
    Proof.
        intros b. destruct b.
        - reflexivity.
        - reflexivity.
    Qed.

    Theorem plus_ble_compat_l : forall n m p : nat,
    n <=? m = true -> (p + n) <=? (p + m) = true.
    Proof.
        intros n m p. intros H. induction p.
        - simpl. rewrite->H. reflexivity.
        - simpl. rewrite->IHp. reflexivity.
    Qed.

    Theorem S_nbeq_0 : forall n:nat,
    (S n) =? 0 = false.
    Proof.
        reflexivity.
    Qed.

    Theorem mult_1_l : forall n:nat, 1 * n = n.
    Proof.
        intros n. simpl. rewrite->plus_n_O. reflexivity.
    Qed.

    Theorem all3_spec : forall b c : bool,
        orb
        (andb b c)
        (orb (negb b)
                (negb c))
    = true.
    Proof.
        intros b c. destruct b. destruct c.
        - reflexivity.
        - reflexivity.
        - reflexivity.
    Qed.
     
    Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
    Proof.
        intros n m p.  
        induction p.
        {rewrite->mult_0_r. rewrite->mult_0_r. rewrite->mult_0_r. reflexivity. }
        {
            rewrite->mult_plus_distr_1. rewrite->mult_plus_distr_1. rewrite->mult_plus_distr_1.
            rewrite->plus_swap. rewrite->IHp.
            rewrite<-plus_assoc. rewrite<-plus_assoc. rewrite->plus_swap.
            reflexivity.
        }
    Qed.

    Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
    Proof.
        intros n m p.
        induction n.
        - reflexivity.
        - simpl. rewrite->IHn. rewrite<-mult_plus_distr_r. reflexivity.
    Qed. 

    Theorem eqb_refl: forall n:nat,
    true = (n =? n).
    Proof.
        intros n. induction n.
        - reflexivity.
        - simpl. rewrite->IHn. reflexivity. 
    Qed.

    Theorem plus_swap': forall n m p:nat,
    n + (m+p) = m+ (n+p) .
    Proof.
        intros n m p. 
        rewrite->plus_assoc.
        replace (n+m) with (m+n). 
        - rewrite<-plus_assoc. reflexivity.
        - rewrite->plus_comm. reflexivity. 
    Qed.
    
    Theorem bin_to_nat_pres_incr: forall n:bin,
    bin_to_nat (incr n) = S (bin_to_nat n).
    Proof.
        intros n. induction n.
        - reflexivity.
        - reflexivity.
        - {simpl. 
        rewrite->IHn. 
        rewrite->plus_n_Sm.
        replace (bin_to_nat n + S (bin_to_nat n)) with (S (bin_to_nat n) + (bin_to_nat n)).
        - rewrite->plus_n_Sm. reflexivity.
        - rewrite->plus_comm. reflexivity. 
        }
    Qed.
    
    Fixpoint nat_to_bin (n:nat):bin:=
        match n with 
        |O => Z
        |S n => incr (nat_to_bin n)
    end.

    Lemma nat_to_bin_pres_incr: forall n:nat,
    incr (nat_to_bin n) = nat_to_bin (S n).
    Proof.
        intros n. induction n.
        - reflexivity.
        - reflexivity.
    Qed.

    Theorem nat_bin_nat: forall n,
    bin_to_nat (nat_to_bin n) =n .
    Proof.
        intros n. induction n.
        - reflexivity.
        - simpl. rewrite->bin_to_nat_pres_incr. rewrite->IHn. reflexivity.
    Qed.
    
    
