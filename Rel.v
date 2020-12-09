Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. Qed.
  
Theorem total_relation_not_a_partial_function:
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros.
  
  assert (0=1) as shit. {
  apply H with (x:=0).
  - apply tot_rel.
  - apply tot_rel. 
  }
  inversion shit.
Qed.  

Theorem empty_relation_partial_function:
  partial_function empty_relation.
Proof.
  unfold partial_function. intros. inversion H.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.
  
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo. Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.
  
Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S in Hnm. apply Hnm.
  - apply le_S in IHHm'o. apply IHHm'o.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply le_S in Hnm.
    apply le_trans with (a := (S n)) (b := (S m)) (c := (S o')).
  -- apply Hnm. -- apply Hmo.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros. inversion H.
  - apply le_n.
  - apply le_Sn_le in H1. apply H1.
Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not. intros. induction n.
  - inversion H. - apply IHn. apply le_S_n in H. apply H.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
  
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric. intros.
  assert (1<=0) as shit.
  {intros. apply H. apply n_le_Sn.
  }
  inversion shit.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.
  
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  intros a b. generalize dependent a. induction b.
  - intros. inversion H. reflexivity.
  - intros. destruct a.
  -- inversion H0.
  -- Search S. 
  apply Sn_le_Sm__n_le_m in H.
  apply IHb in H.
  + rewrite H. reflexivity.
  + apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).
  
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).
Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans. Qed.
      
    
  