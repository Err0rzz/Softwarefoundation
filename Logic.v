Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.
From Coq Require Import Setoids.Setoid.
Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros. split.
    - destruct n .
    -- reflexivity.
    -- discriminate.
    - destruct m .
    -- reflexivity.
    -- rewrite<-plus_n_Sm in H. discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
    intros P Q [_ HQ].
    apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not : forall (P:Prop),
    ~P -> (forall (Q:Prop), P -> Q).
Proof.
    intros. destruct H. apply H0. Qed.
    
Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.
Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem contrapositive : forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
    intros P Q H. unfold not. intros. apply H in H1. apply H0 in H1.
    apply H1. Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
    intros P. unfold not. intros [HP HNA]. apply HNA in HP.
    apply HP. Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R. split.
    - intros [HP | [HQ HR]].
    -- split. left. apply HP. left. apply HP.
    -- split. right. apply HQ. right. apply HR.
    - intros. destruct H as [HPQ HPR]. destruct HPQ.
    -- left. apply H. 
    -- destruct HPR.
    + left. apply H0.
    + right. split. apply H. apply H0.
Qed.

Lemma mult_eq_0: forall n m, n*m =0 -> n = 0 \/ m = 0 .
Proof.
    intros n m H. destruct n.
    - left. reflexivity.
    - destruct m.
    -- right. reflexivity.
    -- discriminate.
Qed.

Lemma eq_mult_0: forall n m, n=0 \/ m =0-> n*m=0 .
Proof.
    intros n m [Hn|Hm].
    - rewrite->Hn. reflexivity.
    - rewrite->Hm. apply mult_comm.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply eq_mult_0.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, not (P x)).
Proof.
  intros. unfold not. intros. destruct H0. apply H0 in H. apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros. split.
    - intros [x [HP|HQ]]. 
    -- left. exists x. apply HP.
    -- right. exists x. apply HQ.
    - intros [HP | HQ].
    -- destruct HP as [x HP]. exists x. left. apply HP.
    -- destruct HQ as [x HQ]. exists x. right. apply HQ.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.
Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|h t IH].
  -- intros. simpl in H. destruct H.
  -- intros. simpl. destruct H eqn:H1.
    + exists h. split. apply e. left. reflexivity.
    + clear H1. apply IH in i. destruct i. exists x. destruct H0. 
      split. apply H0. right. apply H1. 
  - induction l as [|h t IH].
  -- intros. simpl in H. destruct H. destruct H. destruct H0.
  -- intros. simpl. destruct H. simpl in H. destruct H.  
     destruct H0. 
      * left. rewrite->H0. apply H.
      * right. apply IH. exists x. split. apply H. apply H0.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - split.
  -- simpl. intros. right. apply H.
  -- simpl. intros. destruct H. destruct H. apply H.
  - split.
  -- simpl. intros. destruct H.
  + left. left. apply H.
  + apply IH in H. destruct H.
  * left. right. apply H.
  * right. apply H.
  -- simpl. intros. destruct H as [[H1|H2]|H3].
  + left. apply H1. 
  + right. apply IH. left. apply H2.
  + right. apply IH. right. apply H3.  
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop:=
  match l with
  |[] => True
  |h::t => P h /\ (All P t)
end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split. 
  - intros. induction l as [|h t IH].
  -- simpl. reflexivity.
  -- simpl. split.
  + apply H. simpl. left. reflexivity.
  + apply IH. intros. simpl in H. apply H. right. apply H0.
  - induction l as [|h t IH]. 
  + intros. simpl in H0. destruct H0.
  + simpl. intros. destruct H. destruct H0.
  * rewrite<-H0. apply H.
  * apply IH. apply H1. apply H0.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop:=
  fun (n:nat) => if (oddb n) then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros. unfold combine_odd_even. destruct (oddb n) eqn:IH.
  - simpl in H. apply H. reflexivity.
  - apply H0. reflexivity.
Qed.
 
Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H. destruct (oddb n).
  - apply H. 
  - discriminate.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros. unfold combine_odd_even in H. destruct (oddb n).
  - discriminate.
  - apply H.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_append_empty: forall X (l1 l2:list X), rev_append l1 l2 = rev_append l1 []++ l2.
Proof.
  intros X l1. induction l1.
  - intros l2. reflexivity.
  - intros l2. simpl. destruct l2 as [|h t].
  -- rewrite app_nil_r. reflexivity.
  -- rewrite IHl1. replace (rev_append l1 [x]) with (rev_append l1 [] ++ [x]).
  + rewrite<- app_assoc. reflexivity.
  + rewrite<-IHl1. reflexivity.
Qed. 
  
Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros. apply functional_extensionality. 
  unfold tr_rev. induction x as [|h t HX].
  - reflexivity.
  - simpl. rewrite<-HX. apply rev_append_empty.
Qed.

Definition even x := exists n : nat, x = double n.
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof. 
  intros. induction n.
  - reflexivity.
  - rewrite IHn. simpl. rewrite negb_involutive. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as H1. apply H1. Qed.

Lemma evenb_double_conv : forall n, exists k,
  n = if evenb n then double k else S (double k).
Proof.
  intros. induction n as [|n' IH].
  - simpl. exists 0. reflexivity.
  - rewrite evenb_S. destruct (evenb n').
  -- simpl. destruct IH. exists x. rewrite H. reflexivity.
  -- simpl. destruct IH. exists (S x). rewrite H. simpl. reflexivity.
Qed.

Lemma evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> even n.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros. split.
  - intros. destruct b1.
  + simpl in H. rewrite H. split. reflexivity. reflexivity.
  + simpl in H. discriminate.
  - intros. destruct b1.
  + destruct H. rewrite H0. reflexivity.
  + destruct H. simpl. apply H.
Qed.

Theorem orb_true_iff : forall b1 b2,
  orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros. split.
  - intros. destruct b1.
  -- left. reflexivity.
  -- simpl in H. right. apply H.
  - intros. destruct H.
  -- rewrite H. simpl. reflexivity.
  -- destruct b1.
  + reflexivity.
  + simpl. apply H. 
Qed.
Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros. split.
  - rewrite<- not_true_iff_false. intros. intros H'.
  destruct H. rewrite H'. symmetry. apply eqb_refl.
  - rewrite<- not_true_iff_false. intros. intros H'.
  destruct H. apply eqb_true in H'. apply H'.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool:=
  match l1,l2 with
  |nil,nil => true
  |h::t,nil=>false
  |nil,h::t=>false
  |h1::t1,h2::t2=>(eqb h1 h2) && (eqb_list eqb t1 t2)
end.

Lemma andb_true_elim1: forall a b , (a && b) =true->a = true.
Proof.
  intros. destruct a.
  - reflexivity.
  - simpl in H. apply H.
Qed.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros. split.
  - generalize dependent l2. induction l1 as [|h t IH].
  -- simpl. destruct l2. 
  + reflexivity. 
  + intros. discriminate.
  -- simpl. destruct l2 as [|h' t'].
  + intros. discriminate.
  + intros. apply andb_true_iff in H0. destruct H0. 
    apply H in H0. rewrite H0. apply IH in H1. rewrite H1.
    reflexivity.
  - generalize dependent l2. induction l1 as [|h t IH].
  -- simpl. intros. destruct l2.
  + reflexivity.
  + discriminate.
  -- simpl. intros. destruct l2.
  + discriminate.
  + injection H0 as H0. apply H in H0. apply IH in H1.
    rewrite H0. rewrite H1. reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros. split.
  - intros. induction l as [|h t IH].
  -- reflexivity.
  -- simpl. simpl in H. apply andb_true_iff in H.
    destruct H as [H1 H2]. split. 
  + apply H1. 
  + apply IH in H2. apply H2.
  - intros. induction l as [|h t IH].
  -- reflexivity.
  -- simpl. simpl in H. destruct H as [H1 H2].
  rewrite H1. apply IH in H2. rewrite H2. reflexivity.
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.
Theorem restricted_excluded_middle : forall P (b : bool),
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.
  apply H. right. intros. apply H. left. apply H0.
Qed.




