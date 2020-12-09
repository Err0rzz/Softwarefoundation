Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. Qed.
    
Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind. 
  - reflexivity.
  - simpl. intros. rewrite H. reflexivity.
Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind.

Inductive booltree : Type :=
 | bt_empty
 | bt_leaf (b : bool)
 | bt_branch (b : bool) (t1 t2 : booltree).
Check booltree_ind.

Inductive Toy : Type :=
  | con1 (b:bool)
  | con2 (n:nat) (t:Toy).
Check Toy_ind.

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.

Inductive mytype (X:Type): Type:=
  | constr1 (x:X)
  | constr2 (n:nat)
  | constr3 (m:mytype X) (n:nat).
Check mytype_ind.
  
Inductive foo (X Y:Type) : Type:=
  | bar (x:X)
  | baz (y:Y)
  | quux (f1:nat->foo X Y).
Check foo_ind.





