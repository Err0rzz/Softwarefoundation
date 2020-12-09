Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From LF Require Import Maps.

Module AExp.
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1)*(aeval a2)
  end.
Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.
  
Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp:=
  match b with
  | BTrue =>  BTrue
  | BFalse => BFalse
  | BEq a1 a2  => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b => BNot (optimize_0plus_b b)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
end.
Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b. induction b;
  try (simpl;rewrite optimize_0plus_sound''; rewrite optimize_0plus_sound'');
  try reflexivity.
  - try (simpl; rewrite IHb; reflexivity).
  - try (simpl; rewrite IHb1; rewrite IHb2; reflexivity).
Qed.
  Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.
  
Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.
   
Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR : bexp -> bool -> Prop :=
	| E_BTrue : bevalR (BTrue) true
	| E_BFalse : bevalR (BFalse) false
	| E_BEq : forall (e1 e2: aexp) (n1 n2 : nat),
						aevalR e1 n1 -> aevalR e2 n2 -> bevalR (BEq e1 e2) (n1=?n2)
	| E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
						aevalR e1 n1 -> aevalR e2 n2 -> bevalR (BLe e1 e2) (n1<=?n2)
	| E_BNot : forall (e1 : bexp) (b : bool),
							bevalR e1 b -> bevalR (BNot e1) (negb b)
	| E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
							bevalR e1 b1 -> bevalR e2 b2 -> bevalR (BAnd e1 e2) (andb b1 b2)
  where "e '==>b' b" := (bevalR e b) : type_scope.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  split.
  - intros H;induction H; simpl;
    try (apply aeval_iff_aevalR' in H;apply aeval_iff_aevalR' in H0);
    try subst;reflexivity.
  - intros. generalize dependent bv. 
    induction b; simpl; intros; subst; constructor;
    try (apply aeval_iff_aevalR');
    try apply IHb;
    try (apply IHb1);
    try (apply IHb2);
    reflexivity.
Qed.
End AExp.
  
Definition state := total_map nat.
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.
  
Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).
Example aexp1 :
    aeval (X !-> 5) <{ (3 + (X * 2))}>
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4)}>
  = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
  
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.
Print fact_in_coq.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !->0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (Y !->1;X!->0);
    apply E_Ass; reflexivity.
Qed.

Definition pup_to_n : com:=
  <{Y := (ANum 0);
    while ((ANum 1) <= (AId X)) do
      Y := ((AId Y) + (AId X));
      X := (AId X) - (ANum 1)
    end}>.
    
Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  apply E_Seq with (Y!->0;X!->2).
  - apply E_Ass. reflexivity. 
  - apply E_WhileTrue with (X !-> 1 ;Y !-> 2; Y !-> 0; X !-> 2).
  -- reflexivity.
  -- apply E_Seq with (Y!->2;Y!->0;X!->2).
  + apply E_Ass. reflexivity.
  + apply E_Ass. reflexivity.
  -- apply E_WhileTrue with (X !-> 0;
     Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
  + reflexivity.
  + apply E_Seq with (Y !-> 3;X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
  * apply E_Ass. reflexivity. 
  * apply E_Ass. reflexivity.
  + apply E_WhileFalse. reflexivity.
Qed.

Definition plus2 : com :=
  <{ X := X + 2 }>.
Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.
Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.

Definition loop : com :=
  <{ while true do
       skip
     end }>.

Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.
  induction contra;
  try discriminate.
  - inversion Heqloopdef. subst. discriminate.
  - apply IHcontra2. apply Heqloopdef.
Qed. 
  
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }> =>
      false
  end.
  
Inductive no_whilesR: com -> Prop :=
  | NSkip: no_whilesR CSkip
  | NAss (x:string) (a:aexp): no_whilesR (CAss x a)
  | NSeq (c1 c2:com) : no_whilesR c1->no_whilesR c2-> no_whilesR (CSeq c1 c2)
  | NIf (b:bexp) (c1 c2:com): 
  no_whilesR c1->no_whilesR c2-> no_whilesR (CIf b c1 c2)
.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  induction c. 
  - intros. constructor. 
  - intros. constructor.
  - intros. constructor. simpl in H.  apply andb_prop in H.
    destruct H. apply IHc1. apply H. simpl in H.  apply andb_prop in H.
    destruct H. apply IHc2. apply H0.
  - intros. constructor.
  -- apply IHc1. simpl in H. apply andb_prop in H. destruct H.
    apply H.
  -- apply IHc2. simpl in H. apply andb_prop in H. destruct H.
    apply H0.
  - simpl. intros. inversion H.
  - intros. induction H;simpl;try reflexivity.
  -- rewrite IHno_whilesR1. rewrite IHno_whilesR2. simpl. reflexivity.
  -- rewrite IHno_whilesR1. rewrite IHno_whilesR2. simpl. reflexivity.
Qed.
   
Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat:=
  match prog with
  | [] => stack
  | h::t=> match h with
           | SPush n => s_execute st (n::stack) t
           | SLoad x => s_execute st ((st x)::stack) t
           | SPlus => match stack with
                     | [] => s_execute st stack t
                     | [x] => s_execute st stack t
                     | x1::x2::xs => s_execute st ((x1+x2)::xs) t
                     end
           | SMinus => match stack with
                     | [] => s_execute st stack t
                     | [x] => s_execute st stack t
                     | x1::x2::xs => s_execute st ((x2-x1)::xs) t
                     end
           | SMult => match stack with
                     | [] => s_execute st stack t
                     | [x] => s_execute st stack t
                     | x1::x2::xs => s_execute st ((x1*x2)::xs) t
end end end.
Check s_execute.
Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. simpl. reflexivity. Qed.
Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. simpl. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr:=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x] 
  | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SPlus]
  | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMinus]
  | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMult]
end.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. simpl. reflexivity. Qed.

Theorem execute_app : forall st p1 p2 stack,
    s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  induction p1.
  - simpl. reflexivity.
  - destruct a;intros;simpl;destruct stack as  [ | x' [ | y stack']];
    try rewrite IHp1; try reflexivity.
Qed.

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  induction e;simpl;try reflexivity;
  intros; rewrite execute_app; rewrite execute_app; rewrite IHe1; 
  rewrite IHe2; simpl; try rewrite plus_comm; try rewrite mult_comm; reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  induction e;simpl;try reflexivity;
  intros; rewrite execute_app; rewrite execute_app; 
  rewrite IHe1;rewrite s_compile_correct_aux; simpl; try rewrite plus_comm; try rewrite mult_comm; reflexivity.
Qed.

Definition BAnd' (b1 b2:bool):bool:=
  match b1 with
  | false=> false
  | true => match b2 with
            | false => false
            | true => true
            end
  end.

Fixpoint beval' (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval' st b1)
  | <{b1 && b2}> => BAnd' (beval' st b1) (beval' st b2)
  end.

Theorem beval_beval':forall st b, beval st b = beval' st b.
Proof.
  induction b; simpl;try rewrite IHb; 
  try reflexivity.
  rewrite IHb1. rewrite IHb2. destruct (beval' st b1) eqn:IH.
  - simpl. destruct (beval' st b2) eqn:IH'.
  -- reflexivity. -- reflexivity.
  - simpl. reflexivity.
Qed.
Module BreakImp.
Inductive com : Type :=
  | CSkip
  | CBreak (* <--- NEW *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
  
Inductive result : Type :=
  | SContinue
  | SBreak.
Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).
     
Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st,
      st =[ CBreak ]=>st / SBreak
  | E_Ass : forall st a x n,
      aeval st a = n->
      st =[ x:=a ]=> (x!->n;st) / SContinue
  | E_If : forall st st' b c1 c2 s,
      beval st b = true ->
      st =[ c1 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s
 | E_SeqContinue : forall st st' st'' c1 c2,
      st =[ c1 ]=> st' / SContinue ->
      st'=[ c2 ]=> st'' / SContinue ->
      st =[ c1;c2 ]=> st'' / SContinue
  | E_SeqBreak : forall st st' c1 c2,
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1;c2 ]=>st' / SBreak
  | E_WhileEnd : forall st b c,
      beval st b = false ->
      st =[ while b do c end ]=> st / SContinue
  | E_WhileContinue :forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / SContinue->
      st =[ while b do c end ]=> st'' / SContinue
  | E_WhileBreak : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ while b do c end ]=> st' / SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').
  
Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  intros. inversion H. subst. inversion H2. inversion H5.
  reflexivity.
Qed.

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  intros. inversion H;reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros. apply E_WhileBreak;assumption.
Qed.

Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros. remember (<{while b do c end}>) as c'.
  induction H;inversion Heqc'.
  - subst. rewrite H in H0. discriminate.
  - subst. apply IHceval2.
  -- reflexivity. -- assumption.
  - subst. exists st. assumption.
Qed.

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
 (* SOLUTION: *)
  intros.
  generalize dependent s2.
  generalize dependent st2.
  induction H;intros;subst;
  try (inversion H0;split;reflexivity;reflexivity).
  try (inversion H0; subst; split;reflexivity;reflexivity).
  - apply IHceval. inversion H1. subst. apply H9.
  - apply IHceval2. inversion H1; subst. 
  -- apply IHceval1 in H4. destruct H4. subst. apply H8.
  -- apply IHceval1 in H7. destruct H7. inversion H3.
  - apply IHceval. inversion H0;subst.
  -- apply IHceval in H3. destruct H3. inversion H2.
  -- apply IHceval in H6. destruct H6. subst. apply H.
  - inversion H0;subst;
  try( split; reflexivity; reflexivity);
  try( rewrite H in H3; inversion H3).
  - apply IHceval2. inversion H2;subst.
  -- rewrite H in H8. inversion H8.
  -- apply IHceval1 in H6. destruct H6. rewrite H3. apply H10.
  -- apply IHceval1 in H9. destruct H9. inversion H4.
  - inversion H1;subst.
  -- rewrite H in H7. inversion H7.
  -- apply IHceval in H5. destruct H5. inversion H3.
  -- split.
  + apply IHceval in H8. destruct H8. apply H2.
  + reflexivity.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. info_auto. Qed.
End BreakImp. 

 
 
  





