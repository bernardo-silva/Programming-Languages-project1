From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3. TODO: Define the relational semantics (ceval) to support the required constructs.
*)

Inductive ceval : com -> state -> list (state * com) -> 
          result -> state -> list (state * com) -> Prop :=
| E_Skip : forall st q,
    st / q =[ skip ]=> st / q / Success
| E_Asng : forall st q a n x,
    aeval st a = n ->
    st / q =[ x := a ]=> (x !-> n;st) / q / Success
| E_Seq : forall c1 c2 st st' st'' q q' q'' result,
    st / q =[ c1 ]=> st' / q' / Success ->
    st' / q' =[ c2 ]=> st'' / q'' / result ->
    st / q =[ c1 ; c2 ]=> st'' / q'' / result
| E_IfTrue  : forall st st' q q' b c1 c2,
    beval st b = true ->
    st / q =[ c1 ]=> st' / q' / Success ->
    st / q =[ if b then c1 else c2 end ]=> st' / q' / Success
| E_IfFalse  : forall st st' q q' b c1 c2,
    beval st b = false ->
    st / q =[ c2 ]=> st' / q' / Success ->
    st / q =[ if b then c1 else c2 end ]=> st' / q' / Success
| E_WhileTrue  : forall st st' st'' q q' q'' b c,
    beval st b = true ->
    st / q =[ c ]=> st' / q' / Success ->
    st' / q' =[ while b do c end ]=> st'' / q'' / Success ->
    st / q =[ while b do c end ]=> st'' / q'' / Success
(* | E_Choice1 : forall st st' q q' c1 c2, *)
(*     st / ((st , c2)::q) =[ c1 ]=> st' / q' / Success -> *)
(*     st / q =[ c1 !! c2 ]=> st' / q' / Success *)
(* | E_Choice2 : forall st st' q q' c1 c2, *)
(*     st / ((st , c1)::q) =[ c2 ]=> st' / q' / Success -> *)
(*     st / q =[ c1 !! c2 ]=> st' / q' / Success *)
| E_Choice1 : forall st st' q q' c1 c2 res,
    st / q =[ c1 ]=> st' / q' / res ->
    st / q =[ c1 !! c2 ]=> st' / ((st , c2)::q') / res
| E_Choice2 : forall st st' q q' c1 c2 res,
    st / q =[ c2 ]=> st' / q' / res ->
    st / q =[ c1 !! c2 ]=> st' / ((st , c1)::q') / res
| E_GuardTrue : forall st st' q q' b c,
    beval st b = true ->
    st / q =[ c ]=> st' / q' / Success ->
    st / q =[ b -> c ]=> st' / q' / Success
| E_GuardFalseCont : forall st st' st'' st''' q q' q'' t b c1 c2 ,
    beval st b = false ->
    q = (st', c1)::t -> 
    st' / t =[ c1 ]=> st'' / q' / Success ->
    beval st'' b = true ->
    st'' / q' =[ c2 ]=> st'''/ q'' / Success ->
    st / q =[ b -> c2 ]=> st''' / q'' / Success
| E_GuardFalseEmpty : forall st b c,
    beval st b = false ->
    st / [] =[ b -> c]=> empty_st / [] / Fail
(* TODO. Hint: follow the same structure as shown in the chapter Imp *)
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).


(**
  3.1. TODO: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2) [].
    - apply E_Asng. reflexivity.
    - apply E_IfFalse.
      reflexivity.
      apply E_Asng. reflexivity.
Qed.


Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  eapply E_Seq.
  - apply E_Asng. reflexivity.
  - apply E_GuardFalseEmpty. reflexivity.
(*   eapply E_SeqFail2 with(X !-> 2). *)
(*     - apply E_Asng. reflexivity. *)
(*     - apply E_GuardFalseEmpty. reflexivity.    *)
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X!->2) [].
    - apply E_Asng. reflexivity.
    - apply E_GuardTrue.
      -- reflexivity.
      -- apply E_Asng. reflexivity.
Qed. 

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X := 3
]=> (X !-> 3) / q / Success.
Proof.
  eexists ?[x].
  apply E_Seq with (X!->2) ?x.
  - apply E_Choice2.
    apply E_Asng. reflexivity.
  - apply E_GuardTrue.
    -- reflexivity.
    -- assert ((X!->3 ; X!->2)=(X!->3)) by (apply t_update_shadow).
       rewrite <- H.
       apply E_Asng. reflexivity.
Qed.
    
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  eexists.
  eapply E_Seq.
  - apply E_Choice1. apply E_Asng. reflexivity.
  - eapply E_GuardFalseCont; try reflexivity.
    -- apply E_Asng. reflexivity.
    -- reflexivity.
    -- assert ((X!->3 ; X!->2)=(X!->3)) by (apply t_update_shadow).
       rewrite <- H.
       apply E_Asng.
       reflexivity.
(*
  eexists ?[x].
  apply E_Seq with (X!->1) [(empty_st,<{X:=2}>)].
  - apply E_Choice1. apply E_Asng. reflexivity.
  - apply E_GuardFalseCont with empty_st (X!->2) [] [] <{ X := 2 }>; try reflexivity.
    -- apply E_Asng. reflexivity.
    -- assert ((X!->3 ; X!->2)=(X!->3)) by (apply t_update_shadow).
       rewrite <- H.
       apply E_Asng.
       reflexivity.*)
Qed.



(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2. TODO: Prove the properties below.
*)

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  split.
  - eexists. instantiate (1:=q2).
    inversion H; subst.
    inversion H2; subst. simpl in H2.
    inversion H8; subst. simpl in H8.
    inversion H10; subst. simpl in H10.
    clear H3.
    -- eapply E_Asng. reflexivity.
    -- discriminate.
    -- discriminate.
  - eexists.
    inversion H; subst.
    eapply E_Seq.
      -- apply E_Asng. reflexivity.
      -- simpl. apply E_GuardTrue.
        --- reflexivity.
        --- apply E_Skip.
Qed.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  split.
  (*   <{ X := 1 !! X := 2; X = 2 -> skip }> =
  <{ X := 2 }> *)
  - unfold cequiv_imp. intros.
    inversion H; subst.
    inversion H2; subst. simpl in H2. 
    inversion H9; subst. simpl in H9.
    inversion H8; subst. simpl in H8.
    inversion H11; subst. simpl in H11.
    (* Choice 1 - Guard true *)
    -- discriminate.
    (* Choice 1 - Guard false *)
    -- inversion H14; subst. 
       (*symmetry in H4*)
       inversion H4; subst.
       inversion H5; subst.
       eexists.
       eapply E_Asng. reflexivity.
    (* Choice 2 - Guard true *)
    -- inversion H9; subst. simpl in H9.
       inversion H8; subst.
       eexists.
      --- inversion H11; subst.
          inversion H3; subst.
          eapply E_Asng. reflexivity.
      --- discriminate.  
  - eexists.
    inversion H; subst; simpl in H.
    simpl.
    eapply E_Seq.
    -- eapply E_Choice2. 
       eapply E_Asng. reflexivity.
    -- simpl. eapply E_GuardTrue; 
       try reflexivity.
       eapply E_Skip.
Qed.


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
split; unfold cequiv_imp; intros.
  - inversion H; subst; eexists; eassumption.
  - inversion H; subst; eexists; try apply E_Choice1; try eassumption.
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  split; unfold cequiv_imp; intros.
  - inversion H; subst. 
    -- eexists. 
       eapply E_Choice2. 
       eassumption.
    -- eexists. 
       eapply E_Choice1. 
       eassumption.
  - inversion H; subst. 
    -- eexists. 
       eapply E_Choice2. 
       eassumption.
    -- eexists. 
       eapply E_Choice1. 
       eassumption.
Qed. 

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
split; unfold cequiv_imp; intros.
  - inversion H; subst.
    inversion H7; subst.
    -- eexists.  
       eapply E_Choice1.
       eassumption.
    -- eexists.
       eapply E_Choice2.
       eapply E_Choice1. 
       eassumption.
    -- eexists.
       eapply E_Choice2.
       eapply E_Choice2. 
       eassumption.
  - inversion H; subst.
    -- eexists.
       eapply E_Choice1.
       eapply E_Choice1.
       eassumption.
    -- inversion H7; subst.
      --- eexists.
          eapply E_Choice1.
          eapply E_Choice2.
          eassumption.
      --- eexists.
          eapply E_Choice2.
          eassumption.   
Qed.


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
split; unfold cequiv_imp; intros.
  - inversion H; subst.
    inversion H8; subst.
    -- eexists.
       apply E_Choice1.
       eapply E_Seq.
      --- instantiate (1:=q').
          instantiate (1:=st').
          assumption.
      --- instantiate (1:=q'0).
          assumption.
    -- eexists. 
       apply E_Choice2.
       eapply E_Seq.
      --- instantiate (1:=q').
          instantiate (1:=st').
          assumption.
      --- instantiate (1:=q'0).
          assumption.
  - inversion H; subst.
    inversion H7; subst.
    -- eexists.
       eapply E_Seq.
      --- instantiate (1:=q'0).
          instantiate (1:=st').
          assumption.
      --- eapply E_Choice1.
          instantiate (1:=q').
          assumption.
    -- inversion H7; subst.
       eexists.
       eapply E_Seq.
      --- instantiate (1:=q'0).
          instantiate (1:=st').
          assumption.
      ---  apply E_Choice2.
           instantiate (1:=q').
           assumption.
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
intros c1 c1' c2 c2' H_Eq1 H_Eq2.
split.
  - unfold cequiv_imp; intros.
    inversion H; subst.
    -- apply H_Eq1 in H7. 
       inversion H7.
       eexists.
       apply E_Choice1.
       eassumption.
    -- apply H_Eq2 in H7. 
       inversion H7.
       eexists.
       apply E_Choice2.
       eassumption.
  - unfold cequiv_imp; intros.
    inversion H; subst.
    -- apply H_Eq1 in H7. 
       inversion H7.
       eexists.
       apply E_Choice1.
       eassumption.
    -- apply H_Eq2 in H7. 
       inversion H7.
       eexists.
       apply E_Choice2.
       eassumption.
Qed.