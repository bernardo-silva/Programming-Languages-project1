From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.


Inductive interpreter_result : Type :=
  | Success (s: state * (list (state*com)))
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)


Notation "'LETOPT' st , c <== e1 'IN' e2"
  := (match e1 with
          | Success (st,c) => e2
          | Fail => Fail
          | OutOfGas => OutOfGas
       end)
(right associativity, at level 60).

(**
  2.1. TODO: Implement ceval_step as specified. To improve readability,
             you are strongly encouraged to define auxiliary notation.
             See the notation LETOPT in the ImpCEval chapter.
**)

Check (LETOPT st , c <== Success (("x" !-> 2),[]) IN Success (st,c)).

Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | 0 => OutOfGas
  | S i' =>
    match c with
    | <{ skip }> => Success (st, continuation)
    | <{ v := a1 }> => Success ((v !-> aeval st a1; st), continuation)
    | <{ c1 ; c2 }> => 
        LETOPT st' , cont' <== ceval_step st c1 continuation i' IN ceval_step st' c2 cont' i' 
    | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 continuation i'
            else ceval_step st c2 continuation i'
    | <{ while b1 do c1 end }> =>
          if (beval st b1) then 
            LETOPT st' , cont' <== ceval_step st c1 continuation i' IN 
                ceval_step st' c cont' i'
          else Success (st, continuation)
    | <{ c1 !! c2 }> => 
        ceval_step st c1 ((st,c2)::continuation) i'
    | <{ b1 -> c1 }> => 
      if (beval st b1)
      then ceval_step st c1 continuation i'
      else 
        match continuation with
         | (st', c')::t => ceval_step st' <{c';c}> t i'
         | [] => Fail
         end
    end
  end.



(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)
Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_3: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 3 = OK [("X", 8); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 2 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Example test_7:
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  8 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.



(**
  2.2. TODO: Prove p1_equals_p2. Recall that p1 and p2 are defined in Imp.v
*)


(* 
  This therorem state that, given enough gas (i0),
programs p1 and p2 will always evaluate to the same 
resulta
*)
Theorem p1_equals_p2: forall st cont,
  (exists i0,
    (forall i1, i1 >= i0 -> ceval_step st p1 cont i1 =  ceval_step st p2 cont i1)).
Proof.
  intros st cont.
  eexists. instantiate (1:=5).
  destruct i1. lia.
  destruct i1. lia.
  destruct i1. lia.
  destruct i1. lia.
  destruct i1. lia.
  destruct i1; reflexivity.
Qed.


(**
  2.3. TODO: Prove ceval_step_more.
*)

(* 
  This therorem state that if a program
 c is evaluated successfully with a given gas
 it will always evalate to succeed with more gas
*)

Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
  induction i1 as [|i1']; 
  intros i2 st st' c cont cont' Hle Hceval.
  (* i1 = 0 *)
  - simpl in Hceval. discriminate Hceval.
  (* i1 = S i1' *)
  - destruct i2 as [|i2']. 
    inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c; try apply Hceval;
    simpl; simpl in Hceval.
    (* ; *)
    -- destruct (ceval_step st c1 cont i1') eqn:Heqst1'o; 
       try discriminate.
      --- destruct s as [st'' cont'']. 
          apply (IHi1' i2') in Heqst1'o; 
          try assumption.
          rewrite Heqst1'o. 
          apply (IHi1' i2') in Hceval; 
          try assumption. 
    (* if *)
    -- destruct (beval st b);
       apply (IHi1' i2') in Hceval;
       try assumption.
    (* while *)
    -- destruct (beval st b).
       destruct (ceval_step st c cont i1') eqn: Heqst1'o; try discriminate.
      --- destruct s as [st'' cont''].
          apply (IHi1' i2') in Heqst1'o; 
          try assumption.
          rewrite Heqst1'o. 
          apply (IHi1' i2') in Hceval; 
          try assumption.
      --- assumption.
    (* !! *)
    -- apply (IHi1' i2') in Hceval; 
       try assumption. 
    (* -> *)
    -- destruct (beval st b).
      --- apply (IHi1' i2') in Hceval; 
          try assumption.
      --- destruct cont; try discriminate.
          destruct p.
          apply (IHi1' i2') in Hceval;
          assumption.
Qed.
