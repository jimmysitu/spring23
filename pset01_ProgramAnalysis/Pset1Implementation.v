(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 1 *)

(* Welcome to 6.512!  Read through `Pset1Signature.v` before starting here. *)

Require Import Frap Pset1Signature.

Module Impl.
  (* The first part of this assignment involves the [bool] datatype,
   * which has the following definition.
   * <<
       Inductive bool :=
       | true
       | false.
     >>
   * We will define logical negation and conjunction of Boolean values,
   * and prove some properties of these definitions.
   *)

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  Definition Neg (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.


  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  Theorem Neg_true : Neg true = false.
  Proof.
    unfold Neg.
    reflexivity.
  Qed.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
  Proof.
    intros b.
    cases b.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  Definition And (x y : bool) : bool :=
    match (x, y) with
    | (true, true) => true
    | (_, _) => false
    end.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  Theorem And_true_true : And true true = true.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem And_false_true : And false true = false.
  Proof.
    simpl. reflexivity.
  Qed.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  Theorem And_comm : forall x y : bool, And x y = And y x.
  Proof.
    (* We will use cases on x and y to prove commutativity. *)
    intros x y.
    destruct x, y; simpl.
    - reflexivity. (* Case: x = true, y = true *)
    - reflexivity. (* Case: x = true, y = false *)
    - reflexivity. (* Case: x = false, y = true *)
    - reflexivity. (* Case: x = false, y = false *)
  Qed.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  Theorem And_true_r : forall x : bool, And x true = x.
  Proof.
    intros x.
    destruct x.
    - reflexivity.
    - reflexivity.
  Qed.

  (* You may have noticed that the [=] operator above does not return a [bool]. *)
  Check (true = false).
  
  (* [a = b] is instead a [Prop], short for proposition, the type of logical
   * statements. The set of propositions in Coq is large and contains a variety
   * of statements, many of which are undecideable, so we can't in general
   * treat statements in [Prop] as functions with Boolean output. This means
   * that you can't use expressions of type [Prop] when defining a program,
   * since they don't have computational behavior. For example, compare how
   * the following two expressions evaluate. The first expression uses functions
   * we can compute with, while the second uses propositions:
   *)
  Compute (if 1 ==n 2 then (And true false) else true).
  Compute (1 = 2 -> True /\ False).
  
  (* The following operations that you have seen or will see soon are in [Prop],
   * so they cannot be used in if-then-else statements:
   * - [a = b] (equality at an arbitrary type)
   * - [a <= b] (a less than or equal to b for natural numbers)
   * - [a < b] (a less than b for natural numbers)
   * - [a >= b] (a greater than or equal to b for natural numbers)
   * - [a > b] (a greater than b for natural numbers)
   * - [a <> b] (inequality at an arbitrary type)
   * - [a /\ b] (propositional conjunction)
   * - [~ a] (propositional negation)
   *
   * These operations are defined as functions, so you can evalute them:
   * - [a ==n b] (decidable equality for natural numbers)
   * - [a ==v b] (decidable equality for variables)
   * - [And a b] (Boolean conjunction, defined above)
   * - [Neg a] (Boolean negation, defined above)
   *)
  
  (* In the second part of this assignment, we will work with a simple language
   * of imperative arithmetic programs that sequentially apply operations
   * to a natural-number-valued state.

   * The [Prog] datatype defines abstract syntax trees for this language.
   *)

  Print Prog.

  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   *)
  Fixpoint run (p : Prog) (initState : nat) : nat :=
    match p with
    | Done => initState
    | AddThen n p' => run p' (initState + n)
    | MulThen n p' => run p' (initState * n)
    | DivThen n p' => run p' (initState / n)
    | VidThen n p' => run p' (n / initState)
    | SetToThen n p' => run p' n
    end.

  Theorem run_Example1 : run Done 0 = 0.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Proof.
    simpl. reflexivity.
  Qed.

  Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
  Proof.
    simpl. reflexivity.
  Qed.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Fixpoint numInstructions (p : Prog) : nat :=
    match p with
    | Done => 0
    | AddThen _ p' => 1 + numInstructions p'
    | MulThen _ p' => 1 + numInstructions p'
    | DivThen _ p' => 1 + numInstructions p'
    | VidThen _ p' => 1 + numInstructions p'
    | SetToThen _ p' => 1 + numInstructions p'
    end.


  Theorem numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
  Proof.
    simpl. reflexivity.
  Qed.


  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Fixpoint concatProg (p1 p2 : Prog) : Prog :=
    match p1 with
    | Done => p2
    | AddThen n p' => AddThen n (concatProg p' p2)
    | MulThen n p' => MulThen n (concatProg p' p2)
    | DivThen n p' => DivThen n (concatProg p' p2)
    | VidThen n p' => VidThen n (concatProg p' p2)
    | SetToThen n p' => SetToThen n (concatProg p' p2)
    end.

  Theorem concatProg_Example :
       concatProg (AddThen 1 Done) (MulThen 2 Done)
       = AddThen 1 (MulThen 2 Done).
  Proof.
    simpl.
    reflexivity.
  Qed.

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Theorem concatProg_numInstructions
    : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                        = numInstructions p1 + numInstructions p2.
  Proof.
    intros p1 p2.
    induction p1 as [| n p1' IH | n p1' IH | n p1' IH | n p1' IH | n p1' IH].
      simpl. reflexivity.
    - (* Case: p1 = AddThen n p1' *)
      simpl. rewrite IH. reflexivity.
    - (* Case: p1 = MulThen n p1' *)
      simpl. rewrite IH. reflexivity.
    - (* Case: p1 = DivThen n p1' *)
      simpl. rewrite IH. reflexivity.
    - (* Case: p1 = VidThen n p1' *)
      simpl. rewrite IH. reflexivity.
    - (* Case: p1 = SetToThen n p1' *)
      simpl. rewrite IH. reflexivity.
  Qed.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Theorem concatProg_run
    : forall (p1 p2 : Prog) (initState : nat),
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).
  Proof.
    intros p1 p2.
    induction p1 as [| n p1' IH | n p1' IH | n p1' IH | n p1' IH | n p1' IH].
    - simpl. reflexivity.
    - simpl. intros. rewrite IH. reflexivity.
    - simpl. intros. rewrite IH. reflexivity.
    - simpl. intros. rewrite IH. reflexivity.
    - simpl. intros. rewrite IH. reflexivity.
    - simpl. intros. rewrite IH. reflexivity.
  Qed.

  (* Read this definition and understand how division by zero is handled. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.
  Arguments Nat.div : simpl never. (* you don't need to understand this line *)

  (* Here are a few examples: *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Example runPortable_good : forall n,
    runPortable goodProgram1 n = (true, 10/(1+n)).
  Proof. simplify. equality. Qed.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Example runPortable_bad : let n := 0 in
    runPortable badProgram1 n = (false, 0).
  Proof. simplify. equality. Qed.

  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  Example runPortable_bad2 : forall n,
    runPortable badProgram2 n = (false, 1+n).
  Proof. simplify. equality. Qed.

  (* Prove that running the concatenation [p] using [runPortable]
     coincides with using [run], as long as [runPortable] returns
     [true] to confirm that no divison by zero occurred. *)
  Lemma runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.
  Proof.
    (* We proceed by induction on the program p *)
    induction p; intros s0 s1 H.
    
    - (* Case: Done *)
      simpl in H.
      inversion H.
      reflexivity.
  
    - (* Case: AddThen n p *)
      simpl in H.
      destruct (runPortable p (n + s0)) eqn:Hp.
      destruct b.
      + (* Subcase: runPortable p (n + s0) = (true, s1) *)
        simpl.
        apply IHp.
        rewrite <- H.
        rewrite <- Hp.
        f_equal.
        apply Nat.add_comm.
      + (* Subcase: runPortable p (n + s0) = (false, n0) *)
        discriminate H.
  
    - (* Case: MulThen n p *)
      simpl in H.
      destruct (runPortable p (n * s0)) eqn:Hp.
      destruct b.
      + (* Subcase: runPortable p (n * s0) = (true, s1) *)
        simpl.
        apply IHp.
        rewrite <- H.
        rewrite <- Hp.
        f_equal.
        apply Nat.mul_comm.
      + (* Subcase: runPortable p (n * s0) = (false, n0) *)
        discriminate H.
  
    - (* Case: DivThen n p *)
      simpl in H.
      destruct (n ==n 0) eqn:Hn.
      + (* Subcase: n == 0 *)
        discriminate H.
      + (* Subcase: n != 0 *)
        destruct (runPortable p (s0 / n)) eqn:Hp.
        destruct b.
        * (* Sub-subcase: runPortable p (s0 / n) = (true, s1) *)
          simpl.
          apply IHp.
          rewrite <- H.
          assumption.
        * (* Sub-subcase: runPortable p (s0 / n) = (false, n0) *)
          discriminate H.
  
    - (* Case: VidThen n p *)
      simpl in H.
      destruct (s0 ==n 0) eqn:Hs.
      + (* Subcase: s0 == 0 *)
        discriminate H.
      + (* Subcase: s0 != 0 *)
        destruct (runPortable p (n / s0)) eqn:Hp.
        destruct b.
        * (* Sub-subcase: runPortable p (n / s0) = (true, s1) *)
          simpl.
          apply IHp.
          rewrite <- H.
          assumption.
        * (* Sub-subcase: runPortable p (n / s0) = (false, n0) *)
          discriminate H.
  
    - (* Case: SetToThen n p *)
      simpl in H.
      destruct (runPortable p n) eqn:Hp.
      destruct b.
      + (* Subcase: runPortable p n = (true, s1) *)
        simpl.
        apply IHp.
        rewrite <- H.
        assumption.
      + (* Subcase: runPortable p n = (false, n0) *)
        discriminate H.
  Qed.

  (* The final goal of this pset is to implement [validate : Prog -> bool]
     such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     division by zero, but it must recognize as good the examples given below.  In
     jargon, [validate] is required to be sound but not complete, but "complete
     enough" for the use cases defined by the examples given here: *)

  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

  (* If you already see a way to build [validate] that meets the
   * requirements above, _and have a plan for how to prove it correct_,
   * feel free to just code away. Our solution uses one intermediate definition
   * and one intermediate lemma in the soundness proof -- both of which are more
   * sophisticated than the top-level versions given here. *)

  (* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
   * take a look at the hints for this pset at the end of the signature file.
   * It is not expected that this pset is doable for everyone without the hints,
   * and some planning is required to complete the proof successfully.
   * In particular, repeatedly trying out different combinations of tactics
   * and ideas from hints until something sticks can go on for arbitrarily long
   * with little insight and no success; just guessing a solution is unlikely.
   * Thus, we encourage you to take your time to think, look at the hints when
   * necessary, and only jump into coding when you have some idea why it should
   * succeed. Some may call Coq a video game, but it is not a grinding contest. *)

  Fixpoint validate' (p : Prog) (nz: bool) : bool :=
    match p with
    | Done => true
    | AddThen n p' => if n==n 0 then validate' p' nz else validate' p' true
    | MulThen n p' => if n==n 0 then validate' p' false else validate' p' nz
    | DivThen n p' => if n==n 0 then false else validate' p' nz 
    | VidThen n p' => if nz then validate' p' nz else false
    | SetToThen n p' => if n==n 0 then validate' p' false else validate' p' true
    end.

  Definition validate (p : Prog) : bool :=
    validate' p false.
(*
  Definition validate (p : Prog) : bool :=
    let fix validate' (p : Prog) (nz: bool) : bool :=
      match p with
      | Done => true
      | AddThen n p' => if n==n 0 then validate' p' nz else validate' p' true
      | MulThen n p' => if n==n 0 then validate' p' false else validate' p' nz
      | DivThen n p' => if n==n 0 then false else validate' p' nz 
      | VidThen n p' => if nz then validate' p' nz else false
      | SetToThen n p' => if n==n 0 then validate' p' false else validate' p' true
      end
    in validate' p false.
*)

  (* Start by making sure that your solution passes the following tests, and add
   * at least one of your own tests: *)

  Example validate1 : validate goodProgram1 = true.
  Proof.
    simpl. reflexivity.
  Qed.

  Example validate2 : validate goodProgram2 = true.
  Proof.
    simpl. reflexivity.
  Qed.
  
  Example validate3 : validate goodProgram3 = true. 
  Proof.
    simpl. reflexivity.
  Qed.
  
  Example validate4 : validate goodProgram4 = true.
  Proof.
    simpl. reflexivity.
  Qed.
  
  Example validate5 : validate goodProgram5 = true.
  Proof.
    simpl. reflexivity.
  Qed.
  
  Example validate6 : validate goodProgram6 = true.
  Proof.
    simpl. reflexivity.
  Qed.
  
  Example validate7 : validate goodProgram7 = true.
  Proof.
    simpl. reflexivity.
  Qed.
  
  Example validateb1 : validate badProgram1 = false.
  Proof.
    simpl. reflexivity.
  Qed.
  
  Example validateb2 : validate badProgram2 = false.
  Proof.
    simpl. reflexivity.
  Qed.

  (* Then, add your own example of a bad program here, and check that `validate`
   * returns `false` on it: *)

  Definition badProgram3 : Prog := MulThen 0 (VidThen 5 Done). 
  Example validateb3 : validate badProgram3 = false.
  Proof.
    simpl. reflexivity.
  Qed.



  (* Finally, before diving into the Coq proof, try to convince yourself that
   * your code is correct by applying induction by hand.  Can you describe the
   * high-level structure of the proof?  Which cases will you have to reason
   * about?  What do the induction hypotheses look like?  Which key lemmas do
   * you need?  Write a short (~10-20 lines) informal proof sketch before
   * proceeding. *)

  (** Proof sketch: **)
  (* [[Fill in your proof sketch here.]] *)

  (* Now you're ready to write the proof in Coq: *)
  Lemma validate_sound' : forall p,
    (validate' p true = true ->
      forall s, s <> 0 -> runPortable p s = (true, run p s)) /\
    (validate' p false = true ->
       forall s, runPortable p s = (true, run p s)).
  Proof.
    intros p.
    split; intros H.
    - admit.
    - induction p as [| n p' IH | n p' IH | n p' IH | n p' IH | n p' IH].
      + (* Case: Done *)
        auto.

      + (* Case: AddThen n p' *) 
        intros s.
        simpl.
        rewrite Nat.add_comm.
        destruct (s ==n 0) eqn:Hs.
        * apply IH. 
(* TODO *)

(* Not workable below, 
  Lemma validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
  Proof.
    unfold validate.
    intros p Hval.
    induction p as [ | n p' IH | n p' IH | n p' IH | n p' IH | n p' IH ].
    - (* Case: Done *)
      simpl. reflexivity.

    - (* Case: AddThen n p' *)
      simpl in Hval. 
      simpl.
      intros s.
      rewrite Nat.add_comm.
      apply IH. 
      apply Hval.

    - (* Case: MulThen n p' *)
      simpl in Hval.
      simpl.
      intros s.
      rewrite Nat.mul_comm.
      apply IH. 
      apply Hval.

    - (* Case: DivThen n p' *)
      simpl in Hval.
      simpl.
      intros s.
      destruct (n ==n 0) eqn:Hn.
      + (* Subcase: n == 0 *)
        discriminate Hval.
      + (* Subcase: n != 0 *)
        apply IH.
        apply Hval.

    - (* Case: VidThen n p' *)
      simpl in Hval.
      simpl.
      intros s.
      destruct (s ==n 0) eqn:Hs.
      + (* Subcase: s == 0 *)
        admit.
      + (* Subcase: s != 0 *)
        apply IH.
        apply Hval.

    - (* Case: SetToThen n p' *)
      simpl in Hval.
      intros s.
      simpl.
      apply IH.
      apply Hval.
  Admitted.
*)
  (* Here is the complete list of commands used in one possible solution:
    - Search, for example Search (_ + 0).
    - induct, for example induct x
    - simplify
    - propositional
    - equality
    - linear_arithmetic
    - cases, for example cases (X ==n Y)
    - apply, for example apply H
    - apply in, for example apply H1 in H2 or apply somelemma in H1
    - apply with, for example apply H1 with (x:=2)
    - apply in with, for example apply H1 with (x:=2) in H2
    - rewrite, for example rewrite H
    - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
    - ;, for example simplify; propositional *)
End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Coq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset1Signature.S := Impl.
