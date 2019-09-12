Require Import POCS.
Require Import ThreeVariablesAPI.

(** To start with, we define a module called [Exercises] that
    takes as an argument an implementation of our variables
    layer, called [vars].
  *)

Module Exercises (vars : VarsAPI).

  (** Now that we are inside the module, we have access to the
      variables API that we defined in [ThreeVariablesAPI].
      You can examine the functions provided by the [vars]
      module using the [Check] command, as follows: *)

  Check vars.read.

  (** The above [Check] command should have printed:

      <<
        vars.read
             : var -> proc nat
      >>

      meaning that [vars.read] is something that takes a variable
      name (of type [var]) and gives us a procedure that returns
      a [nat] value.
    *)

  Check vars.write.

  (** [vars.write] similarly takes a variable name and a new value
      and gives us a procedure with no return value.
    *)

  (** * Part A: incrementing and swapping. *)

  (** To start with, we will define a simple procedure [incX]
      that increments the value of the x variable: *)

  Definition incX : proc unit :=
    x <- vars.read VarX;
    _ <- vars.write VarX (1+x);
    Ret tt.

  (** To check if we got the implementation right, let's try first
      testing it on a specific input.  We can do this by writing a
      very particular specification: if the starting state was
      (1, 2, 3), corresponding to the values of variables x, y, and
      z respectively, then the final state should be (2, 2, 3).

      The [vars.recover] at the end of the specification says that
      we should run the [vars.recover] procedure after a crash; this
      does not matter so far, because we are ignoring crashes.

      The [vars.abstr] indicates how we are describing states in
      this specification.  Here, states are described in terms of
      the variables layer (i.e., consisting of the three values for
      x, y, and z).  We will see in the next lab how and why your
      specification may want to describe the state at a different
      abstraction layer.
    *)

  Theorem incX_test :
    proc_spec (fun (_:unit) state => {|
                    pre :=
                      state = mkState 1 2 3;
                    post := fun r state' =>
                      state' = mkState 2 2 3;
                    recovered := fun _ _ => False;
                  |})
              incX
              vars.recover vars.abstr.
  Proof.
    (*  Pretty much every proof in our lab infrastructure
        starts by expanding out the procedure you're proving.
      *)
    unfold incX.

    (*  We will now consider each step of this code in turn,
        using the [step_proc] Ltac tactic.  [step_proc] will
        take the first thing our code is doing (here, calling
        [vars.read VarX]) and find a corresponding proven spec
        for that code (here, it comes from [vars.read_ok],
        which states that [vars.read] satisfies [read_spec]).
      *)
    step_proc.

    (* We will potentially have to prove several subgoals after
      calling [step_proc]: that our precondition is sufficient to
      invoke the proven spec that [step_proc] found, that the
      recovery condition matches up, and that the rest of the
      procedure will be correct. Here, most of these were trivial
      and were proven automatically, so we are left with just one
      goal.

      This remaining goal requires us to prove something about
      executing the rest of the [incX] code. To help orient yourself
      in this proof ("what is this that I'm having to prove?"), look
      at [Lexec] in your proof context. It's a marker telling you
      that the current proof goal is what's left "after" running
      [(vars.read VarX)].

      This time, to illustrate what step_proc is doing, we break
      it apart into several steps.  This first invocation does
      everything step_proc does except solve trivial goals. *)

    step_proc_basic; simplify; split_all; simplify.

    (* We are now left with several sub-goals that we have
      to prove.  To orient yourself among these subgoals,
      look for [Marker] hypotheses in the context.  In this
      first subgoal, you should see [L] as a marker indicating
      that we are looking at a subgoal related to the precondition
      of [vars.write VarX 2].  The precondition happens to be
      just [True], so it would have been automatically solved
      if you had invoked the full [step_proc] tactic.
      *)

    {
      (* To solve this subgoal, we must use curly braces
        (or dashes), in order to keep the proof script
        clean and readable.

        Since the goal is [True], we can solve it using the
        [trivial] tactic.  [eauto] would have also worked.
        *)

      trivial.
    }

    {
      (* The next subgoal left for us by [step_proc_basic]
        relates to the recovery condition of [vars.write VarX 2],
        which you can determine by looking at the bottom-most
        [Marker] in the current context.

        Since we aren't reasoning about crashes in this lab,
        every recovered condition is [False].  You can prove
        this using the recovered condition of the [vars.read
        VarX] operation, which is [H: False].

        [assumption] does this, as would [eauto].
        *)
      assumption.
    }

    (*  Now we are left with the remaining part of the [incX] code:
        the call to [Ret tt].

        You can see there are two markers in your proof context now,
        since these markers simply accumulate. The bottom marker
        will always be the most recent one, so here [Lexec0] tells
        you that you're looking at the proof state just after
        calling [vars.write VarX (StateX {| ... |} + 1)].

        What's left for us to prove? The goal is saying something
        pretty simple: if the starting state is (2, 2, 3), as
        specified by the precondition, then running [Ret tt] gives
        us a state of (2, 2, 3).

        Invoking [step_proc] proves this simple fact. *)
    step_proc.
  Qed.

  (** Now your job is to state a more general specification for [incX]. It
      should take a precondition of [True], as stated in the theorem below. Your
      task is to fill in the postcondition below so that it applies to any
      starting state, unlike the previous theorem that only worked for [mkState
      1 2 3]. Then, prove your general specification correct.

      Replace [Admitted.] with [Qed.] when the proof is complete. When we grade,
      we basically check that your code compiles and that you didn't use
      [Admitted].

      Take a look at the specifications in ThreeVariablesAPI.v if you're not
      sure where to start.
  *)

  Theorem incX_ok :
    proc_spec (fun (_:unit) state => {|
                    pre := True;
                    post := fun r state' =>
                      (* EXERCISE: replace with your postcondition *)
                      state' = state;
                    recovered := fun _ _ => False;
                  |})
              incX
              vars.recover vars.abstr.
  Proof.
    (* EXERCISE: Fill in your proof here. *)
  Admitted.

  (** You have proven that the code of [incX] satisfies your specification
      in [incX_ok], but how do you know if your specification is good enough?
      Did your specification omit any important details?

      One general approach is to try to use your specification to prove something.
      Let's do that now: prove that your specification above is sufficient
      to prove that running [incX] from state (5, 5, 5) gives us state (6, 5, 5).

      To use your [incX_ok] theorem from above, we tell the [step_proc] tactic
      about it by including it in the [core] hints database.  To make sure that
      we don't accidentally look inside the code of [incX], and thus force ourselves
      to prove statements about [incX] by relying on [incX_ok], we mark it opaque
      using [Opaque incX].
    *)

  Hint Resolve incX_ok : core.
  Opaque incX.

  Theorem incX_ok_seems_good :
    proc_spec (fun (_:unit) state => {|
                    pre :=
                      state = mkState 5 5 5;
                    post := fun r state' =>
                      state' = mkState 6 5 5;
                    recovered := fun _ _ => False;
                  |})
              incX
              vars.recover vars.abstr.
  Proof.
    (* EXERCISE: Fill in your proof here. Most likely [step_proc.] will be
    enough to prove the entire theorem, if your specification is correct. *)
  Admitted.


  (** * Swapping. *)

  (** Here is another exercise, this time with you writing the code,
      the spec, and the proof.  Implement a procedure [swapXY] that
      swaps the values of x and y; write a specification for it; and
      prove that your code meets the spec. *)

  Definition swapXY : proc unit :=
    (* EXERCISE: Fill in your code here. *)
    Ret tt.

  Theorem swapXY_ok :
    (* EXERCISE: Fill in your spec here. *)
    True.
  Proof.
    (* EXERCISE: Fill in your proof here. *)
  Admitted.

  (** As a sanity check, prove that [swapXY] from state (2, 3, 4)
      gives you state (3, 2, 4). *)

  Hint Resolve swapXY_ok : core.
  Opaque swapXY.

  Theorem swapXY_ok_seems_good :
    proc_spec (fun (_:unit) state => {|
                   pre := state = mkState 2 3 4;
                   post := fun r state' => state' = mkState 3 2 4;
                   recovered := fun _ state' => False;
                 |})
              swapXY
              vars.recover
              vars.abstr.
  Proof.
    (* EXERCISE: Fill in your proof here. *)
  Admitted.


  (** * Part B: recursive procedures. *)

  (** In this last part of the lab assignment, you will reason about
      recursive procedures.  To start with, we will give an example.
      We define a helper called [addX] that adds [delta] to the x variable. *)

  Definition addX (delta : nat) : proc unit :=
    x <- vars.read VarX;
    _ <- vars.write VarX (x + delta);
    Ret tt.

  Theorem addX_ok : forall delta,
    proc_spec (fun (_:unit) state => {|
                   pre := True;
                   post := fun r state' => state' = mkState (delta + StateX state) (StateY state) (StateZ state);
                   recovered := fun _ _ => False;
                   |})
              (addX delta)
              vars.recover
              vars.abstr.
  Proof.
    intros.
    unfold addX.
    step_proc.
    step_proc.
    step_proc.
    replace (StateX state + delta) with (delta + StateX state).
    - reflexivity.
    - lia.
  Qed.

  Hint Resolve addX_ok : core.
  Opaque addX.

  (** Now, we define a procedure [addX_list] that takes a list of [nat]s,
      and calls [addX] on each of them in turn. *)

  Fixpoint addX_list (l : list nat) : proc unit :=
    match l with
    | nil =>
      Ret tt
    | v :: l' =>
      _ <- addX v;
      _ <- addX_list l';
      Ret tt
    end.

  (** To specify what we expect [addX_list] to do, we need to talk about
      the sum of values in a list.  To do that, we define a Gallina function
      (purely in Coq) that computes the sum of values in a list. *)

  Fixpoint list_sum (l : list nat) : nat :=
    match l with
    | nil => 0
    | v :: l' => v + (list_sum l')
    end.

  (** Now we can state a specification about [addX_list] and prove it using
      induction.

      Note: You get an error "Expected a single focused goal but 2 goals are
      focused". For the labs, we turned on an option in Coq that enforces proofs
      use bullets ([+], [-], [*]) or curly braces [{ }] to "focus" each line of
      the proof on a single goal. This makes proof scripts more manageable,
      which will help in later labs.

     If you get this error, make sure to use bullets or braces, the way you saw
     throughout Software Foundations.
   *)

  Theorem addX_list_ok : forall l,
    proc_spec (fun (_:unit) state => {|
                   pre := True;
                   post := fun r state' =>
                             state' = mkState (StateX state + list_sum l) (StateY state) (StateZ state);
                   recovered := fun _ _ => False;
                   |})
              (addX_list l)
              vars.recover
              vars.abstr.
  Proof.
    induction l.
    - (* The base case: adding an empty list. *)
      simpl.

      (* EXERCISE: Finish the proof. *)
      admit.

    - (* The inductive case: adding one more element. *)
      simpl.

      (* We first consider the [addX v] call in the second case of [addX_list]'s match. *)
      step_proc.

      (*  You can see that this is indeed where we are in the proof,
          by observing the [Lexec] marker: it says we're just after
          executing [addX a]. *)
      simpl.

      (*  Now we need to run the rest of [addX_list l].  This works
          out surprisingly easily, because the [induction l] tactic
          gave us an inductive hypothesis, [IHl], that gives us a
          specification for [addX_list l].  [step_proc] will use this
          hypothesis if it matches the invocation. *)
      step_proc.

      (*  Finally, we have to prove the state matches the postcondition
          after running both [addX] and [addX_list l]. *)

      (* EXERCISE: Finish the proof. *)
      admit.
  Admitted.


  (** * Recursive procedures on your own. *)

  (** For the final part, you will work out an example of recursive procedures
      on your own.

      Your job is to implement a procedure [add_odds_evens] that takes a list
      of [nat]s, adds all of the even nats to variable x, and all of the odd
      nats to variable y.

      Implement [add_odds_events] in the recursive [Fixpoint] style
      that we used above in part C, write a spec for it, and prove it.

      Use [Nat.even] and [Nat.odd] to determine if a [nat] value is even
      or odd.  You can use [Search] to locate helpful theorems about
      these, as follows:
    *)

  Search Nat.even.
  Search Nat.odd.

  (* EXERCISE: Fill in your code, spec, and proof here. *)

  Fixpoint add_odds_evens (l : list nat) : proc unit := Ret tt.


  (** To check your solution, prove this simple theorem about
      a particular execution of [add_odds_evens] using your spec.
      Add a [Hint Resolve] statement to let [step_proc] see your
      proven specification about [add_odds_evens]. *)

  Opaque add_odds_evens.

  Theorem add_odds_evens_ok_seems_good :
    proc_spec (fun (_:unit) state => {|
                   pre := state = mkState 0 0 0;
                   post := fun r state' => state' = mkState 6 7 0;
                   recovered := fun _ _ => False;
                   |})
              (add_odds_evens (2 :: 3 :: 3 :: 4 :: 1 :: nil))
              vars.recover
              vars.abstr.
  Proof.
    (* EXERCISE: Prove this specification. *)
  Admitted.

End Exercises.
