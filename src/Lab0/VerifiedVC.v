(*** Vale's VC generator for POCS ***)

Require Import POCS.
Require Import ThreeVariablesAPI.

Unset Implicit Arguments.

Module ThreeVarVC (vars : VarsAPI).

  (* begin hide *)
  Implicit Types (s:State).
  (* end hide *)

(******************************************************************************)

  (*** Defining quickCode ***)


  (* note that we need all the weakest preconditions to also talk about return
  values of type [T], so almost everything will take an extra parameter for the
  return type. *)
  Definition t_wp T := forall (k: T -> State -> Prop), (State -> Prop).

  (* this is the core of weakest preconditions: wp k is a precondition that
     guarantees the postcondition k

     the "weakest" in weakest preconditions means [wp k] is supposed to be the
     minimal condition necessary to guarantee k, but we don't prove that (as is
     common) *)
  Definition has_wp {T} (code: proc T) (wp:t_wp T) :=
    forall (k: T -> State -> Prop),
      proc_spec (fun (_:unit) s0 =>
                   {|
                     pre := wp k s0;
                     post r sM := k r sM;
                     recovered _ _ := False;
                   |})
                code
                vars.recover vars.abstr.

  Class quickCode {T} (code:proc T) : Type :=
    QProc {
        (* a quickCode has a _predicate transformer_ function wp that
        produces a weakest precondition for a given postcondition *)
        wp: t_wp T;
        (* ...and this wp is proven correct *)
        hasWp: has_wp code wp;
      }.

  (* begin hide *)
  Arguments QProc {T code} wp hasWp.
  Arguments wp {T} {code} qc : rename.
  Arguments hasWp {T} {code} qc : rename.
  (* end hide *)

  (******************************************************************************)

 (*+ Examples of quickCode +*)

  (* the type of QProc is as given in the paper (just written with different
  syntax) *)
  About QProc.

  Instance quick_read var : quickCode (vars.read var).
  Proof.
    refine {|
        wp := fun k => (fun s => k (StateVar var s) s)
      |}.

    unfold has_wp; intros.
    step_proc.
  Defined.

  Instance quick_write var v : quickCode (vars.write var v).
  Proof.
    refine {|
        wp := fun k => (fun s => k tt (match var with
                                 | VarX => mkState v (StateY s) (StateZ s)
                                 | VarY => mkState (StateX s) v (StateZ s)
                                 | VarZ => mkState (StateX s) (StateY s) v
                                 end))
      |}.

    unfold has_wp; intros.
    step_proc.
    destruct var; subst; auto.
  Defined.

  Instance quick_ret T (x:T) : quickCode (Ret x).
  Proof.
    refine {|
      wp :=
        fun k => (fun s => k x s)
      |}.

    unfold has_wp; intros.
    step_proc.
  Defined.

  (*+ Packaging quickCodes for a procedure +*)

  (* The paper first defines a version of [quickCodes] for a list of
     instructions. *)

  (* Our only notion of code is [proc T], where commands are sequenced with
     functions rather than being a plain list (the plain list makes more sense
     for assembly, where there's no notion of "returning" a value)

     For that reason we immediately jump to the "shallow embedding" version in
     the paper that supports ghost state; we don't thread ghost state
     but return values. *)
  Inductive quickCodes : forall {T:Type}, proc T -> Type :=
  | QRet : quickCodes (Ret tt)
  | QBind : forall T1 (c:proc T1) T2 (cs:T1 -> proc T2),
      forall (qc:quickCode c)
        (f_qcs:forall x, quickCodes (cs x)),
        quickCodes (Bind c cs)
  .

  (******************************************************************************)

  (*** Writing the VC generator ***)

  (* So now we have a representation of programs along with weakest
     preconditions for the basic components. *)

  (* vc_gen is the crux of this approach: it sequences weakest preconditions
  together from [quickCode] instances to build up all the verification
  conditions for a whole procedure. *)
  Fixpoint vc_gen {T} (cs:proc T) (qcs: quickCodes cs) (k: T -> State -> Prop)
           {struct qcs}
    : State -> Prop.
    (* I had a hard time writing this function so I switched to proof mode. *)
    destruct qcs as [| T1 c T2 cs qc f_qcs]; intro s0.
    - exact (k tt s0).
    - (* the paper defines an intermediate function; rather than do that, we can
      just put an _ in Coq and then fill it in as a goal later. *)
      refine (qc.(wp) _ s0).
      (* the whole is vc_gen_Bind cs.tl f_qcs k from the paper *)
      intros x s1.
      refine (vc_gen _ (cs x) (f_qcs x) k s1).
  Defined.

  Theorem vc_sound {T} (cs:proc T) {qcs: quickCodes cs} : has_wp cs (vc_gen cs qcs).
  Proof.
    induction qcs; simpl.
    - unfold has_wp; step_proc.
    - unfold has_wp in *; intros.
      (* I started from the paper, but the answer is actually in the goal;
      alternately, we can rely on Coq to guess the right postcondition for the
      first procedure *)
      (* eapply proc_spec_rx; [ eapply (qc_has_wp q) | ]; simplify; eauto. *)
      pose proof (qc.(hasWp) (fun x s1 => vc_gen (cs x) (f_qcs x) k s1)).
      step_proc.
  Qed.

  (*** Applying the VC generator ***)

  Definition addX (d : nat) : proc unit :=
    x <- vars.read VarX;
      _ <- vars.write VarX (x + d);
      Ret tt.

  (* we need a quickCodes version of addX to teach the vc generator the
  structure of the procedure as well as the wp's for all the primitives; here's
  some magic so Coq will do that for us *)
  (* begin hide *)
  Existing Class quickCodes.
  Existing Instance QRet.
  Existing Instance QBind.
  Arguments QBind {T1 c T2 cs}.
  (* end hide *)

  Definition quick_addX d : quickCodes (addX d) := _.

  Theorem quick_addX_is : forall d,
      quick_addX d =
      QBind (quick_read VarX)
            (fun x => QBind (quick_write VarX (x + d))
                         (fun _ => QRet)).
  Proof.
    reflexivity.
  Qed.

  Theorem addX_ok : forall d,
      proc_spec (fun (_:unit) state => {|
                     pre := True;
                     post := fun r state' => state' = mkState (d + StateX state) (StateY state) (StateZ state);
                     recovered := fun _ _ => False;
                   |})
                (addX d)
                vars.recover
                vars.abstr.
  Proof.
    intros.
    spec_intros.
    rename state0 into state.

    pose proof
         (vc_sound (addX d))
         (fun r state' =>
            state' =
            mkState (d + StateX state) (StateY state) (StateZ state)).

    (* if that's tedious, we could instead get its parts from the goal: *)
    match goal with
    | [ |- proc_spec
            (fun _ state0 =>
               {| post := @?k0 state0 |})
            ?code
            _ _ ] =>
      let k := constr:(k0 state) in
      let H := fresh in
      pose proof (vc_sound code k) as H;
        simpl in H
    end.

    step_proc.
    f_equal.
    lia.
  Qed.

End ThreeVarVC.
