Require Import POCS.
Require Import ThreeVariablesAPI.

Module ThreeVarVC (vars : VarsAPI).

  (* note that we need all the weakest preconditions to also talk about return
  values of type [T], so almost everything will take an extra parameter for the
  return type. *)
  Definition t_wp T := forall (k: T -> State -> Prop), (State -> Prop).

  Definition has_wp T (code: proc T) (wp:t_wp T) :=
    forall (k: T -> State -> Prop),
      proc_spec (fun (_:unit) s0 =>
                   {|
                     pre := wp k s0;
                     post r sM := k r sM;
                     recovered _ _ := False;
                   |})
                code
                vars.recover vars.abstr.

  Class quickCode T (code:proc T) : Type :=
    QProc {
        qc_wp:t_wp T;
        qc_has_wp: has_wp code qc_wp;
      }.

  Arguments qc_wp {T} {code} qc : rename.
  Arguments qc_has_wp {T} {code} qc : rename.

  (* the type of QProc is as given in the paper (just written with different
  syntax) *)
  Check QProc.

  Instance quick_read var : quickCode (vars.read var).
  Proof.
    exists (fun k => (fun s => k (StateVar var s) s)).

    unfold has_wp; intros.
    step_proc.
  Defined.

  Instance quick_write var v : quickCode (vars.write var v).
  Proof.
    exists (fun k => (fun s => k tt (match var with
                          | VarX => mkState v (StateY s) (StateZ s)
                          | VarY => mkState (StateX s) v (StateZ s)
                          | VarZ => mkState (StateX s) (StateY s) v
                          end))).

    unfold has_wp; intros.
    step_proc.
    destruct var; subst; auto.
  Defined.

  Instance quick_ret T (x:T) : quickCode (Ret x).
  Proof.
    exists (fun k => (fun s => k x s)).

    unfold has_wp; intros.
    step_proc.
  Defined.

  Inductive quickCodes : forall T, proc T -> Type :=
  | QRet : quickCodes (Ret tt)
  | QBind : forall T1 (c:proc T1) T2 (cs:T1 -> proc T2),
      quickCode c ->
      (forall x, quickCodes (cs x)) ->
      quickCodes (Bind c cs)
  .

  Fixpoint vc_gen T (cs:proc T) (qcs: quickCodes cs) (k: T -> State -> Prop)
           {struct qcs}
    : State -> Prop.
    destruct qcs as [| T1 c T2 cs qc f_qcs]; intro s0.
    - exact (k tt s0).
    - refine (qc_wp qc _ s0).
      (* this is vc_gen_Bind cs.tl f_qcs k *)
      intros x s1.
      refine (vc_gen _ (cs x) (f_qcs x) k s1).
  Defined.

  Arguments vc_gen {T} cs qcs k.

  Theorem vc_sound T (cs:proc T) (qcs: quickCodes cs) : has_wp cs (vc_gen cs qcs).
  Proof.
    induction qcs; simpl.
    - unfold has_wp; step_proc.
    - unfold has_wp in *; intros.
      pose proof (qc_has_wp q (fun x s1 => vc_gen (cs x) (q0 x) k s1)).
      step_proc.
  Qed.

  Arguments QBind {T1 c T2 cs}.

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
    spec_intros.
    rename state0 into state.

    pose proof
         (vc_sound (cs:=addX delta)
                   (QBind (quick_read VarX)
                          (fun x => QBind (quick_write VarX (x + delta))
                                       (fun _ => QRet)))
                   (fun r state' =>
                      state' =
                      mkState (delta + StateX state) (StateY state) (StateZ state))).
    simpl in H0.

    step_proc.
    f_equal.
    lia.
  Qed.

End ThreeVarVC.
