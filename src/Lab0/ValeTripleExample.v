
Require Import POCS.
Require Import ThreeVariablesAPI.

Module ValeTripleExample (vars : VarsAPI).

  Definition Move dst src : proc unit :=
    x <- vars.read src;
    vars.write dst x.

  Definition StateUpd var v (s:State) : State :=
    match var with
    | VarX => mkState v (StateY s) (StateZ s)
    | VarY => mkState (StateX s) v (StateZ s)
    | VarZ => mkState (StateX s) (StateY s) v
    end.

  Theorem Move_ok dst src :
    proc_spec
      (fun (_:unit) state =>
         {|
           pre := True;
           post r state' :=
             state' = StateUpd dst (StateVar src state) state;
           recovered _ _ := False
         |})
      (Move dst src)
      vars.recover vars.abstr.
  Proof.
    repeat step_proc.
    destruct dst; intuition.
  Qed.

  Definition Add dst src : proc unit :=
      x <- vars.read dst;
      y <- vars.read src;
      vars.write dst (x + y).

  Definition pow2_64 := Nat.pow 2 64.
  Opaque pow2_64.

  Theorem Add_ok dst src :
    proc_spec
      (fun (_:unit) state =>
         {|
           pre := StateVar src state + StateVar dst state < pow2_64;
           post r state' :=
             state' = StateUpd dst (StateVar dst state + StateVar src state) state;
           recovered _ _ := False
         |})
      (Add dst src)
      vars.recover vars.abstr.
  Proof.
    repeat step_proc.
    destruct dst; intuition.
  Qed.

  Hint Resolve Add_ok : core.
  Hint Resolve Move_ok : core.

  Definition Triple : proc unit :=
    _ <- Move VarY VarX;
    _ <- Add VarX VarY;
    _ <- Add VarY VarX;
    Ret tt.

  Opaque StateUpd StateVar.

  Theorem Triple_ok :
    proc_spec
      (fun (_:unit) state =>
         {|
           pre := StateVar VarX state < 100;
           post r state' :=
             StateVar VarY state' = 3*(StateVar VarX state);
           recovered _ _ := False;
         |})
      Triple
      vars.recover vars.abstr.
  Proof.
    unfold Triple.
    repeat step_proc.
    { admit. }
    { admit. }
    { admit. }
  Abort.

End ValeTripleExample.
