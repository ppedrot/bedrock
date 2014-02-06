Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Module Make (Import M : RepInv.RepInv).

  Module Import InvMake := Inv.Make M.
  Module Import CompileStmtSpecMake := CompileStmtSpec.Make M.
  Module Import CompileStmtImplMake := CompileStmtImpl.Make M.
  Require Import CompileStmtTactics.
  Module Import CompileStmtTacticsMake := CompileStmtTactics.Make M.

  Import CompileStmtSpecMake.InvMake.

  Section TopSection.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Require Import Syntax.
    Require Import Wrap.

    Variable rv_postcond : W -> Semantics.State -> Prop.

    Definition compile := compile vars temp_size imports_global modName rv_postcond.

    Require Import Semantics.
    Require Import Safe.
    Require Import Notations.
    Require Import SemanticsFacts.
    Require Import SynReqFacts.
    Require Import ListFacts.
    Require Import StringSet.
    Require Import SetFacts.

    Open Scope stmt.

    Opaque funcs_ok.
    Opaque mult.
    Opaque star. (* necessary to use eapply_cancel *)

    Hint Resolve Subset_syn_req_In.
    Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).
    Hint Resolve map_length.

    Set Printing Coercions.

    Require Import SemanticsExpr.
    Require Import GeneralTactics.
    Require Import VerifCondOkTactics.
    Require Import WordFacts.
    Require Import SynReqFacts2.
    Require Import SynReqFacts3.

    Open Scope nat.

    Lemma verifCond_ok_label : 
      forall x lbl k (pre : assert),
        let s := Syntax.Label x lbl in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (compile s k pre)).
    Proof.

      unfold verifCond, imply.
      wrap0.
      eapply H2 in H.
      unfold precond in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold is_state in *.
      post.
      unfold var_slot in *.
      unfold vars_start in *.
      destruct_state.
      Ltac inversion_Safe :=
        repeat match goal with
                 | H : Safe _ _ _ |- _ => inversion H; clear H; subst
               end.

      inversion_Safe.
      Ltac auto_apply_in t :=
        match goal with
            H : _ |- _ => eapply t in H
        end.

      auto_apply_in ex_up.
      openhyp.
      simpl in *.
      rewrite_natToW_plus.
      assert (List.In x vars) by (eapply syn_req_Label_in; eauto).
      assert (
          evalInstrs stn st
                     (IL.Assign 
                        (LvMem (Imm (Regs st Sp ^+ $8 ^+ $(variablePosition vars x))))
                        (RvImm x2) :: nil) =
          None
        ) ; [ | clear H0 ].
      rewrite <- H0.
      Transparent evalInstrs.
      simpl.
      repeat rewrite wplus_assoc in *.
      Require Import ConvertLabel.
      unfold from_bedrock_label_map in *.
      rewrite H.
      eauto.
      Opaque evalInstrs.
      unfold from_bedrock_label_map in *.
      hiding ltac:(evaluate auto_ext).
    Qed.

    Lemma verifCond_ok_assign : 
      forall x e k (pre : assert),
        let s := Syntax.Assign x e in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (compile s k pre)).
    Proof.

      unfold verifCond, imply.
      wrap0.
      unfold CompileExpr.imply in *.
      unfold CompileExpr.new_pre in *.
      unfold CompileExpr.is_state in *.
      intros.
      eapply H2 in H.
      unfold precond in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold is_state in *.
      post.
      descend.
      repeat hiding ltac:(step auto_ext).
      eauto.
      eapply syn_req_Assign_e; eauto.

      eapply H2 in H3.
      unfold precond in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold CompileExpr.runs_to in *.
      unfold is_state in *.
      unfold CompileExpr.is_state in *.
      post.

      transit.

      destruct_state.
      post.
      unfold var_slot in *.
      unfold vars_start in *.
      rewrite_natToW_plus.
      assert (List.In x vars) by (eapply syn_req_Assign_in; eauto).
      assert (
          evalInstrs stn st
                     (IL.Assign 
                        (LvMem (Imm (Regs st Sp ^+ $8 ^+ $(variablePosition vars x))))
                        Rv :: nil) =
          None
        ) ; [ | clear H0 ].
      rewrite <- H0.
      Transparent evalInstrs.
      simpl.
      repeat rewrite wplus_assoc in *.
      eauto.
      Opaque evalInstrs.
      hiding ltac:(evaluate auto_ext).
    Qed.

  End TopSection.

End Make.