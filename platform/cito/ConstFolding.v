Require Import Optimizer.
Require Import Syntax Semantics.
Require Import SyntaxExpr.

Set Implicit Arguments.

Definition VarToW := string -> option W.

Fixpoint const_folding_expr (e : Expr) (env : VarToW) : Expr :=
  match e with
    | Var var =>
      match env var with
        | Some w => Const w
        | None => e
      end
    | Const w => e
    | Binop op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match a', b' with
        | Const wa,  Const wb => Const (evalBinop op wa wb)
        | _, _ => Binop op a' b'
      end
    | TestE op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match a', b' with
        | Const wa,  Const wb => Const (if evalTest op wa wb then $1 else $0)
        | _, _ => TestE op a' b'
      end
  end.

Definition Vars := list string.

Open Scope type_scope.

(* Info: vars with know value * assigned vars *)
Definition Info := VarToW * Vars.

Definition empty_Vars : Vars := nil.

Variable subtract : VarToW -> Vars -> VarToW.
Infix "-" := subtract.

Variable union : Vars -> Vars -> Vars.
Infix "+" := union.

Variable add : Vars -> string -> Vars.
Infix "%+" := add (at level 60).

Variable VarToW_add : VarToW -> string * W -> VarToW.
Infix "%%+" := VarToW_add (at level 60).

Variable VarToW_del : VarToW -> string -> VarToW.
Infix "%%-" := VarToW_del (at level 60).

Hypothesis sel_remove_eq : forall m x, (m %%- x) x = None.

Hypothesis sel_remove_ne : forall m x x', x <> x' -> (m %%- x) x' = m x'.

Hypothesis sel_add_eq : forall m x w, (m %%+ (x, w)) x = Some w.

Hypothesis sel_add_ne : forall m x w x', x <> x' -> (m %%+ (x, w)) x' = m x'.

Inductive IsZeroResult := 
  | IsZero : IsZeroResult
  | NotAlwaysZero : Expr -> IsZeroResult.

Definition const_folding_expr_is_zero e env : IsZeroResult :=
  match const_folding_expr e env with
    | Const w =>
      if wneb w $0 then
        NotAlwaysZero (Const w)
      else
        IsZero
    | c' => NotAlwaysZero c'
  end.

Fixpoint const_folding (s : Statement) (info : Info) : Statement * Info :=
  match s with
    | Syntax.Skip => (s, info)
    | Syntax.Seq a b => 
      let (a', info') := const_folding a info in
      let (b', info'') := const_folding b info' in
      (Syntax.Seq a' b', info'')
    | Conditional c t f =>
      match const_folding_expr c (fst info) with
        | Const w =>
          if wneb w $0 then
            const_folding t info
          else
            const_folding f info
        | c' =>
          let (t', info_t) := const_folding t (fst info, empty_Vars) in
          let (f', info_f) := const_folding f (fst info, empty_Vars) in
          (* assigned vars in branches will no longer have known values *)
          let vars_with_known_value := fst info - snd info_t - snd info_f in
          let assigned_vars := snd info + snd info_t + snd info_f in
          (Conditional c' t' f', (vars_with_known_value, assigned_vars))
      end
    | Loop c b =>
      match const_folding_expr_is_zero c (fst info) with
        | IsZero =>
            (Syntax.Skip, info)
        | NotAlwaysZero c' =>
          let (b', info_b) := const_folding b (fst info, empty_Vars) in
          (* assigned vars in loop body will no longer have known values *)
          let vars_with_know_value := fst info - snd info_b in
          let assigned_vars := snd info + snd info_b in
          (Loop c' b', (vars_with_know_value, assigned_vars))
      end          
    | Syntax.Assignment var e =>
      let assigned_vars := snd info %+ var in
      match const_folding_expr e (fst info) with
        | Const w =>
          let vars_with_known_value := fst info %%+ (var, w) in
          (Syntax.Assignment var (Const w), (vars_with_known_value, assigned_vars))
        | e' =>
          let vars_with_known_value := fst info %%- var in
          (Syntax.Assignment var e', (vars_with_known_value, assigned_vars))
      end
    | Syntax.ReadAt var arr idx =>
      let arr' := const_folding_expr arr (fst info) in
      let idx' := const_folding_expr idx (fst info) in
      (Syntax.ReadAt var arr' idx', (fst info %%- var, snd info %+ var))
    | Syntax.WriteAt arr idx e =>
      let arr' := const_folding_expr arr (fst info) in
      let idx' := const_folding_expr idx (fst info) in
      let e' := const_folding_expr e (fst info) in
      (Syntax.WriteAt arr' idx' e', info)
    | Syntax.Len var arr =>
      let arr' := const_folding_expr arr (fst info) in
      (Syntax.Len var arr', (fst info %%- var, snd info %+ var))
    | Syntax.Malloc var size =>
      let size' := const_folding_expr size (fst info) in
      (Syntax.Malloc var size', (fst info %%- var, snd info %+ var))
    | Syntax.Free arr =>
      let arr' := const_folding_expr arr (fst info) in
      (Syntax.Free arr', info)
    | Syntax.Call f x =>
      let f' := const_folding_expr f (fst info) in
      let x' := const_folding_expr x (fst info) in
      (Syntax.Call f' x', info)
  end.

Definition agree_with (v : vals) (m : VarToW) :=
  forall x w,
    m x = Some w ->
    sel v x = w.

Definition const_folding_rel vs s vt t := 
  exists info,
    t = fst (const_folding s info) /\
    vt = vs /\
    agree_with vs (fst info).

Require Import GeneralTactics.
Require Import StepsTo.

Hint Unfold const_folding_rel.

Require Import WritingPrograms.
Require Import SemanticsExpr.

Lemma expr_dec : 
  forall e, 
    (exists x, e = Var x) \/
    (exists w, e = Const w) \/
    (exists op a b, e = Binop op a b) \/
    (exists op a b, e = TestE op a b).
Proof.
  destruct e.
  left; eexists; intuition eauto.
  right; left; eexists; intuition eauto.
  right; right; left; do 3 eexists; intuition eauto.
  right; right; right; do 3 eexists; intuition eauto.
Qed.

Lemma agree_with_remove : forall local m x e, agree_with local m -> agree_with (upd local x e) (m %%- x).
  unfold agree_with; intros; destruct (string_dec x x0).
  subst; rewrite sel_remove_eq in *; discriminate.
  rewrite sel_remove_ne in *; eauto; rewrite sel_upd_ne; eauto.
Qed.
Hint Resolve agree_with_remove.

Lemma agree_with_add : forall local m x w, agree_with local m -> agree_with (upd local x w) (m %%+ (x, w)).
  unfold agree_with; intros; destruct (string_dec x x0).
  subst.
  rewrite sel_add_eq in *; eauto; injection H0; intros; subst; rewrite sel_upd_eq in *; eauto.
  rewrite sel_add_ne in *; eauto; rewrite sel_upd_ne; eauto.
Qed.
Hint Resolve agree_with_add.

Definition sel_dec : forall (m : VarToW) x, {w | m x = Some w} + {m x = None}.
  intros; destruct (m x); intuition eauto.
Defined.

Ltac my_f_equal :=
  match goal with
    | |- (if ?E1 then _ else _) = (if ?E2 then _ else _) => replace E2 with E1; try reflexivity
  end.

Lemma const_folding_expr_correct : 
  forall e e' m local, 
    e' = const_folding_expr e m -> 
    agree_with local m -> 
    exprDenote e' local = exprDenote e local.
Proof.
  induction e; try solve [simpl; intuition]; intros.
  simpl in *.
  destruct (sel_dec m s).
  destruct s0.
  subst; rewrite e.
  simpl.
  unfold agree_with in *.
  symmetry.
  eauto.
  subst; rewrite e.
  eauto.

  simpl in *.
  subst.
  eauto.
  
  simpl in *.
  specialize (expr_dec (const_folding_expr e1 m)); intros; openhyp; subst; rewrite H1 in *.

  simpl in *; f_equal.
  replace (local x) with (exprDenote x local); eauto.
  eauto.

  specialize (expr_dec (const_folding_expr e2 m)); intros; openhyp; subst; rewrite H in *; simpl in *; (f_equal; [ replace x with (exprDenote x local); eauto | ]).
  replace (local x0) with (exprDenote x0 local); eauto.
  replace x0 with (exprDenote x0 local); eauto.
  replace (evalBinop _ _ _) with (exprDenote (Binop x0 x1 x2) local); eauto.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x0 x1 x2) local)
  end; eauto.

  simpl in *; f_equal.
  replace (evalBinop _ _ _) with (exprDenote (Binop x x0 x1) local); eauto.
  eauto.

  simpl in *; f_equal.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x x0 x1) local)
  end; eauto.
  eauto.

  simpl in *.
  specialize (expr_dec (const_folding_expr e1 m)); intros; openhyp; subst; rewrite H1 in *.

  simpl in *; my_f_equal; f_equal.
  replace (local x) with (exprDenote x local); eauto.
  eauto.

  specialize (expr_dec (const_folding_expr e2 m)); intros; openhyp; subst; rewrite H in *; simpl in *; (my_f_equal; f_equal; [ replace x with (exprDenote x local); eauto | ]).
  replace (local x0) with (exprDenote x0 local); eauto.
  replace x0 with (exprDenote x0 local); eauto.
  replace (evalBinop _ _ _) with (exprDenote (Binop x0 x1 x2) local); eauto.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x0 x1 x2) local)
  end; eauto.

  simpl in *; my_f_equal; f_equal.
  replace (evalBinop _ _ _) with (exprDenote (Binop x x0 x1) local); eauto.
  eauto.

  simpl in *; my_f_equal; f_equal.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x x0 x1) local)
  end; eauto.
  eauto.
Qed.

Lemma const_folding_expr_correct' : 
  forall e m local, 
    agree_with local m -> 
    exprDenote (const_folding_expr e m) local = exprDenote e local.
  intros; erewrite const_folding_expr_correct; eauto.
Qed.

Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Lemma assign_done : 
  forall x e info local heap local' heap', 
    let s := x <- e in
    let result := const_folding s info in
    Step (fst result) (local, heap) (Done (local', heap')) ->
    agree_with local (fst info) ->
    Step s (local, heap) (Done (local', heap')) /\
    agree_with local' (fst (snd result)).
Proof.
  intros.
  unfold result, s in *; clear result s.
  simpl in *.
  specialize (expr_dec (const_folding_expr e (fst info))); intros; openhyp; rewrite H1 in *; simpl in *; inversion H; unfold_all; subst; split; try erewrite const_folding_expr_correct; eauto.
  erewrite <- const_folding_expr_correct.
  2 : symmetry; eauto.
  simpl.
  eauto.
  eauto.
Qed.

Hint Resolve assign_done.

Lemma break_pair : forall A B (p : A * B), p = (fst p, snd p).
  intros; destruct p; eauto.
Qed.

Lemma const_folding_rel_is_backward_simulation' :
  forall s vt t info,
    t = fst (const_folding s info) ->
    agree_with vt (fst info) ->
    (forall heap vt' heap',
       Step t (vt, heap) (Done (vt', heap')) ->
       Step s (vt, heap) (Done (vt', heap')) /\
       agree_with vt' (fst (snd (const_folding s info)))) /\
    (forall heap f x t' vt' heap',
       Step t (vt, heap) (ToCall f x t' (vt', heap')) ->
       exists s',
         Step s (vt, heap) (ToCall f x s' (vt', heap')) /\
         exists info' : Info,
           t' = fst (const_folding s' info') /\
           agree_with vt' (fst info') /\
           snd (const_folding s info) = snd (const_folding s' info')).
Proof.
  induction s; try solve [simpl; intuition]; intros; subst.

  (* assign *)
  split.

  intros.
  eauto.

  intros.
  simpl in *; specialize (expr_dec (const_folding_expr e (fst info))); intros; openhyp; rewrite H1 in *; simpl in *; inversion H.

  Focus 3.
  (* seq *)
  split.

  intros.
  simpl in *.
  erewrite (break_pair (const_folding s1 info)) in *.
  erewrite (break_pair (const_folding s2 (snd (const_folding s1 info)))) in *.
  simpl in *.
  inversion H; subst.
  destruct v'; simpl in *.
  eapply IHs1 in H3; eauto; openhyp.
  eapply IHs2 in H6; eauto; openhyp.
  intuition eauto.

  intros.
  simpl in *.
  erewrite (break_pair (const_folding s1 info)) in *.
  erewrite (break_pair (const_folding s2 (snd (const_folding s1 info)))) in *.
  simpl in *.
  inversion H; subst.

  destruct v'; simpl in *.
  eapply IHs1 in H3; eauto; openhyp.
  eapply IHs2 in H6; eauto; openhyp; subst.
  eexists; intuition eauto.

  eapply IHs1 in H0; eauto; openhyp.
  eapply H1 in H4; openhyp; subst.
  eexists; intuition eauto.
  eexists; intuition eauto.
  simpl.
  erewrite (break_pair (const_folding x0 x1)) in *.
  erewrite (break_pair (const_folding s2 (snd (const_folding x0 x1)))) in *.
  simpl in *.
  do 3 f_equal.
  eauto.
  simpl.
  erewrite (break_pair (const_folding x0 x1)) in *.
  erewrite (break_pair (const_folding s2 (snd (const_folding x0 x1)))) in *.
  simpl in *.
  do 2 f_equal.
  eauto.

  (* read *)
  split.

  intros.
  simpl in *.
  inversion H; unfold_all; subst.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  intuition.

  intros.
  simpl in *; specialize (expr_dec (const_folding_expr e (fst info))); intros; openhyp; rewrite H1 in *; simpl in *; inversion H.

  (* write *)
  split.

  intros.
  simpl in *.
  inversion H; unfold_all; subst.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  intuition.

  intros.
  simpl in *; specialize (expr_dec (const_folding_expr e (fst info))); intros; openhyp; rewrite H1 in *; simpl in *; inversion H.

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Qed.

Theorem const_folding_rel_is_backward_simulation : is_backward_simulation const_folding_rel.
Proof.
  unfold is_backward_simulation, const_folding_rel.
  intros.
  openhyp; subst.
  eapply const_folding_rel_is_backward_simulation' in H1; eauto.
  openhyp.
  split.
  intros.
  eapply H in H1; openhyp.
  eexists; intuition eauto.
  intros.
  eapply H0 in H1; openhyp.
  do 2 eexists; intuition eauto.
Qed.

Hint Resolve const_folding_rel_is_backward_simulation.

Definition empty_VarToW : VarToW := fun _ => None.

Definition empty_info := (empty_VarToW, empty_Vars).

Definition constant_folding s := fst (const_folding s empty_info).

Lemma everything_agree_with_empty_map : forall v, agree_with v empty_VarToW.
  unfold agree_with, empty_VarToW; intuition.
Qed.
Hint Resolve everything_agree_with_empty_map.

Theorem constant_folding_is_congruence : forall s v, const_folding_rel v s v (constant_folding s).
  unfold const_folding_rel; intros; eexists; intuition eauto.
Qed.

Theorem constant_folding_is_backward_similar_callee : 
  forall s, is_backward_similar_callee (Internal s) (Internal (constant_folding s)).
  intros; econstructor; eauto; eapply constant_folding_is_congruence.
Qed.