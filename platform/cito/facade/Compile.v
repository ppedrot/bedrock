Set Implicit Arguments.

Require Import Memory IL.
Require Import Facade.
Require Syntax.
Require Import String.
Open Scope string.
Require Import SyntaxExpr.
Require Import StringMap.
Import StringMap.
Require Import GLabel.
Require Import StringMapFacts.
Import FMapNotations.
Open Scope fmap.

Coercion Var : string >-> Expr.

Fixpoint compile (s : Stmt) : Syntax.Stmt :=
  match s with
    | Skip => Syntax.Skip
    | Seq a b => Syntax.Seq (compile a) (compile b)
    | If e t f => Syntax.If e (compile t) (compile f)
    | While e c => Syntax.While e (compile c)
    | Assign x e => Syntax.Assign x e
    | Label x lbl => Syntax.Label x lbl
    | Call x f args => Syntax.Call (Some x) f (List.map Var args)
  end.

Require Import ADT.

Module Make (Import A : ADT).

  Require Semantics.
  Module Cito := Semantics.Make A.

  Definition RunsTo := @RunsTo ADTValue.
  Definition State := @State ADTValue.
  Definition Env := @Env ADTValue.
  Definition AxiomaticSpec := @AxiomaticSpec ADTValue.
  Definition Value := @Value ADTValue.
  Definition Sca := @SCA ADTValue.
  Definition Adt := @ADT ADTValue.

  Definition represent p (o : option ADTValue) v :=
    match v with
      | SCA w => p = w
      | ADT a => o = Some a
    end.

  Require Import WordMap.

  Definition related (s_st : State) (t_st : Cito.State) := 
    (forall x v, 
       find x s_st = Some v -> let p := Locals.sel (fst t_st) x in represent p (WordMap.find p (snd t_st)) v) /\
    (forall p a,
       WordMap.find p (snd t_st) = Some a ->
       exists! x,
         Locals.sel (fst t_st)  x = p /\
         find x s_st = Some (ADT a)).
                
  Definition CitoEnv := ((glabel -> option W) * (W -> option Cito.Callee))%type.

  Coercion Semantics.Fun : Semantics.InternalFuncSpec >-> FuncCore.FuncCore.

  Definition CitoIn_FacadeIn (argin : Cito.ArgIn) : Value :=
    match argin with
      | inl w => SCA _ w
      | inr a => ADT a
    end.

  Definition CitoInOut_FacadeInOut (in_out : Cito.ArgIn * Cito.ArgOut) : Value * option Value :=
    match fst in_out, snd in_out with
      | inl w, _ => (SCA _ w, Some (SCA _ w))
      | inr a, Some a' => (ADT a, Some (ADT a'))
      | inr a, None => (ADT a, None)
    end.

  Definition compile_ax (spec : AxiomaticSpec) : Cito.Callee :=
    Semantics.Foreign 
      {|
        Semantics.PreCond args := PreCond spec (List.map CitoIn_FacadeIn args) ;
        Semantics.PostCond pairs ret := PostCond spec (List.map CitoInOut_FacadeInOut pairs) (CitoIn_FacadeIn ret)
      |}.

  Definition compile_op (spec : OperationalSpec) : Cito.Callee.
    refine
      (Cito.Internal
         {|
           Semantics.Fun :=
             {|
               FuncCore.ArgVars := ArgVars spec;
               FuncCore.RetVar := RetVar spec;
               FuncCore.Body := compile (Body spec)
             |};
           Semantics.NoDupArgVars := _
         |}
      ).
    simpl.
    destruct spec.
    simpl.
    inversion NoDupArgVars.
    eauto.
  Defined.

  Definition FuncSpec := @FuncSpec ADTValue.

  Definition compile_spec (spec : FuncSpec) : Cito.Callee :=
    match spec with
      | Axiomatic s => compile_ax s
      | Operational s => compile_op s
    end.

  Definition compile_env (env : Env) : CitoEnv :=
    (Label2Word env, 
     fun w => option_map compile_spec (Word2Spec env w)).
    
  Require Import GeneralTactics.
  Require Import GeneralTactics3.

  Ltac inject h := injection h; intros; subst; clear h.

  Notation ceval := SemanticsExpr.eval.
  Notation cRunsTo := Semantics.RunsTo.
  Lemma is_true_is_false : forall (st : State) e, is_true st e -> is_false st e -> False.
  Proof.
    intros.
    unfold is_true, is_false in *.
    rewrite H in *; discriminate.
  Qed.
  Lemma safe_if_true : forall (env : Env) e t f st, Safe env (If e t f) st -> is_true st e -> Safe env t st.
  Proof.
    intros.
    inversion H; subst.
    eauto.
    exfalso; eapply is_true_is_false; eauto.
  Qed.
  Definition is_bool (st : State) e := eval_bool st e <> None.
  Definition value_dec (v : Value) : {w | v = SCA _ w} + {a | v = ADT a}.
    destruct v.
    left; exists w; eauto.
    right; exists a; eauto.
  Defined.
  Definition option_value_dec (v : option Value) : {w | v = Some (SCA _ w)} + {a | v = Some (ADT a)} + {v = None}.
    destruct (option_dec v).
    destruct s; subst.
    destruct (value_dec  x).
    destruct s; subst.
    left; left; eexists; eauto.
    destruct s; subst.
    left; right; eexists; eauto.
    subst.
    right; eauto.
  Qed.
  Lemma eval_ceval : forall s_st vs h e w, eval s_st e = Some (SCA _ w) -> related s_st (vs, h) -> ceval vs e = w.
  Proof.
    induction e; simpl; intuition.
    unfold related in *.
    openhyp.
    eapply H0 in H.
    eauto.

    unfold eval_binop_m in *.
    destruct (option_value_dec (eval s_st e1)).
    destruct s.
    destruct s.
    rewrite e in *.
    destruct (option_value_dec (eval s_st e2)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    erewrite IHe1; [ | eauto .. ].
    erewrite IHe2; [ | eauto .. ].
    eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
    destruct s.
    rewrite e in *; discriminate.
    rewrite e in *; discriminate.
    
    unfold eval_binop_m in *.
    destruct (option_value_dec (eval s_st e1)).
    destruct s.
    destruct s.
    rewrite e in *.
    destruct (option_value_dec (eval s_st e2)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    erewrite IHe1; [ | eauto .. ].
    erewrite IHe2; [ | eauto .. ].
    eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
    destruct s.
    rewrite e in *; discriminate.
    rewrite e in *; discriminate.
  Qed.
  Lemma eval_bool_wneb : forall (s_st : State) vs h e b, eval_bool s_st e = Some b -> related s_st (vs, h) -> wneb (ceval vs e) $0 = b.
  Proof.
    intros.
    unfold eval_bool in *.
    destruct (option_value_dec (eval s_st e)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    eapply eval_ceval in e0; [ | eauto].
    rewrite e0 in *; eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
  Qed.
  Notation boolcase := Sumbool.sumbool_of_bool.
  Lemma wneb_is_true : forall s_st vs h e, wneb (ceval vs e) $0 = true -> related s_st (vs, h) -> is_bool s_st e -> is_true s_st e.
  Proof.
    intros.
    unfold is_true.
    unfold is_bool in *.
    eapply ex_up in H1.
    openhyp.
    destruct (boolcase x); subst.
    eauto.
    eapply eval_bool_wneb in H1; eauto.
    set (ceval _ _) in *.
    rewrite H in *; discriminate.
  Qed.
  Lemma is_true_is_bool : forall st e, is_true st e -> is_bool st e.
  Proof.
    intros.
    unfold is_true, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.
  Lemma is_false_is_bool : forall st e, is_false st e -> is_bool st e.
  Proof.
    intros.
    unfold is_false, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.
  Lemma safe_if_is_bool : forall (env : Env) e t f st, Safe env (If e t f) st -> is_bool st e.
  Proof.
    intros.
    inversion H; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.
  Lemma safe_if_false : forall (env : Env) e t f st, Safe env (If e t f) st -> is_false st e -> Safe env f st.
  Proof.
    intros.
    inversion H; subst.
    exfalso; eapply is_true_is_false; eauto.
    eauto.
  Qed.
  Lemma wneb_is_false : forall s_st vs h e, wneb (ceval vs e) $0 = false -> related s_st (vs, h) -> is_bool s_st e -> is_false s_st e.
  Proof.
    intros.
    unfold is_false.
    unfold is_bool in *.
    eapply ex_up in H1.
    openhyp.
    destruct (boolcase x); subst.
    eapply eval_bool_wneb in H1; eauto.
    set (ceval _ _) in *.
    rewrite H in *; discriminate.
    eauto.
  Qed.

  Require Import StringSet.

  Require Import WordMapFacts.
  Import FMapNotations.
  Open Scope fmap.
  Require Import WordMap.
  Import WordMap.

  Definition Submap {elt} m1 m2 := forall {k v}, @find elt k m1 = Some v -> find k m2 = Some v.
  Infix "<=" := Submap.

(*

  s_st ------- s_env, s --------> exists s_st'
 (Safe)
   ||             |                  ||          
   ||          compile               ||
   ||             |                  ||
   ||             v                  ||

  t_st ------ t_env, t -------->    t_st' 

*)

  Theorem compile_runsto : 
    forall t t_env t_st t_st', 
      Cito.RunsTo t_env t t_st t_st' -> 
      forall s, 
        t = compile s -> 
        (* h1 : the heap portion that this program is allowed to change *)
        forall h1, 
          h1 <= snd t_st -> 
          forall s_st, 
            related s_st (fst t_st, h1) -> 
            forall s_env, 
              t_env = compile_env s_env -> 
              Safe s_env s s_st -> 
              exists s_st', 
                RunsTo s_env s s_st s_st' /\ 
                (* h2 : the frame heap (the outside portion that won't be touched by this program *)
                let h2 := snd t_st - h1 in 
                (* the frame heap will be intacked in the final state *)
                h2 <= snd t_st' /\ 
                (* variables not appearing as LHS won't change value in Cito state *)
                (forall x, ~ StringSet.In x (assigned s) -> Locals.sel (fst t_st) x = Locals.sel (fst t_st') x) /\
                (* newly allocated ADT objects during this program's execution won't collide with the frame heap *)
                (forall x a, ~ StringMap.In x s_st -> StringMap.find x s_st' = Some (ADT a) -> ~ WordMap.In (Locals.sel (fst t_st') x) h2) /\
                (* main result: final source-level and target level states are related *)
                related s_st' (fst t_st', snd t_st' - h2).
  Proof.
    induction 1; simpl; intros; destruct s; simpl in *; intros; try discriminate.

    Focus 7.
    (* call-operational *)
    unfold_all.
    inject H2.
    destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))); simpl in *.
    2 : rewrite e0 in *; simpl in *; discriminate.
    destruct s0.
    rewrite e0 in *; simpl in *.
    inject H.
    destruct x; simpl in *.
    destruct a; simpl in *; unfold compile_ax in *; simpl in *; discriminate.
    unfold compile_op in *; simpl in *.
    inject H2; simpl in *.
    inversion H6; subst.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
    rewrite e0 in *.
    discriminate.
    
    unfold_all.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
    rewrite e0 in *.
    inject H9.

    edestruct IHRunsTo; [ .. | clear IHRunsTo].
    eauto.
    2 : eauto.
    3 : eauto.
    3 : eauto.
    3 : eauto.
    Focus 3.
    openhyp.
    Ltac copy h := generalize h; intro.
    copy H; eapply H16 in H.
    openhyp.
    eapply ex_up in H.
    openhyp.
    eexists.
    split.
    eapply RunsToCallOp.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    reflexivity.
    Unfocus.
    Require Import List.
    Fixpoint reachable_heap vs argvars (input : list Value) := 
      match argvars, input with
        | k :: ks, i :: is =>
          let h := reachable_heap vs ks is in
          match i with
            | SCA _ => h 
            | ADT a => WordMap.add (Locals.sel vs k) a h
          end
        | _, _ => WordMap.empty _
      end.

    instantiate (1 := reachable_heap (fst v) l input).
    Lemma reachable_submap_related : forall st args input vs h, mapM (sel st) args = Some input -> related st (vs, h) -> reachable_heap vs args input <= h /\ related (make_state args input) (vs, reachable_heap vs args input).
      admit.
    Qed.
    eapply reachable_submap_related in H4; openhyp; eauto.
    Lemma submap_trans : forall elt (a b c : WordMap.t elt), a <= b -> b <= c -> a <= c.
      admit.
    Qed.
    eapply submap_trans; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.
    Lemma change_var_names : forall vs1 vs2 h vars1 vars2 input, related (make_state vars1 input) (vs1, h) -> (map (Locals.sel vs2) vars2 = map (fun x => vs1 x) vars1) -> related (make_state vars2 input) (vs2, h).
      admit.
    Qed.
    eapply change_var_names; eauto.
    rewrite map_map in H0; simpl in *; eauto.
    Ltac split' name :=
      match goal with
        | |- ?T /\ _ => assert (name: T); [ | split; [ auto | ] ]
      end.

    split' Hsm.
    eapply submap_trans; eauto.
    Lemma submap_diff : forall elt (a b c : WordMap.t elt), c <= b -> b <= a -> a - b <= a - c.
      admit.
    Qed.
    eapply submap_diff; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.

    split.
    intros.
    Require Import GeneralTactics2.
    Lemma singleton_iff_not : forall e e', ~ StringSet.In e' (StringSet.singleton e) <-> e <> e'.
      split; intros; not_not; eapply StringSetFacts.singleton_iff; eauto.
    Qed.
    eapply singleton_iff_not in H19.
    rewrite Locals.sel_upd_ne by eauto.
    eauto.

    Import WordMap.

    split.
    intros.
    destruct (string_dec x1 s).
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject H20.
    rewrite Locals.sel_upd_eq by eauto.
    Lemma submap_in : forall elt h1 h2, h1 <= h2 -> forall k, @In elt k h1 -> In k h2.
      admit.
    Qed.
    Lemma submap_not_in : forall elt h1 h2, h1 <= h2 -> forall k, ~ @In elt k h2 -> ~ In k h1.
      intros; not_not; eapply submap_in; eauto.
    Qed.
    eapply submap_not_in.
    2 : eapply H9.
    eapply submap_diff; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.
    Lemma make_state_not_in : forall k ks (vs : list Value), ~ List.In k ks -> ~ StringMap.In k (make_state ks vs).
      admit.
    Qed.
    eapply make_state_not_in.
    Require Import ListFacts1 ListFacts2 ListFacts3 ListFactsNew.
    Import WordMapFacts.
    Lemma NoDup_not_in : forall A (x : A) xs, NoDup (x :: xs) -> ~ List.In x xs.
      inversion 1; subst; eauto.
    Qed.
    eapply NoDup_not_in.
    destruct spec; eauto.
    eauto.

    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne by eauto.
    nintro; eapply H19; clear H19.
    Definition not_reachable key (k : key) ks ins := ~ List.In k ks \/ exists i w, nth_error ks i = Some k /\ nth_error ins i = Some (Sca w).

    Lemma find_Some_add_remove_many : 
      forall k ks ins outs h v, 
        NoDup ks -> 
        length ks = length ins -> 
        length ks = length outs -> 
        (StringMap.find k (add_remove_many ks ins outs h) = Some v <-> 
         ((not_reachable k ks ins /\ StringMap.find k h = Some v) \/ 
          exists i a, 
            nth_error ks i = Some k /\ 
            nth_error ins i = Some (ADT a) /\ 
            nth_error outs i = Some (Some v))).
      admit.
    Qed.
    Lemma In_add_remove_many : 
      forall k ks (ins : list Value) outs h, 
        NoDup ks -> 
        mapM (sel h) ks = Some ins ->
        StringMap.In k (add_remove_many ks ins outs h) -> 
        StringMap.In k h.
      admit.
    Qed.
    eapply In_add_remove_many; eauto.
    eapply StringMapFacts.MapsTo_In.
    eapply StringMapFacts.find_mapsto_iff.
    eauto.
    
    copy H4; eapply reachable_submap_related in H4; openhyp; eauto.
    destruct v as [vs h]; simpl in *.
    set (h2 := h - h1) in *.
    unfold related; simpl.
    split.

    (* related (1) *)
    intros k v Hf.

    eapply StringMapFacts.find_mapsto_iff in Hf.
    eapply StringMapFacts.add_mapsto_iff in Hf; openhyp.
    subst.
    rewrite Locals.sel_upd_eq by eauto.
    unfold related in H14; simpl in H14; openhyp.
    eapply H14 in H.
    set (h23 := h - reachable_heap vs l input) in *.
    set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
    Lemma submap_represent : forall p h1 h2 v, represent p (WordMap.find p h1) v -> h1 <= h2 -> represent p (WordMap.find p h2) v.
      admit.
    Qed.
    eapply submap_represent.
    eauto.
    eapply submap_diff; eauto.
    eapply submap_diff; eauto.

    rewrite Locals.sel_upd_ne by eauto.
    eapply StringMapFacts.find_mapsto_iff in H22.
    eapply find_Some_add_remove_many in H22.
    openhyp.
    copy H19; unfold related in H19; simpl in H19; openhyp.
    eapply H19 in H23.
    Lemma not_in_find_submap : forall elt h1 h2 k, h2 <= h1 -> ~@WordMap.In elt k h2 -> WordMap.find k h1 = WordMap.find k (h1 - h2).
      admit.
    Qed.
    erewrite not_in_find_submap in H23.
    Focus 3.
    Lemma not_reachable_iff : forall k ks st vs h input, related st (vs, h) -> mapM (sel st) ks = Some input -> (not_reachable k ks input <-> ~ WordMap.In (Locals.sel vs k) (reachable_heap vs ks input)).
      admit.
    Qed.
    eapply not_reachable_iff; eauto.
    2 : eauto.
    eapply submap_represent.
    eauto.
    Lemma submap_diff_diff : forall elt (h1 h2 h3 : WordMap.t elt), h1 <= h2 -> h2 <= h3 -> h2 - h1 == (h3 - h1) - (h3 - h2).
      admit.
    Qed.
    Require Import Setoid.
    Global Add Parametric Morphism elt : (@Submap elt)
        with signature Equal ==> Equal ==> iff as Submap_m.
      admit.
    Qed.
    erewrite submap_diff_diff; eauto.
    Lemma submap_restrict : forall elt (h1 h2 h : WordMap.t elt), h1 <= h2 -> h1 - h <= h2 - h.
      admit.
    Qed.
    eapply submap_restrict.
    eauto.

    rewrite map_map in H0; simpl in *.
    Lemma map_eq : forall A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) ls1 ls2 i a1, List.map f1 ls1 = List.map f2 ls2 -> nth_error ls1 i = Some a1 -> exists a2, nth_error ls2 i = Some a2 /\ f1 a1 = f2 a2.
      admit.
    Qed.
    symmetry in H0.
    eapply map_eq in H0; [ | eauto ..].
    openhyp.
    unfold Locals.sel in *.
    rewrite H25.
    rewrite H5.
    Focus 2.
    Lemma disjoint_in_not : forall s1 s2 x, disjoint s1 s2 -> StringSet.In x s2 -> ~ StringSet.In x s1.
      admit.
    Qed.
    eapply disjoint_in_not; eauto.
    eapply StringSetFacts.of_list_1.
    eapply SetoidListFacts.In_InA.
    eapply Locals.nth_error_In; eauto.
    rename x1 into i.
    rename l into args.
    erewrite map_nth_error in H24 by eauto.
    inject H24.
    copy H14; unfold related in H14; simpl in H14; eapply H14 in H26.
    unfold Locals.sel in *.
    set (h23 := h - reachable_heap vs args input) in *.
    set (p := vs_callee' x3) in *.
    eapply submap_represent.
    eauto.
    eapply submap_diff; eauto.
    eapply submap_diff; eauto.

    eauto.

    Lemma mapM_length : forall A B (f : A -> option B) ls1 ls2, mapM f ls1 = Some ls2 -> length ls1 = length ls2.
      admit.
    Qed.
    eapply mapM_length; eauto.
    rewrite map_length.
    rewrite map_map in H0.
    eapply map_eq_length_eq in H0.
    eauto.

    (* related (2) *)
    intros.
    rename s into lhs.
    rename l into args.
    rename h into h123.
    rename h1 into h23.
    rename h2 into h1.
    set (h3 := reachable_heap vs args input) in *.
    set (h12 := h123 - h3) in *.
    set (h2 := h12 - h1) in *.
    set (h3' := heap' - h12) in *.
    set (h23' := heap' - h1) in *.
    Notation direct_sum h1 h2 h12 := (h1 <= h12 /\ h2 <= h12 /\ Disjoint h1 h2).
    Notation "h1 * h2 === h12" := (direct_sum h1 h2 h12) (at level 100).
    assert (direct_sum h1 h2 h12) by admit.
    assert (direct_sum h2 h3 h23) by admit.
    assert (direct_sum h1 h23 h123) by admit.
    assert (direct_sum h12 h3 h123) by admit.
    assert (direct_sum h2 h3' h23') by admit.

    Lemma find_Some_direct_sum : forall elt h1 h2 h12, direct_sum h1 h2 h12 -> forall k (v : elt), find k h12 = Some v <-> find k h1 = Some v \/ find k h2 = Some v.
      admit.
    Qed.

    eapply find_Some_direct_sum in H21; eauto; openhyp.

    copy H19; unfold related in H19; simpl in H19; openhyp.
    specialize (H38 _ _ (H23 _ _ H21)).
    destruct H38.
    destruct H38.
    openhyp.
    rename x1 into x2.
    destruct (string_dec x2 lhs).
    subst.
    contradict H12; eexists; eauto.
    exists x2.
    split.
    split.
    rewrite Locals.sel_upd_ne by eauto; eauto.
    rewrite StringMapFacts.add_neq_o by eauto.
    eapply find_Some_add_remove_many.
    eauto.
    eapply mapM_length; eauto.
    rewrite map_length.
    rewrite map_map in H0.
    eapply map_eq_length_eq in H0.
    eauto.
    left.
    split.
    eapply not_reachable_iff; eauto.
    Lemma Disjoint_in_not : forall elt h1 h2 x, @Disjoint elt h1 h2 -> In x h1 -> ~ In x h2.
      admit.
    Qed.
    eapply (Disjoint_in_not H34).
    rewrite H38.
    Lemma find_Some_in : forall elt k m (v : elt), find k m = Some v -> In k m.
      intros; eapply MapsTo_In; eapply find_mapsto_iff; eauto.
    Qed.
    eapply find_Some_in; eauto.
    eauto.

    intros.
    openhyp.
    destruct (string_dec x' lhs).
    subst.
    rewrite StringMapFacts.add_eq_o in *.
    rewrite Locals.sel_upd_eq in * by eauto.
    inject H42.
    eapply H9 in H.
    contradict H.
    rewrite H41.
    eapply submap_in; eauto.
    eapply find_Some_in; eauto.
    eapply make_state_not_in.
    eapply NoDup_not_in.
    destruct spec; eauto.
    eauto.

    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne in * by eauto.
    eapply H39.
    split.
    eauto.
    Lemma find_Some_add_remove_many_not_reachable : 
      forall k ks ins outs h v, 
        NoDup ks -> 
        length ks = length ins -> 
        length ks = length outs -> 
        StringMap.find k (add_remove_many ks ins outs h) = Some v -> 
        not_reachable k ks ins -> 
        StringMap.find k h = Some v.
      admit.
    Qed.
    eapply find_Some_add_remove_many_not_reachable in H42.
    eauto.
    eauto.
    eapply mapM_length; eauto.
    rewrite map_length.
    rewrite map_map in H0.
    eapply map_eq_length_eq in H0; eauto.
    eapply not_reachable_iff; eauto.
    eapply (Disjoint_in_not H34).
    rewrite H41.
    eapply find_Some_in; eauto.

    
    (* p is in h3' *)

    (*here*)
    admit.

(*
      Lemma make_state_Some : forall k (v : Value) ks vs, StringMap.find k (make_state ks vs) = Some v -> exists i, nth_error ks i = Some k /\ nth_error vs i = Some v.
        admit.
      Qed.
      eapply make_state_Some in H.
      openhyp.
      Lemma mapM_Some : forall A B (f : A -> option B) ls1 ls2 i a2, mapM f ls1 = Some ls2 -> nth_error ls2 i = Some a2 -> exists a1, nth_error ls1 i = Some a1 /\ f a1 = Some a2.
        admit.
      Qed.
      eapply mapM_Some in H2; [ | eauto].
      openhyp.
      unfold related in H4.
      openhyp.
      eapply H4 in H3.
      rewrite map_map in H0; simpl in *.
      Lemma map_eq : forall A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) ls1 ls2 i a1 a2, map f1 ls1 = map f2 ls2 -> nth_error ls1 i = Some a1 -> nth_error ls2 i = Some a2 -> f1 a1 = f2 a2.
        admit.
      Qed.
      eapply map_eq in H0; [ | eauto ..].
      rewrite H0 in *.
      eauto.

      intros.
      unfold related in H4.
      openhyp.
      eapply H3 in H.
      openhyp.

      Definition get_ret (st : Cito.State) x : Value :=
        let w := fst st x in
        match Cito.heap_sel (snd st) w with
          | Some a => ADT a
          | None => SCA _ w
        end.
      instantiate (1 := get_ret (vs_callee', heap') (RetVar spec)).
      admit.


      admit.
      admit.
*)

    Focus 7.
    (* call-axiomatic *)
    unfold_all.
    injection H6; intros; subst; clear H6.
    simpl in *.
    destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))).
    destruct s0.
    rewrite e0 in *; simpl in *.
    injection H; intros; subst; clear H.
    destruct x; simpl in *.
    destruct a; simpl in *.
    unfold compile_ax in *; simpl in *.
    injection H6; intros; subst; simpl in *; clear H6.
    (* eexists. *)
    (* split. *)
    (* eapply RunsToCallAx. *)
    admit.

    discriminate.
    
    rewrite e0 in *; simpl in *; discriminate.

    (* skip *)
    eexists; split.
    eapply RunsToSkip.
    eauto.

    (* seq *)
    subst.
    inject H1.
    edestruct IHRunsTo1; clear IHRunsTo1; eauto.
    Lemma safe_seq_1 : forall (env : Env) a b st, Safe env (Seq a b) st -> Safe env a st.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.
    eapply safe_seq_1; eauto.
    openhyp.
    edestruct IHRunsTo2; clear IHRunsTo2; eauto.
    Lemma safe_seq_2 : forall (env : Env) a b st, Safe env (Seq a b) st -> forall st', RunsTo env a st st' -> Safe env b st'.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.
    eapply safe_seq_2; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToSeq; eauto.
    eauto.

    (* if-true *)
    injection H1; intros; subst; clear H1.
    edestruct IHRunsTo.
    eauto.
    eauto.
    eauto.
    eapply safe_if_true; eauto.
    eapply wneb_is_true; eauto.
    eapply safe_if_is_bool; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToIfTrue.
    eapply wneb_is_true; eauto.
    eapply safe_if_is_bool; eauto.
    eauto.
    eauto.

    (* if-false *)
    injection H1; intros; subst; clear H1.
    edestruct IHRunsTo.
    eauto.
    eauto.
    eauto.
    eapply safe_if_false; eauto.
    eapply wneb_is_false; eauto.
    eapply safe_if_is_bool; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToIfFalse.
    eapply wneb_is_false; eauto.
    eapply safe_if_is_bool; eauto.
    eauto.
    eauto.


    (* while-true *)
    admit.
    (* while-false *)
    admit.

    (* label *)
    admit.

    (* assign *)
    admit.

  Qed.

End Make.