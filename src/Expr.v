(** TODO List
 ** - Merging states
 ** - Lifting expressions to new states
 ** - Unification variables?
 **)
Require Import List Env.
Require Import EqdepClass.

Set Implicit Arguments.

Section env.
  Record type := {
    Impl : Type;
    Eq : forall x y : Impl, option (x = y)
  }.

  Variable types : list type.

  Definition tvar := option (fin types).
  Definition tvarD x := match x with
                          | None => Prop
                          | Some x => Impl (get types x)
                        end.

  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Record signature := {
    Domain : list tvar;
    Range : tvar;
    Denotation : functionTypeD (map tvarD Domain) (tvarD Range)
  }.

  Definition functions := list signature.
  Definition variables := list tvar.

  Variable funcs : functions.
  Variable uvars : variables.
  Variable vars : variables.

  Definition func := fin funcs.
  Definition var := fin vars.
  Definition uvar := fin uvars.

  Inductive expr : tvar -> Type :=
  | Const : forall t : tvar, tvarD t -> expr t
  | Var : forall x : var, expr (get vars x)
  | UVar : forall x : uvar, expr (get uvars x)
  | Func : forall f : func, hlist expr (Domain (get funcs f)) -> expr (Range (get funcs f)).

  Fixpoint hlist_All T F (ls : list T) (P : forall t : T, F t -> Prop) (h : hlist F ls) {struct h} : Prop :=
    match h with
      | HNil => True
      | HCons _ _ a b => P _ a /\ hlist_All P b
    end.

  Lemma expr_ind_strong : forall (P : forall t, expr t -> Prop),
    (forall (t : tvar) (t0 : tvarD t), P t (Const t t0)) ->
    (forall x : var, P (get vars x) (Var x)) ->
    (forall x : uvar, P (get uvars x) (UVar x)) ->
    (forall (f2 : func) (h : hlist expr (Domain (get funcs f2))),
      hlist_All P h ->
      P (Range (get funcs f2)) (Func f2 h)) ->
    forall (t : tvar) (e : expr t), P t e.
  Proof.
    intros P Hconst Hvar Huvar Hfunc.
    refine (fix expr_ind_strong t e {struct e} : P t e :=
      match e as e in expr t return P t e with
        | Var _ => Hvar _ 
        | Const _ _ => Hconst _ _
        | UVar _ => Huvar _
        | Func _ h  => 
          Hfunc _ _ ((fix prove_sub ls (h : hlist expr ls) : hlist_All P h :=
            match h with
              | HNil => I
              | HCons _ _ e r => conj (expr_ind_strong _ e) (prove_sub _ r)
            end) _ h)
      end).
  Qed.

  Section applyD.
    Variable exprD : forall t, expr t -> tvarD t.

    Fixpoint applyD domain (xs : hlist expr domain)
      : forall range, functionTypeD (map tvarD domain) range -> range :=
        match xs in hlist _ domain return forall range, functionTypeD (map tvarD domain) range -> range with
          | HNil => fun _ x => x
          | HCons _ _ x xs' => fun _ f => applyD xs' _ (f (exprD x))
        end.

    Fixpoint etaD domain {struct domain}
      : forall (xs : hlist expr domain) range, functionTypeD (map tvarD domain) (tvarD range) -> tvarD range :=
        match domain return forall (xs : hlist expr domain) range, functionTypeD (map tvarD domain) (tvarD range) -> tvarD range with
          | nil => fun _ _ D => D
          | a :: b => fun hl r D => @etaD b (hlist_tl hl) r (D (exprD (hlist_hd hl)))
        end.
  End applyD.

  Variable uenv : hlist tvarD uvars.
  Variable env : hlist tvarD vars.

  Fixpoint exprD t (e : expr t) {struct e} : tvarD t :=
    match e with
      | Const _ c => c
      | Var x => hlist_get x env
      | UVar x => hlist_get x uenv
      | Func f xs => applyD exprD xs _ (Denotation (get funcs f))
    end.
  
  Lemma tvar_dec : forall (a b : tvar), {a = b} + {a <> b}.
    decide equality. eapply finEq. 
  Defined.

  Definition tvarCmp (a : tvar) : forall b, dcomp a b :=
    match a as a return forall b, dcomp a b with
      | None => fun b => match b with
                           | None => Env.Eq (eq_refl _)
                           | _ => Env.Lt _ _
                         end
      | Some a => fun b => match b return dcomp (Some a) b with
                             | None => Env.Gt _ _ 
                             | Some b =>
                               match finCmp a b with
                                 | Env.Eq pf => Env.Eq (match pf in _ = t return Some a = Some t with 
                                                          | refl_equal => refl_equal _
                                                        end)
                                 | Env.Lt => Env.Lt _ _
                                 | Env.Gt => Env.Gt _ _
                               end
                           end
    end.

  Definition exprEq : forall t (x y : expr t), option (x = y).
  refine (fix exprEq t (x : expr t) {struct x} : forall y : expr t, option (x = y) :=
    match x in expr t return forall y : expr t, option (x = y) with
      | Const t c1 => fun y : expr t => 
        match y in expr t' return forall c1 : tvarD t', option (Const t' c1 = y) with
          | Const t c2 => match t return forall c2 c1 : tvarD t, option (Const t c1 = Const t c2) with
                            | None => fun _ _ => None
                            | Some t => fun x y => if Eq (get types t) x y then Some _ else None
                          end c2
          | _ => fun _ => None
        end c1
      | Var x1 => fun y => 
        match y in expr t return forall Heq : t = get vars x1, option (Var x1 = match Heq in _ = T return expr T with
                                                                                  | refl_equal => y
                                                                                end) with
          | Var x2 => fun Heq => if finEq x1 x2 then Some _ else None
          | _ => fun _ => None
        end (refl_equal _)
      | UVar x1 => fun y => 
        match y in expr t 
          return forall Heq : t = get uvars x1, 
            option (UVar x1 = match Heq in _ = T return expr T with
                                | refl_equal => y
                              end) with
          | UVar x2 => fun Heq => if finEq x1 x2 then Some _ else None
          | _ => fun _ => None
        end (refl_equal _)
      | Func f1 xs1 => fun y => 
        match y in expr t return forall Heq : t = Range (get funcs f1),
          (forall xs2, option (xs1 = xs2))
          -> option (Func f1 xs1 = match Heq in _ = T return expr T with
                                     | refl_equal => y
                                   end) with
          | Func f2 xs2 => fun Heq cmp => match finEq f1 f2 with
                                            | right _ => None
                                            | left Heq' =>
                                              if cmp (match sym_eq Heq' in _ = F
                                                        return hlist expr (Domain (get funcs F)) with
                                                        | refl_equal => xs2
                                                      end) then Some _ else None
                                          end
          | _ => fun _ _ => None
        end (refl_equal _) (hlistEq exprEq xs1)
    end); clear exprEq; try abstract (subst;
      repeat match goal with
               | [ Heq : _ = _ |- _ ] => rewrite (@UIP_refl _ _ _ Heq) in *; clear Heq; simpl in *
             end; congruence).
  Defined.

  Definition exprCmp : forall t (x y : expr t), option (dcomp x y).
   refine (fun _ _ _ => None).
  Defined.
End env.

Section Lifting.
  Variable types : list type.
  Variable funcs : functions types.
  Section Vars.
    Variable uvars : variables types.
    Variable vars' ext vars : variables types.

    Fixpoint liftExpr (T : tvar types) (e : expr funcs uvars (vars' ++ vars) T) 
      : expr funcs uvars (vars' ++ ext ++ vars) T :=
      match e in expr _ _ _ T return expr funcs uvars (vars' ++ ext ++ vars) T with
        | Var v => 
          match @liftDmid _ vars vars' ext v with
            | existT v pf => match pf in _ = t 
                               return expr funcs uvars (vars' ++ ext ++ vars) t
                               with
                               | refl_equal => Var _ uvars v
                             end
          end
        | UVar v => UVar _ _ v
        | Const t x => Const funcs uvars (vars' ++ ext ++ vars) t x 
        | Func f a => 
          Func f (@hlist_map _ _ (expr funcs uvars (vars' ++ ext ++ vars)) (fun t (x : expr funcs uvars (vars' ++ vars) t) => liftExpr x) _ a)
      end.

  End Vars.


  Lemma liftExpr_nil : forall uvars vars' vars T (e : expr funcs uvars (vars' ++ vars) T),
    liftExpr vars' nil vars e = e.
  Proof.
    induction e using expr_ind_strong; simpl; auto.
    assert (liftDmid vars vars' nil x = @existT _ _ x (refl_equal _)). admit.
    rewrite H. auto.
    f_equal. induction h; simpl; auto. simpl in *. firstorder. f_equal; auto.
  Qed.
  
  Parameter hlist_get_lift : forall ls ls' ls'' (f : fin (ls ++ ls'')) G G' G'',
    hlist_get f (hlist_app G G'') = match liftDmid ls'' ls ls' f with
                                      | existT f' pf =>
                                        match pf in _ = t return @tvarD types t with
                                          | refl_equal => 
                                            hlist_get f' (hlist_app G (hlist_app G' G''))
                                        end
                                    end.

  Lemma hlist_nil_only : forall (F : tvar types -> Type) (h : hlist F nil), 
    h = HNil.
  Proof.
    clear. intros.
    change h with (match refl_equal in _ = t return hlist F t with
                     | refl_equal => h
                   end).
    generalize (refl_equal (@nil (tvar types))). generalize h. clear. 
    assert (forall k (h : hlist F k) (e : k = nil),
      match e in (_ = t) return (hlist F t) with
        | eq_refl => h
      end = HNil).
    destruct h. 
    uip_all. reflexivity.
    congruence.
    eauto.
  Qed.

  Lemma hlist_eta : forall a b (F : tvar types -> Type) (h : hlist F (a :: b)),
    h = HCons (hlist_hd h) (hlist_tl h).
  Proof.
    clear. intros.
    assert (forall k (h : hlist F k) (e : k = a :: b),
      match e in (_ = t) return (hlist F t) with
        | eq_refl => h
      end = HCons (hlist_hd match e in _ = t return hlist F t with
                              | eq_refl => h
                            end)
                  (hlist_tl match e in _ = t return  hlist F t with
                              | eq_refl => h
                            end)).
    destruct h0. congruence.
    intros. inversion e. subst.
    generalize e. uip_all. reflexivity.

    specialize (H _ h (refl_equal _)). assumption.
  Qed.

  Lemma liftExpr_denote : forall uvars vars' vs vars T (e : expr funcs uvars (vars' ++ vars) T) U G G' G'', 
      exprD U (hlist_app G (hlist_app G' G'')) (liftExpr vars' vs vars e) = exprD U (hlist_app G G'') e.
  Proof.
    induction e using expr_ind_strong; simpl; auto.
      case_eq (liftDmid vars vars' vs x); intros. 
      generalize (@hlist_get_lift vars' vs vars x G G' G''). intros.
      unfold tvar in *. rewrite H0. rewrite H. clear.
      generalize (hlist_app G (hlist_app G' G'')). generalize e.
      rewrite <- e. intros. uip_all. reflexivity.

      generalize dependent h. destruct (get funcs f2). simpl. 
        generalize dependent Denotation0.      
        induction Domain0; simpl; intros. clear H.
        rewrite (@hlist_nil_only _ h). simpl. auto.
       
      rewrite (hlist_eta h) in *. simpl in *. rewrite IHDomain0; try tauto.
        f_equal. destruct H. rewrite H. reflexivity.
  Qed.

  Section UVars.
    Variable uvars' ext uvars : variables types.
    Variable vars : variables types.

    Fixpoint liftExprU (T : tvar types) (e : expr funcs (uvars' ++ uvars) vars T) 
      : expr funcs (uvars' ++ ext ++ uvars) vars T :=
      match e in expr _ _ _ T return expr funcs (uvars' ++ ext ++ uvars) vars T with
        | UVar v => 
          match @liftDmid _ uvars uvars' ext v with
            | existT v pf => match pf in _ = t 
                               return expr funcs (uvars' ++ ext ++ uvars) vars t
                               with
                               | refl_equal => UVar _ vars v
                             end
          end
        | Var v => Var _ _ v
        | Const t x => Const funcs (uvars' ++ ext ++ uvars) vars t x 
        | Func f a => 
          Func f (@hlist_map _ _ (expr funcs (uvars' ++ ext ++ uvars) vars) (fun t (x : expr funcs (uvars' ++ uvars) vars t) => liftExprU x) _ a)
      end.
  End UVars.

End Lifting.

Section Qexpr.
  Context {types : list type}.
  Variable fs : functions types.

  Definition Qexpr := { x : variables types & expr fs nil x None }.

  Fixpoint denoteQuant (ls : variables types) : (hlist (@tvarD types) ls -> Prop) -> Prop :=
    match ls as ls return (hlist (@tvarD types) ls -> Prop) -> Prop with
      | nil => fun cc => cc (HNil)
      | a :: b => fun cc => 
        forall x, denoteQuant (fun g => cc (HCons x g))
    end.

  Definition qexprD (p : Qexpr) : Prop :=
    @denoteQuant (projT1 p) (fun x => exprD HNil x (projT2 p)).
End Qexpr.

Section ProverT.
  Context {types : list type}.
  Variable fs : functions types.

  Definition ProverT : Type := forall 
    (hyps : list (@expr types fs nil nil None))
    (goal : @expr types fs nil nil None), 
    hlist (fun e => @exprD _ fs _ _ HNil HNil None e) hyps -> 
    option (exprD HNil HNil goal).
  
End ProverT.

Section PartialApply.
  Fixpoint funtype (ls : list Type) (r : Type) : Type :=
    match ls with 
      | nil => r
      | a :: b => a -> funtype b r
    end.

  Fixpoint apply_ls (ls : list Type) (T : Type) (R : T -> Type) (V : T)
    : funtype ls (forall x : T, R x) -> funtype ls (R V) :=
    match ls with
      | nil => fun F => F V
      | a :: b => fun F => fun x : a => apply_ls b R V (F x)
    end.
End PartialApply.

(** Reflection Tactics **)
(************************)
Require Import Reflect.

Ltac extend_type T D types :=
  match T with
    | Prop => types
    | _ => 
      let rec find types :=
      match types with
        | nil => constr:(false)
        | ?a :: ?b =>
          let T' := eval simpl Impl in (Impl a) in
          match T' with
            | T => constr:(true)
            | _ => find b
          end
      end
    in
    match find types with
      | true => types
      | _ => constr:(D :: types)
    end
  end.

Definition defaultType T := {| Impl := T; Eq := fun _ _ => None |}.

Ltac extend_all_types Ts types :=
  match Ts with
    | nil => types
    | ?a :: ?b => 
      let types := extend_type a (defaultType a) types in
      extend_all_types b types
  end.

Ltac buildTypes e types :=
  let rec bt_args args types :=
    match args with
      | tt => types
      | (?a, ?b) => 
        let types := buildTypes a types in
        bt_args b types
    end
  in
  let cc _ Ts args :=
    let Ts := bt_args args Ts in
    let Ts := eval simpl app in Ts in
    extend_all_types Ts types
  in
  refl_app cc e.

Ltac collectTypes_expr e types :=
  let rec bt_args args types :=
    match args with
      | tt => types
      | (?a, ?b) =>
        let types := collectTypes_expr a types in
        bt_args b types
    end
  in
  let cc _ Ts args := 
    let types := append_uniq Ts types in
    let types := bt_args args types in
    types
  in
  refl_app cc e.

(*
Parameter g : bool -> nat -> nat -> nat.

Set Printing Implicit.

Goal forall a b, g a b b = b.
    intros.
    match goal with
      | [ |- ?L ] =>
        let r := constr:(@nil Type) in
          let t := constr:((nat : Type) :: nil) in
        let lt := collectTypes_expr L r in
(*        let rt := collectTypes_sexpr R lt in *)
        idtac lt
(*
        let Ts := constr:(@nil type) in
        let g := elabTypes Ts f in
        idtac g
*)
    end.
*)

Ltac typesIndex x types :=
  indexOf Impl x types.
(*
  match types with
    | ?T1 :: ?TS =>
      match types' with
        | x :: _ => constr:(@FO _ T1 TS)
        | _ :: ?ls' => let f := typesIndex x TS ls' in constr:(@FS _ T1 TS f)
      end
  end.
*)

Ltac funcIndex x funcs :=
  indexOf Denotation x funcs.
(*
  match funcs with
    | ?F :: ?ls' =>
      let F' := eval simpl in (Denotation F) in
      match F' with
        | x => constr:(@FO _ F ls')
        | _ => let f := funcIndex x ls' in constr:(@FS _ F ls' f)
      end
  end.
*)

Ltac refl_type types types' T :=
  match T with
    | Prop => constr:(None : tvar types)
    | _ => 
      let i := typesIndex T types types' in
      constr:(Some i)
  end.

Ltac refl_signature types types' f :=
  let rec refl T :=
    match T with 
      | ?A -> ?B =>
        let Ta := refl_type types types' A in
        match refl B with
          | ( ?args , ?rt ) =>
            let res := constr:(((Ta : @tvar types) :: args , rt)) in
                res
        end
      | _ =>
        let T := refl_type types types' T in
        constr:((@nil (@tvar types), T))
    end
  in
  let T := type of f in
  (** NOTE: T should never be dependent **)
  match refl T with
    | ( ?args , ?rt ) =>
      constr:(@Build_signature types args rt f)
  end.

Ltac extend_func types types' f funcs :=
  let rec find fs :=
    match fs with
      | nil => false
      | ?X :: ?Y =>
        let X' := eval simpl in (Denotation X) in
        match X' with
          | f => true
          | _ => find Y
        end
    end
  in
  match find funcs with
    | true => funcs
    | false => 
      let s := refl_signature types types' f in
      constr:(s :: funcs)
  end.

Ltac buildFuncs isConst types types' e funcs :=
  let rec refl_args args funcs :=
    match args with
      | tt => funcs
      | (?X, ?Y) => 
        let funcs := bf X funcs in
        refl_args Y funcs
    end
  with bf e funcs :=
    match isConst e with
      | true => funcs
      | _ => 
        let cc f Ts args := 
          let funcs := extend_func types types' f funcs in
          refl_args args funcs
        in        
        refl_app cc e
    end
  in bf e funcs.

Ltac buildExpr isConst types types' funcs vars e :=
  let rec refl_args args :=
    match args with
      | tt => 
        let res := constr:(@HNil _ (@expr types funcs vars)) in
        res
      | (?X, ?Y) => 
        let x := be X in
        let y := refl_args Y in
            let res := constr:(HCons x y) in
              res
    end
  with be e :=
    match isConst e with
      | false =>
        let cc f Ts args := 
          let f := funcIndex f funcs in
          let args := refl_args args in
          constr:(@Func types funcs vars f args)
        in        
        refl_app cc e
      | true =>
        let t := type of e in
        let t := refl_type types types' t in
        let res := constr:(@Const types funcs vars t e) in
        res
    end
  in be e.

Ltac extendEnv isConst types funcs vars G :=
  match G with
    | forall x : _ , ?G' =>
      let types := buildTypes G types in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G funcs in
      let funcs := eval simpl in funcs in
      extendEnv isConst types funcs vars G'
    | forall x : _ , @?G' x => fail (** TODO : how do I fill the hole in G'? **)
    | _ => 
      let types := buildTypes G types in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G funcs in
      let funcs := eval simpl in funcs in
      constr:((types, funcs, vars))
  end.

Ltac reflect_goal isConst types funcs vars :=
  match goal with
    | [ |- ?G ] =>
      let types := buildTypes G (@nil type) in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G (@nil (signature types)) in
      let funcs := eval simpl in funcs in
      let vars := constr:(@nil (tvar types)) in
      let e := buildExpr isConst types types' funcs vars G in
      change (exprD HNil HNil e)
  end.

Ltac reflect isConst :=
  match goal with
    | [ |- ?G ] =>
      let types := buildTypes G (@nil type) in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G (@nil (signature types)) in
      let funcs := eval simpl in funcs in
      let vars := constr:(@nil (tvar types)) in
      let e := buildExpr isConst types types' funcs vars G in
      change (exprD HNil HNil e)
  end.


Ltac consts e :=
  match e with
    | true => true
    | false => true
    | O => true
    | S ?n => consts n
    | _ => false
  end.

(** Three simple test cases **) 
(** These terms get pretty big since we have to store the list instead of just the length.
 ** It would probably be beneficial to let-bind some terms unless Coq is doing its own sharing
 **)
(* TODO: Fix this if unification works out well this way....

Goal forall a b : nat, a + b = a + b.
  intros; reflect consts.
(* Performance Evaluation *)
  match goal with
    | [ |- exprD _ (Func _ (HCons ?A (HCons ?B _))) ] => 
      pose A ; pose B
  end.
  pose (exprEq e e0). hnf in o.
Abort.

Goal negb false = true.
  intros; reflect consts.
Abort.

Goal forall n m, n + m = m + 0 + n.
  intros; reflect consts.
Abort.
*)

Require Export Env.