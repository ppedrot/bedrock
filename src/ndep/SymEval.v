Require Import List Bedrock.DepList Word Memory.
Require Import Heaps SepTheoryX.
Require Import Bedrock.ndep.Expr Bedrock.ndep.SepExpr Bedrock.ndep.Provers.

Set Implicit Arguments.
Set Strict Implicit.

Section UpdatePosition.
  Variable T : Type.

  Fixpoint updatePosition (n : nat) (v : T) (ls : list T) : list T :=
    match n , ls with
      | 0 , nil => v :: nil
      | 0 , _ :: b => v :: b 
      | S n , nil => v :: updatePosition n v nil
      | S n , a :: b => a :: updatePosition n v b
    end.

  Lemma updatePosition_eq : forall n types' t,
    nth_error (updatePosition n t types') n = Some t.
  Proof.
    induction n; simpl; destruct types'; eauto.
  Defined.

  Lemma updatePosition_neq : forall t n types' m,
    n <> m ->
    nth_error types' n <> None ->
    nth_error (updatePosition m t types') n = nth_error types' n.
  Proof.
    clear.
    induction n; destruct types'; destruct m; simpl; intros; try solve [ exfalso; auto; omega ]; auto.
  Defined.
End UpdatePosition.

(** * These are generic search functions *)
Section search_read_write.
  Variable A : Type.
  Variable B : A -> Type.
  Variable types : list type.
  Variable sfuncs : list A.

  Variable T : Type.
  Variable F : forall s, B s -> list (expr types) -> option T.
  Variable F_upd : forall s, B s -> list (expr types) -> option (list (expr types)).

  Section arg.
    Variable ss : A.
    Variable se : B ss.
    
    Fixpoint fold_args (es : list (list (expr types))) : option T :=
      match es with 
        | nil => None
        | a :: b => 
          match F se a with
            | None => fold_args b
            | Some r => Some r
          end
      end.
    
    Theorem fold_args_correct : forall es v,
      fold_args es = Some v ->
      exists k, In k es /\ F se k = Some v.
    Proof.
      clear. induction es.
      simpl; congruence.
      simpl. case_eq (F se a); intros.
      inversion H0. subst. eauto.
      eapply IHes in H0. destruct H0.
      exists x. tauto.
    Qed.

    Fixpoint fold_args_update (es : list (list (expr types))) : option (list (list (expr types))) :=
      match es with 
        | nil => None
        | a :: b => 
          match F_upd se a with
            | None => match fold_args_update b with
                        | None => None
                        | Some b => Some (a :: b)
                      end
            | Some r => Some (r :: b)
          end
      end.
    
    Theorem fold_args_update_correct : forall es es',
      fold_args_update es = Some es' ->
      exists pre, exists post, exists k, exists k',
        es = pre ++ k :: post /\
        F_upd se k = Some k' /\
        es' = pre ++ k' :: post.
    Proof.
      clear. induction es.
      simpl; congruence.
      simpl. case_eq (F_upd se a); intros.
      inversion H0. subst. do 4 eexists; intuition eauto.
      instantiate (2 := nil). reflexivity. reflexivity.

      generalize dependent H0.
      case_eq (fold_args_update es); intros.
      inversion H1; subst. eapply IHes in H0.
      do 4 destruct H0. exists (a :: x). exists x0.
      eexists; eexists; intuition; subst; eauto. reflexivity.

      congruence.
    Qed.
  End arg.

  Variable impures : FM.t (list (list (expr types))).

  Fixpoint fold_known (k : list nat) :
    hlist (fun n : nat => match nth_error sfuncs n with
                            | None => Empty_set 
                            | Some ss => B ss
                          end) k
    -> option T :=
    match k as k 
      return hlist (fun n : nat => match nth_error sfuncs n with
                                     | None => Empty_set 
                                     | Some ss => B ss
                                   end) k
      -> option T
      with
      | nil => fun _ => None
      | a :: b => fun ss =>
        match FM.find a impures with
          | None => fold_known (hlist_tl ss)
          | Some argss =>
            match nth_error sfuncs a as ss
              return match ss with
                       | None => Empty_set 
                       | Some ss => B ss
                     end -> option T
              with
              | Some _ => fun se =>
                match fold_args se argss with
                  | None => fold_known (hlist_tl ss)
                  | Some r => Some r
                end
              | None => fun err => match err with end
            end (hlist_hd ss)
        end
    end.
  
  Theorem fold_known_correct : forall k
    (h : hlist (fun n : nat => match nth_error sfuncs n with
                                 | None => Empty_set 
                                 | Some ss => B ss
                               end) k) v,
    @fold_known k h = Some v ->
    exists n, exists ss,
      exists se :  B ss, exists ls, exists args, 
        nth_error sfuncs n = Some ss 
        /\ FM.find n impures = Some ls 
        /\ In args ls 
        /\ F se args = Some v.
  Proof.
    clear. induction k; simpl.
    congruence.
    intros h v. specialize (IHk (hlist_tl h) v).
    rewrite (hlist_eta _ h) in *.
    generalize dependent (hlist_hd h). simpl.
    case_eq (FM.find a impures); intros; eauto 10.

    assert (exists k, nth_error sfuncs a = Some k).
    generalize y. clear.
    destruct (nth_error sfuncs a); [ eauto | destruct 1 ]. 
    destruct H1.
    generalize dependent y.
    rewrite H1. intro.
    case_eq (fold_args y l); intros; eauto 10.
    inversion H2; subst.
    eapply fold_args_correct in H0. destruct H0; eauto 10.
  Qed.

  Fixpoint fold_known_update (k : list nat) :
    hlist (fun n : nat => match nth_error sfuncs n with
                            | None => Empty_set 
                            | Some ss => B ss
                          end) k
    -> option (FM.t (list (list (expr types)))) :=
    match k as k 
      return hlist (fun n : nat => match nth_error sfuncs n with
                                     | None => Empty_set 
                                     | Some ss => B ss
                                   end) k
      -> option (FM.t (list (list (expr types))))
      with
      | nil => fun _ => None
      | a :: b => fun ss =>
        match FM.find a impures with
          | None => fold_known_update (hlist_tl ss)
          | Some argss =>
            match nth_error sfuncs a as ss
              return match ss with
                       | None => Empty_set 
                       | Some ss => B ss
                     end -> option (FM.t (list (list (expr types))))
              with
              | Some _ => fun se =>
                match fold_args_update se argss with
                  | None => fold_known_update (hlist_tl ss)
                  | Some r => Some (FM.add a r impures) (* this is a replace *)
                end
              | None => fun err => match err with end
            end (hlist_hd ss)
        end
    end.
  
  Theorem fold_known_update_correct : forall k
    (h : hlist (fun n : nat => match nth_error sfuncs n with
                                 | None => Empty_set 
                                 | Some ss => B ss
                               end) k) i',
    @fold_known_update k h = Some i' ->
    exists n, exists ss,
      exists se : B ss, exists ls, exists ls',
        nth_error sfuncs n = Some ss 
        /\ FM.find n impures = Some ls 
        /\ fold_args_update se ls = Some ls'
        /\ i' = FM.add n ls' impures.
  Proof.
    clear. induction k; simpl.
    congruence.
    intros h v. specialize (IHk (hlist_tl h) v).
    rewrite (hlist_eta _ h) in *.
    generalize dependent (hlist_hd h). simpl.
    case_eq (FM.find a impures); intros; eauto 10.

    assert (exists k, nth_error sfuncs a = Some k).
    generalize y. clear.
    destruct (nth_error sfuncs a); [ eauto | destruct 1 ]. 
    destruct H1.
    generalize dependent y.
    rewrite H1. intro.
    case_eq (fold_args_update y l); intros; eauto 10.
    inversion H2; subst.
    eauto 10.
  Qed.

End search_read_write.

Module Type EvaluatorPluginType (B : Heap) (ST : SepTheoryX.SepTheoryXType B).
  Module Import SEP := SepExpr B ST.

  Section typed.
    Variable types : list type.

    Variable tvState : tvar.
    Variable tvPc : tvar.
    Variable tvPtr : tvar.
    Variable tvVal : tvar.

    Variable smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
      option (tvarD types tvVal).
    Variable smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
      -> ST.HT.smem -> option ST.HT.smem.
    
    Variable funcs : functions types.

    (** TODO: This can't be a record, it needs to be a dependent tuple,
     ** i.e. we don't want to create a new inductive type b/c then
     ** we'll be generative and we want to be applicative.
     **)
    Parameter SymEval : forall
      (types : list type)
      (tvState : tvar)
      (tvPc : tvar)
      (tvPtr : tvar)
      (tvVal : tvar)
      
      (smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
        option (tvarD types tvVal))
      (smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
        -> ST.HT.smem -> option ST.HT.smem)
      
      (funcs : functions types)
      (Predicate : ssignature types tvPc tvState), Type.

    Parameter sym_read : forall
      (types : list type)
      (tvState : tvar)
      (tvPc : tvar)
      (tvPtr : tvar)
      (tvVal : tvar)
      
      (smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
        option (tvarD types tvVal))
      (smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
        -> ST.HT.smem -> option ST.HT.smem)
      
      (funcs : functions types)
      (Predicate : ssignature types tvPc tvState), 
      @SymEval types tvState tvPc tvPtr tvVal smem_get_value smem_set_value funcs Predicate -> 
      forall (hyps args : list (expr types)) (p : expr types),
        option (expr types).

    Parameter sym_read_correct : forall
      (types : list type)
      (tvState : tvar)
      (tvPc : tvar)
      (tvPtr : tvar)
      (tvVal : tvar)
      
      (smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
        option (tvarD types tvVal))
      (smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
        -> ST.HT.smem -> option ST.HT.smem)
      
      (funcs : functions types)
      (Predicate : ssignature types tvPc tvState)
      (se : @SymEval types tvState tvPc tvPtr tvVal smem_get_value smem_set_value funcs Predicate), 
      forall args uvars vars cs hyps pe ve m stn,
        sym_read se hyps args pe = Some ve ->
        AllProvable funcs uvars vars hyps ->
        match 
          applyD (exprD funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match 
          exprD funcs uvars vars pe tvPtr, 
          exprD funcs uvars vars ve tvVal
          with
          | Some p , Some v =>
            smem_get_value stn p m = Some v
          | _ , _ => False
        end.

    Parameter sym_write : forall
      (types : list type)
      (tvState : tvar)
      (tvPc : tvar)
      (tvPtr : tvar)
      (tvVal : tvar)
      
      (smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
        option (tvarD types tvVal))
      (smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
        -> ST.HT.smem -> option ST.HT.smem)
      
      (funcs : functions types)
      (Predicate : ssignature types tvPc tvState), 
      @SymEval types tvState tvPc tvPtr tvVal smem_get_value smem_set_value funcs Predicate ->
      forall (hyps args : list (expr types)) (p v : expr types),
        option (list (expr types)).

    Parameter sym_write_correct : forall
      (types : list type)
      (tvState : tvar)
      (tvPc : tvar)
      (tvPtr : tvar)
      (tvVal : tvar)
      
      (smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
        option (tvarD types tvVal))
      (smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
        -> ST.HT.smem -> option ST.HT.smem)
      
      (funcs : functions types)
      (Predicate : ssignature types tvPc tvState)
      (se : @SymEval types tvState tvPc tvPtr tvVal smem_get_value smem_set_value funcs Predicate),
      forall args uvars vars cs hyps pe ve v m stn args',
        sym_write se hyps args pe ve = Some args' ->
        AllProvable funcs uvars vars hyps ->
        exprD funcs uvars vars ve tvVal = Some v ->
        match
          applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match exprD funcs uvars vars pe tvPtr with
          | Some p =>
            match 
              applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate)
            with
              | None => False
              | Some pr => 
                match smem_set_value stn p v m with
                  | None => False
                  | Some sm' => ST.satisfies cs pr stn sm'
                end
            end
          | _ => False
        end.

    Parameter Build_SymEval : forall
      (types : list type)
      (tvState : tvar)
      (tvPc : tvar)
      (tvPtr : tvar)
      (tvVal : tvar)
      
      (smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
        option (tvarD types tvVal))
      (smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
        -> ST.HT.smem -> option ST.HT.smem)
      
      (funcs : functions types)
      (Predicate : ssignature types tvPc tvState)

      (sym_read : forall (hyps args : list (expr types)) (p : expr types),
        option (expr types))
      (sym_write : forall (hyps args : list (expr types)) (p v : expr types),
        option (list (expr types)))
      (sym_read_correct : forall args uvars vars cs hyps pe ve m stn,
        sym_read hyps args pe = Some ve ->
        AllProvable funcs uvars vars hyps ->
        match 
          applyD (exprD funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match 
          exprD funcs uvars vars pe tvPtr, 
          exprD funcs uvars vars ve tvVal
          with
          | Some p , Some v =>
            smem_get_value stn p m = Some v
          | _ , _ => False
        end)
      (sym_write_correct : forall args uvars vars cs hyps pe ve v m stn args',
        sym_write hyps args pe ve = Some args' ->
        AllProvable funcs uvars vars hyps ->
        exprD funcs uvars vars ve tvVal = Some v ->
        match
          applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match exprD funcs uvars vars pe tvPtr with
          | Some p =>
            match 
              applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate)
            with
              | None => False
              | Some pr => 
                match smem_set_value stn p v m with
                  | None => False
                  | Some sm' => ST.satisfies cs pr stn sm'
                end
            end
          | _ => False
        end),
      @SymEval types tvState tvPc tvPtr tvVal smem_get_value smem_set_value funcs Predicate.
      
  End typed.

End EvaluatorPluginType.

Module EvaluatorPlugin (B : Heap) (ST : SepTheoryX.SepTheoryXType B) : EvaluatorPluginType B ST.
  Module Import SEP := SepExpr B ST.

  Section typed.
    Variable types : list type.

    Variable tvState : tvar.
    Variable tvPc : tvar.
    Variable tvPtr : tvar.
    Variable tvVal : tvar.

    Variable smem_get_value : IL.settings -> tvarD types tvPtr -> ST.HT.smem -> 
      option (tvarD types tvVal).
    Variable smem_set_value : IL.settings -> tvarD types tvPtr -> tvarD types tvVal
      -> ST.HT.smem -> option ST.HT.smem.
    
    Variable funcs : functions types.

    Record SymEval' (Predicate : ssignature types tvPc tvState) : Type :=
    { sym_read  : 
      forall (hyps args : list (expr types)) (p : expr types),
      option (expr types)
    ; sym_write : 
      forall (hyps args : list (expr types)) (p v : expr types),
      option (list (expr types))
    ; sym_read_correct : forall args uvars vars cs hyps pe ve m stn,
      sym_read hyps args pe = Some ve ->
      AllProvable funcs uvars vars hyps ->
      match 
        applyD (exprD funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
        with
        | None => False
        | Some p => ST.satisfies cs p stn m
      end ->
      match 
        exprD funcs uvars vars pe tvPtr, 
        exprD funcs uvars vars ve tvVal
        with
        | Some p , Some v =>
          smem_get_value stn p m = Some v
        | _ , _ => False
      end
    ; sym_write_correct : forall args uvars vars cs hyps pe ve v m stn args',
      sym_write hyps args pe ve = Some args' ->
      AllProvable funcs uvars vars hyps ->
      exprD funcs uvars vars ve tvVal = Some v ->
      match
        applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
        with
        | None => False
        | Some p => ST.satisfies cs p stn m
      end ->
      match exprD funcs uvars vars pe tvPtr with
        | Some p =>
          match 
            applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate)
            with
            | None => False
            | Some pr => 
              match smem_set_value stn p v m with
                | None => False
                | Some sm' => ST.satisfies cs pr stn sm'
              end
          end
        | _ => False
      end
    }.

    Definition SymEval := SymEval'.

    Definition Build_SymEval := Build_SymEval'.

  End typed.

End EvaluatorPlugin.


Module BedrockEvaluator (B : Heap) (ST : SepTheoryX.SepTheoryXType B).
  Module Import SEP := SepExpr B ST.
  Require Import IL.

  (** TODO : This is specialized to bedrock **)
  Require Import Bedrock.SepTac.

  Variable types' : list type.
  Definition types := bedrock_types ++ types'.
  Definition pcT := tvType 0.
  Definition stT := tvType 1.

  (** These the reflected version of the IL, it essentially 
   ** replaces all uses of W with expr types so that the value
   ** can be inspected.
   ** TODO: Is it better to parameterize the initial definition in
   **       IL.v by the type of values?
   ** The problem comes (once again) from casts...
   **)
  Inductive sym_loc :=
  | SymReg : reg -> sym_loc
  | SymImm : expr types -> sym_loc
  | SymIndir : reg -> expr types -> sym_loc.

  (* Valid targets of assignments *)
  Inductive sym_lvalue :=
  | SymLvReg : reg -> sym_lvalue
  | SymLvMem : sym_loc -> sym_lvalue.
  
  (* Operands *)
  Inductive sym_rvalue :=
  | SymRvLval : sym_lvalue -> sym_rvalue
  | SymRvImm : expr types -> sym_rvalue
  | SymRvLabel : label -> sym_rvalue.

  (* Non-control-flow instructions *)
  Inductive sym_instr :=
  | SymAssign : sym_lvalue -> sym_rvalue -> sym_instr
  | SymBinop : sym_lvalue -> sym_rvalue -> binop -> sym_rvalue -> sym_instr.

  
  (** Symbolic registers **)
  Definition SymRegType : Type :=
    (expr types * expr types * expr types)%type.

  Definition sym_getReg (r : reg) (sr : SymRegType) : expr types :=
    match r with
      | Sp => fst (fst sr)
      | Rp => snd (fst sr)
      | Rv => snd sr
    end.

  Definition sym_setReg (r : reg) (v : expr types) (sr : SymRegType) : SymRegType :=
    match r with
      | Sp => (v, snd (fst sr), snd sr)
      | Rp => (fst (fst sr), v, snd sr)
      | Rv => (fst sr, v)
    end.

  (** Symbolic State **)
  Record SymState : Type :=
  { SymMem  : SEP.SHeap types pcT stT
  ; SymRegs : SymRegType
  }.

  (** This has to be connected to the type of the intermediate representation **)
  Definition tvWord := tvType 0.

  Definition sym_evalRval (rv : sym_rvalue) (ss : SymState) : option (expr types) :=
    match rv with
      | SymRvLval (SymLvReg r) =>
        Some (sym_getReg r (SymRegs ss))
      | SymRvLval (SymLvMem l) => 
        (** TODO: this should be a sym_eval_read **)
        None (* match evalLoc l with
                     | None => None
                     | Some a =>
                       if inBounds_dec a
                       then Some (ReadWord stn (Mem st) a)
                       else None
                   end *)
      | SymRvImm w => Some w 
      | SymRvLabel l => None (* Labels stn l *)
    end.

  Definition sym_evalLval (lv : sym_lvalue) (val : expr types) (ss : SymState) : option SymState :=
    match lv with
        | SymLvReg r =>
          Some {| SymMem := SymMem ss ; SymRegs := sym_setReg r val (SymRegs ss) |}
        | SymLvMem l => None 
          (** TODO: this should be a sym_eval_write **)
(* match evalLoc l with
                       | None => None
                       | Some a =>
                         if inBounds_dec a
                         then Some {| Regs := Regs st;
                           Mem := WriteWord stn (Mem st) a v |}
                         else None
                     end
*)
      end.

  Variable fPlus fMinus fTimes : expr types -> expr types -> expr types.

  Definition sym_evalInstr (i : sym_instr) (ss : SymState) : option SymState :=
    match i with 
      | SymAssign lv rv =>
        match sym_evalRval rv ss with
          | None => None
          | Some rv => sym_evalLval lv rv ss
        end
      | SymBinop lv l o r =>
        match sym_evalRval l ss , sym_evalRval r ss with
          | Some l , Some r => 
            let v :=
              match o with
                | Plus  => fPlus
                | Minus => fMinus
                | Times => fTimes                  
              end l r
            in
            sym_evalLval lv v ss
          | _ , _ => None
        end
    end.

  Variable funcs : functions types.

(*
  Hypothesis fPlus_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fPlus l r) tvWord = Some (wplus lv rv)
      | _ , _ => False
    end.
*)

  Variable sfuncs : SEP.sfunctions types pcT stT.

  (* Denotation functions *)
  Section sym_denote.
    Variable uvars vars : env types.

    Definition sym_regsD (rs : SymRegType) : option regs :=
      match rs with
        | (sp, rp, rv) =>
          match 
            exprD funcs uvars vars sp tvWord ,
            exprD funcs uvars vars rp tvWord ,
            exprD funcs uvars vars rv tvWord 
            with
            | Some sp , Some rp , Some rv =>
                Some (fun r => 
                  match r with
                    | Sp => sp
                    | Rp => rp
                    | Rv => rv
                  end)
            | _ , _ , _ => None
          end
      end.    

    Definition sym_locD (s : sym_loc) : option loc :=
      match s with
        | SymReg r => Some (Reg r)
        | SymImm e =>
          match exprD funcs uvars vars e tvWord with
            | Some e => Some (Imm e)
            | None => None
          end
        | SymIndir r o =>
          match exprD funcs uvars vars o tvWord with
            | Some o => Some (Indir r o)
            | None => None
          end
      end.

    Definition sym_lvalueD (s : sym_lvalue) : option lvalue :=
      match s with
        | SymLvReg r => Some (LvReg r)
        | SymLvMem l => match sym_locD l with
                          | Some l => Some (LvMem l)
                          | None => None
                        end
      end.

    Definition sym_rvalueD (r : sym_rvalue) : option rvalue :=
      match r with
        | SymRvLval l => match sym_lvalueD l with
                           | Some l => Some (RvLval l)
                           | None => None
                         end
        | SymRvImm e => match exprD funcs uvars vars e tvWord with
                          | Some l => Some (RvImm l)
                          | None => None
                        end
        | SymRvLabel l => Some (RvLabel l)
      end.

    Definition sym_instrD (i : sym_instr) : option instr :=
      match i with
        | SymAssign l r =>
          match sym_lvalueD l , sym_rvalueD r with
            | Some l , Some r => Some (Assign l r)
            | _ , _ => None
          end
        | SymBinop lhs l o r =>
          match sym_lvalueD lhs , sym_rvalueD l , sym_rvalueD r with
            | Some lhs , Some l , Some r => Some (Binop lhs l o r)
            | _ , _ , _ => None
          end
      end.

    Fixpoint sym_instrsD (is : list sym_instr) : option (list instr) :=
      match is with
        | nil => Some nil
        | i :: is => 
          match sym_instrD i , sym_instrsD is with
            | Some i , Some is => Some (i :: is)
            | _ , _ => None
          end
      end.

    Definition regsD (r : regs) (sr : SymRegType) : Prop :=
      let '(sp, rp, rv) := sr in
         exprD funcs uvars vars sp tvWord = Some (r Sp)
      /\ exprD funcs uvars vars rp tvWord = Some (r Rp)
      /\ exprD funcs uvars vars rv tvWord = Some (r Rv).

    Require Import PropX.

    Definition stateD cs (stn : IL.settings) (s : state) (ss : SymState) : Prop :=
      PropX.interp cs ([| regsD (Regs s) (SymRegs ss) |] /\ 
                       SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD (SymMem ss))) (stn, s))%PropX.

  End sym_denote.

(*
  Lemma sym_evalRvalueD_sound : forall r rD,
    sym_evalRvalueD uvars vars r = Some rD ->
    forall s ss,
      stateD cs stn s ss ->
      evalRvalueD rD = Some rD.

*)

  Theorem sym_evalIntr_sound : forall i iD uvars vars, 
    sym_instrD uvars vars i = Some iD ->
    forall stn ss ss',
    sym_evalInstr i ss = Some ss' ->
    forall specs s,
    stateD uvars vars specs stn s ss ->
    exists s',
    evalInstr stn s iD = Some s' /\ stateD uvars vars specs stn s' ss'.
  Proof.
    destruct i; simpl; intros iD uvars vars0.
      
      case_eq (sym_lvalueD uvars vars0 s); try congruence.
      case_eq (sym_rvalueD uvars vars0 s0); try congruence.
      intros. inversion H1; clear H1; subst.
        simpl.
        Lemma sym_rvalue_sound : forall uvars vars0 r rD,
          sym_rvalueD uvars vars0 r = Some rD ->
          forall specs stn s ss, 
          stateD uvars vars0 specs stn s ss ->
          forall rv,
          sym_evalRval r ss = Some rv ->
          exists rvD ,
          exprD funcs uvars vars0 rv tvWord = Some rvD /\
          evalRvalue stn s rD = Some rvD.
        Proof.          
        Admitted.
        Check sym_evalLval.
        Lemma sym_lvalue_sound : forall uvars vars0 l lD,
          sym_lvalueD uvars vars0 l = Some lD ->
          forall specs stn s ss, 
          stateD uvars vars0 specs stn s ss ->
          forall a aD ss',
          exprD funcs uvars vars0 a tvWord = Some aD ->
          sym_evalLval l a ss = Some ss' ->
          exists s' , 
               evalLvalue stn s lD aD = Some s'
            /\ stateD uvars vars0 specs stn s' ss'.
        Proof.
          destruct l; simpl; intros.
            inversion H; clear H; subst.
            inversion H2; clear H2; subst.
            simpl; eexists; split; [ reflexivity | ].
            Focus.
            unfold stateD, regsD in *. PropXTac.propxFo.
              destruct (SymRegs ss). destruct p.
              destruct r; simpl in *; intuition.

          
        Admitted.
        generalize dependent H2. case_eq (sym_evalRval s0 ss); try congruence.
        intros. eapply sym_rvalue_sound in H1; eauto. destruct H1. destruct H1.
        eapply sym_lvalue_sound in H2; eauto. do 2 destruct H2.
        rewrite H4. eauto.

  Admitted.

End BedrockEvaluator.


(*
Module Evaluator (B : Heap) (ST : SepTheoryX.SepTheoryXType B).
  Module Import SEP := SepExpr B ST.

  Section typed.
    Variable types' : list type.

    Variable stateIndex : nat.
    Variable pcIndex : nat.
    Variable ptrIndex : nat.
    Definition ptrType : type :=
      {| Impl := B.addr
       ; Eq := fun x y => match B.addr_dec x y with
                           | left pf => Some pf
                           | _ => None
                         end
       |}.

    (** * Bytes *)
    Section ByteAccess.
      Variable byteIndex : nat.
      Definition byteType : type :=
        {| Impl := B
         ; Eq := fun x y => match weq x y with
                              | left pf => Some pf
                              | _ => None
                            end
         |}.

      Hypothesis byte_ptr : byteIndex <> ptrIndex.

      Definition btypes := 
        updatePosition ptrIndex ptrType (updatePosition byteIndex byteType types').

      Variable funcs : functions btypes.

      Lemma ptrType_get : tvarD btypes (tvType ptrIndex) = B.addr.
        unfold btypes, tvarD. rewrite updatePosition_eq. reflexivity.
      Qed.

      Definition exprD_ptr (uvars vars : env btypes)
        (e : expr btypes) : option B.addr :=
        match ptrType_get in _ = t return option t with
          | refl_equal => exprD funcs uvars vars e (tvType ptrIndex)
        end.

      Lemma byteType_get : tvarD btypes (tvType byteIndex) = B.
        unfold btypes, tvarD. rewrite updatePosition_neq; auto;
        rewrite updatePosition_eq; auto. congruence.
      Qed.

      Definition exprD_byte (uvars vars : env btypes)
        (e : expr btypes) : option B :=
        match byteType_get in _ = t return option t with
          | refl_equal => exprD funcs uvars vars e (tvType byteIndex)
        end.

      Record SymEval_byte (Predicate : ssignature btypes (tvType pcIndex) (tvType stateIndex))
        : Type :=
      { sym_read_byte  : 
        forall (hyps args : list (expr btypes)) (p : expr btypes), option (expr btypes)
      ; sym_write_byte : 
        forall (hyps args : list (expr btypes)) (p v : expr btypes),
        option (list (expr btypes))
      ; sym_read_byte_correct : forall args uvars vars cs hyps pe ve m stn,
        sym_read_byte hyps args pe = Some ve ->
        AllProvable funcs uvars vars hyps ->
        match 
          applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match exprD_ptr uvars vars pe , exprD_byte uvars vars ve with
          | Some p , Some v =>
            ST.HT.smem_get p m = Some v
          | _ , _ => False
        end
      ; sym_write_byte_correct : forall args uvars vars cs hyps pe ve v m stn args',
        sym_write_byte hyps args pe ve = Some args' ->
        AllProvable funcs uvars vars hyps ->
        exprD_byte uvars vars ve = Some v ->
        match
          applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match exprD_ptr uvars vars pe with
          | Some p =>
            match 
              applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate)
              with
              | None => False
              | Some pr => 
                match ST.HT.smem_set p v m with
                  | None => False
                  | Some sm' =>
                    ST.satisfies cs pr stn sm'
                end
            end
          | _ => False
        end
      }.

      Definition defaultSymEval_byte (P : ssignature btypes (tvType pcIndex) (tvType stateIndex))
        : SymEval_byte P.
      refine (
        {| sym_read_byte          := fun _ _ _ => None
         ; sym_write_byte         := fun _ _ _ _ => None
         ; sym_read_byte_correct  := _
         ; sym_write_byte_correct := _
         |}); 
      abstract (simpl; intros; congruence).
      Defined.

      Variable sfuncs : list (ssignature btypes (tvType pcIndex) (tvType stateIndex)).

      Variable known : list nat. 
      Variable evals : hlist (fun n : nat => match nth_error sfuncs n with
                                               | None => Empty_set 
                                               | Some ss => SymEval_byte ss
                                             end) known.

      Definition symeval_read_byte (hyps : list (expr btypes)) (p : expr btypes) 
        (s : SHeap btypes (tvType pcIndex) (tvType stateIndex))
        : option (expr btypes) :=
        let hyps := hyps ++ pures s in
        let reader _ seb args := 
          sym_read_byte seb hyps args p
        in
        fold_known _ _  reader (impures s) evals.

      Theorem symeval_read_byte_correct : forall cs stn hyps pe ve s uvars vars (m : B.mem),
        symeval_read_byte hyps pe s = Some ve ->
        AllProvable funcs uvars vars hyps ->
        (exists sm, 
          ST.satisfies cs (sexprD funcs sfuncs uvars vars (sheapD s)) stn sm
          /\ ST.HT.satisfies sm m) ->
        match exprD_ptr uvars vars pe , exprD_byte uvars vars ve with
          | Some p , Some v => 
            B.mem_get m p = Some v
          | _ , _ => False
        end.
      Proof.
        unfold symeval_read_byte. intros.
        eapply fold_known_correct in H.
        do 5 destruct H. destruct H1.
        intuition.

        generalize (sheapD_pures _ _ _ _ _ H); intros.

        eapply sheapD_pull_impure 
          with (funcs := funcs) (sfuncs := sfuncs) (a := uvars) (c := vars0) (cs := cs)
            in H1.
        apply In_split in H3. destruct H3. destruct H3.
        subst. rewrite starred_In in H1.

        rewrite <- heq_star_assoc in H1. rewrite heq_star_comm in H1.
        rewrite H1 in H.
        simpl in H.
        eapply ST.satisfies_star in H. destruct H. destruct H. intuition.
        rewrite H2 in *.
 
        eapply sym_read_byte_correct 
          with (uvars := uvars) (vars := vars0) (cs := cs) (stn := stn) (m := x2)
          in H6.
        2: eapply AllProvable_app; auto.
        destruct (exprD_ptr uvars vars0 pe); auto.
        destruct (exprD_byte uvars vars0 ve); auto.
        eapply ST.HT.satisfies_get. eauto.

        eapply ST.HT.split_smem_get; eauto.
        unfold tvarD.
        match goal with 
          | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
            destruct (applyD A B C D E)
        end; auto.
        eapply ST.satisfies_pure in H. PropXTac.propxFo.
      Qed.

      Definition symeval_write_byte (hyps : list (expr btypes)) (p v : expr btypes) 
        (s : SHeap btypes (tvType pcIndex) (tvType stateIndex))
        : option (SHeap btypes (tvType pcIndex) (tvType stateIndex)) :=
        let hyps := hyps ++ pures s in
        let writer _ seb args := 
          sym_write_byte seb hyps args p v
        in
        match fold_known_update _ _ writer (impures s) evals with
          | None => None
          | Some i' => Some {| impures := i' ; pures := pures s ; other := other s |}
        end.

      Theorem symeval_write_byte_correct : forall cs stn hyps pe ve v s s' uvars vars (m : B.mem),
        symeval_write_byte hyps pe ve s = Some s' ->
        AllProvable funcs uvars vars hyps ->
        exprD_byte uvars vars ve = Some v ->
        (exists sm, 
             ST.satisfies cs (sexprD funcs sfuncs uvars vars (sheapD s)) stn sm
          /\ ST.HT.satisfies sm m) ->
        match exprD_ptr uvars vars pe with
          | Some p =>
            exists sm, 
              ST.satisfies cs (sexprD funcs sfuncs uvars vars (sheapD s')) stn sm
              /\ ST.HT.satisfies sm (B.mem_set m p v)
          | _ => False
        end.
      Proof.
        unfold symeval_write_byte. intros.
        generalize dependent H.
        match goal with
          | [ |- context [ fold_known_update ?A ?B ?C ?D ?E ] ] =>
            case_eq (fold_known_update A B C D E); intros; try congruence
        end.
        eapply fold_known_update_correct in H.
        do 5 destruct H. destruct H2.
        intuition. inversion H3; clear H3; subst. 
        
        eapply fold_args_update_correct in H6.
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
               end. intuition; subst.
        generalize (sheapD_pures _ _ _ _ _ H4).
        rewrite sheapD_pull_impure in H4 by eauto.
        rewrite starred_In in H4.
        rewrite <- heq_star_assoc in H4. rewrite heq_star_comm in H4.
        
        simpl in *. rewrite H2 in *.
        intros.

        eapply ST.satisfies_star in H4. do 2 destruct H4. intuition.

        eapply sym_write_byte_correct with (stn := stn) (cs := cs) (m := x2)
          in H3; eauto.

        2: apply AllProvable_app; eauto.

        destruct (exprD_ptr uvars vars0 pe); eauto.
        unfold tvarD in H3.

        generalize dependent H3.
        case_eq (ST.HT.smem_set a v x2); [ intros |
          match goal with 
            | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
              destruct (applyD A B C D E); intros; exfalso; assumption
          end ].
        
        exists (ST.HT.join s0 x3).
        rewrite sheapD_pull_impure by eapply FM.find_add.
        simpl. rewrite FM.remove_add.
        rewrite starred_In.
        simpl. rewrite H2. generalize dependent H8. 
        rewrite <- ST.heq_star_assoc. rewrite ST.heq_star_comm. 
        match goal with
          | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
            destruct (applyD A B C D E); try solve [ intros; intuition ]
        end. 
        generalize dependent H9.
        match goal with
          | [ |- ST.satisfies _ ?Y _ _ -> _ -> ST.satisfies _ (ST.star _ ?X) _ _ /\ _ ] => 
            change X with Y; generalize dependent Y
        end.
        intros.

        generalize (ST.HT.split_set _ _ (proj1 H7) _ _ _ H3).
        split.
        eapply ST.satisfies_star. do 2 eexists. split; eauto. eapply ST.HT.disjoint_split_join; eauto. tauto.

        eapply ST.HT.satisfies_set. eauto. destruct H7; subst. tauto.

        unfold tvarD. generalize dependent H4.
        match goal with
          | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
            destruct (applyD A B C D E); try solve [ intros; intuition ]
        end. intros.
        eapply ST.satisfies_pure in H4. PropXTac.propxFo.
      Qed.
    End ByteAccess.

    (** * Words *)
    Section WordAccess.
      Variable wordIndex : nat.
      Definition wordType : type :=
        {| Impl := W
          ; Eq := fun x y => match weq x y with
                               | left pf => Some pf
                               | _ => None
                             end
        |}.

      Hypothesis word_ptr : wordIndex <> ptrIndex.

      Definition wtypes := 
        updatePosition ptrIndex ptrType (updatePosition wordIndex wordType types').

      Lemma ptrType_get_w : tvarD wtypes (tvType ptrIndex) = B.addr.
        unfold wtypes, tvarD. rewrite updatePosition_eq. reflexivity.
      Defined.

      Definition exprD_ptr_w funcs (uvars vars : env wtypes)
        (e : expr wtypes) : option B.addr :=
        match ptrType_get_w in _ = t return option t with
          | refl_equal => exprD funcs uvars vars e (tvType ptrIndex)
        end.

      Lemma wordType_get_w : tvarD wtypes (tvType wordIndex) = W.
        unfold wtypes, tvarD. rewrite updatePosition_neq; auto;
        rewrite updatePosition_eq; auto. congruence.
      Defined.

      Definition exprD_word funcs (uvars vars : env wtypes)
        (e : expr wtypes) : option W :=
        match wordType_get_w in _ = t return option t with
          | refl_equal => exprD funcs uvars vars e (tvType wordIndex)
        end.

      Variable funcsT : functions wtypes -> functions wtypes.

      Record SymEval_word (Predicate : ssignature wtypes (tvType pcIndex) (tvType stateIndex))
        : Type :=
      { sym_read_word  : 
        forall (hyps args : list (expr wtypes)) (p : expr wtypes), option (expr wtypes)
      ; sym_write_word : 
        forall (hyps args : list (expr wtypes)) (p v : expr wtypes),
        option (list (expr wtypes))
      ; sym_read_word_correct : forall funcs args uvars vars cs hyps pe ve m stn,
        sym_read_word hyps args pe = Some ve ->
        AllProvable (funcsT funcs) uvars vars hyps ->
        match 
          applyD (exprD (funcsT funcs) uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match 
          exprD_ptr_w (funcsT funcs) uvars vars pe , 
          exprD_word (funcsT funcs) uvars vars ve
          with
          | Some p , Some v =>
            ST.HT.smem_get_word (IL.implode stn) p m = Some v
          | _ , _ => False
        end
      ; sym_write_word_correct : forall funcs args uvars vars cs hyps pe ve v m stn args',
        sym_write_word hyps args pe ve = Some args' ->
        AllProvable (funcsT funcs) uvars vars hyps ->
        exprD_word (funcsT funcs) uvars vars ve = Some v ->
        match
          applyD (@exprD _ (funcsT funcs) uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
          with
          | None => False
          | Some p => ST.satisfies cs p stn m
        end ->
        match exprD_ptr_w (funcsT funcs) uvars vars pe with
          | Some p =>
            match 
              applyD (@exprD _ (funcsT funcs) uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate)
              with
              | None => False
              | Some pr => 
                match ST.HT.smem_set_word (IL.explode stn) p v m with
                  | None => False
                  | Some sm' => ST.satisfies cs pr stn sm'
                end
            end
          | _ => False
        end
      }.

      Definition defaultSymEval_word (P : ssignature wtypes (tvType pcIndex) (tvType stateIndex))
        : SymEval_word P.
      refine (
        {| sym_read_word          := fun _ _ _ => None
         ; sym_write_word         := fun _ _ _ _ => None
         ; sym_read_word_correct  := _
         ; sym_write_word_correct := _
        |}); 
      abstract (simpl; intros; congruence).
      Defined.

      (** * The full tactic *)
      Variable sfuncs : list (ssignature wtypes (tvType pcIndex) (tvType stateIndex)).

      Variable known : list nat. 
      Variable evals : hlist (fun n : nat => match nth_error sfuncs n with
                                               | None => Empty_set 
                                               | Some ss => SymEval_word ss
                                             end) known.

      Definition symeval_read_word (hyps : list (expr wtypes)) (p : expr wtypes) 
        (s : SHeap wtypes (tvType pcIndex) (tvType stateIndex))
        : option (expr wtypes) :=
        let hyps := hyps ++ pures s in
        let reader ss (seb : SymEval_word ss) args := 
          sym_read_word seb hyps args p
        in
        fold_known _ _ reader (impures s) evals.

      Theorem symeval_read_word_correct : forall hyps pe s ve, 
        symeval_read_word hyps pe s = Some ve ->
        forall funcs cs stn uvars vars m,
        AllProvable (funcsT funcs) uvars vars hyps ->
        (exists sm, 
             ST.satisfies cs (sexprD (funcsT funcs) sfuncs uvars vars (sheapD s)) stn sm
          /\ ST.HT.satisfies sm m) ->
        match 
          exprD_ptr_w (funcsT funcs) uvars vars pe ,
          exprD_word (funcsT funcs) uvars vars ve
          with
          | Some p , Some v => 
            mem_get_word B.addr B.mem B.footprint_w B.mem_get (IL.implode stn) p m = Some v
          | _ , _ => False
        end.
      Proof.
        unfold symeval_read_word. intros.
        eapply fold_known_correct in H.
        do 5 destruct H. destruct H1.
        intuition.

        generalize (sheapD_pures _ _ _ _ _ H); intros.

        eapply sheapD_pull_impure 
          with (sfuncs := sfuncs) (a := uvars) (c := vars0) (cs := cs)
            in H1.
        apply In_split in H3. destruct H3. destruct H3.
        subst. rewrite starred_In in H1.

        rewrite <- heq_star_assoc in H1. rewrite heq_star_comm in H1.
        rewrite H1 in H.
        simpl in H.
        eapply ST.satisfies_star in H. destruct H. destruct H. intuition.
        rewrite H2 in *.
 
        eapply sym_read_word_correct 
          with (uvars := uvars) (vars := vars0) (cs := cs) (stn := stn) (m := x2)
          in H6.
        2: eapply AllProvable_app; eauto.
        destruct (exprD_ptr_w (funcsT funcs) uvars vars0 pe); auto.
        destruct (exprD_word (funcsT funcs) uvars vars0 ve); auto.
        eapply ST.HT.satisfies_get_word. eauto.

        eapply ST.HT.split_smem_get_word; eauto.
        unfold tvarD.
        match goal with 
          | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
            destruct (applyD A B C D E)
        end; auto.
        eapply ST.satisfies_pure in H. PropXTac.propxFo.
      Qed.

      Definition symeval_write_word (hyps : list (expr wtypes)) (p v : expr wtypes) 
        (s : SHeap wtypes (tvType pcIndex) (tvType stateIndex))
        : option (SHeap wtypes (tvType pcIndex) (tvType stateIndex)) :=
        let hyps := hyps ++ pures s in
        let writer _ seb args := 
          sym_write_word seb hyps args p v
        in
        match fold_known_update _ _ writer (impures s) evals with
          | None => None
          | Some i' => Some {| impures := i' ; pures := pures s ; other := other s |}
        end.

      Theorem symeval_write_word_correct : forall funcs hyps pe ve s s',
        symeval_write_word hyps pe ve s = Some s' ->
        forall cs stn uvars vars m v,
        AllProvable (funcsT funcs) uvars vars hyps ->
        exprD_word (funcsT funcs) uvars vars ve = Some v ->
        (exists sm, 
             ST.satisfies cs (sexprD (funcsT funcs) sfuncs uvars vars (sheapD s)) stn sm
          /\ ST.HT.satisfies sm m) ->
        match exprD_ptr_w (funcsT funcs) uvars vars pe with
          | Some p =>
            exists sm, 
                 ST.satisfies cs (sexprD (funcsT funcs) sfuncs uvars vars (sheapD s')) stn sm
              /\ ST.HT.satisfies sm (mem_set_word B.addr B.mem B.footprint_w B.mem_set (IL.explode stn) p v m)
          | _ => False
        end.
      Proof.
        unfold symeval_write_word. intros.
        generalize dependent H.
        match goal with
          | [ |- context [ fold_known_update ?A ?B ?C ?D ?E ] ] =>
            case_eq (fold_known_update A B C D E); intros; try congruence
        end.
        eapply fold_known_update_correct in H.
        do 5 destruct H. destruct H2.
        intuition. inversion H3; clear H3; subst. 
        
        eapply fold_args_update_correct in H6.
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
               end. intuition; subst.
        generalize (sheapD_pures _ _ _ _ _ H4).
        rewrite sheapD_pull_impure in H4 by eauto.
        rewrite starred_In in H4.
        rewrite <- heq_star_assoc in H4. rewrite heq_star_comm in H4.
        
        simpl in *. rewrite H2 in *.
        intros.

        eapply ST.satisfies_star in H4. do 2 destruct H4. intuition.

        eapply sym_write_word_correct with (stn := stn) (cs := cs) (m := x2)
          in H3; eauto.

        2: apply AllProvable_app; eauto.

        destruct (exprD_ptr_w (funcsT funcs) uvars vars0 pe); eauto.
        unfold tvarD in H3.

        generalize dependent H3.
        case_eq (ST.HT.smem_set_word (IL.explode stn) a v x2); [ intros |
          match goal with 
            | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
              destruct (applyD A B C D E); intros; exfalso; assumption
          end ].
        
        exists (ST.HT.join s0 x3).
        rewrite sheapD_pull_impure by eapply FM.find_add.
        simpl. rewrite FM.remove_add.
        rewrite starred_In.
        simpl. rewrite H2. generalize dependent H8. 
        rewrite <- ST.heq_star_assoc. rewrite ST.heq_star_comm. 
        match goal with
          | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
            destruct (applyD A B C D E); try solve [ intros; intuition ]
        end. 
        generalize dependent H9.
        match goal with
          | [ |- ST.satisfies _ ?Y _ _ -> _ -> ST.satisfies _ (ST.star _ ?X) _ _ /\ _ ] => 
            change X with Y; generalize dependent Y
        end.
        intros.

        generalize (ST.HT.split_set_word _ _ (proj1 H7) _ _ _ _ H3).
        split.
        eapply ST.satisfies_star. do 2 eexists. split; eauto. eapply ST.HT.disjoint_split_join; eauto. tauto.

        eapply ST.HT.satisfies_set_word. eauto. destruct H7; subst. tauto.

        unfold tvarD. generalize dependent H4.
        match goal with
          | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
            destruct (applyD A B C D E); try solve [ intros; intuition ]
        end. intros.
        eapply ST.satisfies_pure in H4. PropXTac.propxFo.
      Qed.

    End WordAccess.
  End typed.
End Evaluator.
*)
(*
Require Import SepIL Bedrock.SepTac.

Module BedrockEvaluator_ptsto.
  Module E := EvaluatorPlugin (BedrockHeap) (ST).

  

Module BedrockEvaluator.
  Module E := EvaluatorPlugin (BedrockHeap) (ST).
  Module Import SEP := E.SEP.

  Definition pcIndex : nat := 0.
  Definition stateIndex : nat := 1.
  
  Definition addr_type :=
    {| Impl := W
     ; Eq := seq_dec 
     |}.

  Definition word_type :=
    {| Impl := W
     ; Eq := seq_dec 
     |}.

  Definition wtypes := bedrock_types ++ addr_type :: word_type :: nil.

  Definition ptsto32_ssig : ssignature wtypes (tvType pcIndex) (tvType stateIndex).
  refine (
  {| SepExpr.SDomain := tvType 2 :: tvType 3 :: nil
   ; SepExpr.SDenotation := _
   |}).
  refine (ptsto32 _).
  Defined.

  Definition wordIndex := 3.
  Definition ptrIndex := 2.
  Lemma wordIndex_ptrIndex : wordIndex <> ptrIndex.
    intro. inversion H.
  Qed.

  Variable funcs : functions wtypes.

  (** TODO: maybe this should be like unification? 
   ** - in that case the substitution is an effect and needs to be
   **   threaded through the computation (monadically?)
   **)
  Variable expr_equal : forall (hyps : list (expr wtypes)) (tv : tvar) (a b : expr wtypes), bool.

  Definition sym_read_word_ptsto32 (hyps args : list (expr wtypes)) (p : expr wtypes) 
    : option (expr wtypes) :=
    match args with
      | p' :: v' :: nil => 
        if expr_equal hyps (tvType ptrIndex) p p' then Some v' else None
      | _ => None
    end.
  Definition sym_write_word_ptsto32 (hyps args : list (expr wtypes)) (p v : expr wtypes)
    : option (list (expr wtypes)) :=
    match args with
      | p' :: v' :: nil =>
        if expr_equal hyps (tvType ptrIndex) p p' then Some (p :: v :: nil) else None
      | _ => None
    end.

  Variable expr_equal_correct : forall T hyps a b,
    expr_equal hyps T a b = true ->
    forall uvars vars,
    AllProvable funcs uvars vars hyps ->
    exprD funcs uvars vars a T = exprD funcs uvars vars b T.

  Ltac expose :=
    repeat (unfold wordIndex, ptrIndex in *; 
            match goal with 
              | [ H : match applyD _ _ ?A _ _ with
                        | Some _ => _ 
                        | None => False 
                      end |- _ ] =>
              destruct A; simpl in H; try (exfalso; assumption)
              | [ H : match 
                        match exprD ?A ?B ?C ?D ?E with
                          | None => _
                          | Some _ => _
                        end _ _ 
                        with 
                        | None => _
                        | Some _ => _
                      end |- _ ] =>
              generalize dependent H; case_eq (exprD A B C D E); simpl; intros; 
                try (exfalso; assumption)
              | [ H : context [ match expr_equal ?A ?B ?C ?D with
                                  | true => _
                                  | false => _
                                end ] |- _ ] =>
                generalize dependent H; case_eq (expr_equal A B C D); intros; 
                  try (exfalso; congruence)
              | [ H : expr_equal ?A ?B ?C ?D = true 
                , H' : AllProvable _ _ _ ?A |- _ ] =>
                generalize (@expr_equal_correct _ _ _ _ H _ _ H'); clear H; intros
              | [ H : Some _ = Some _ |- _ ] =>
                inversion H; clear H; subst
              | [ H : exprD _ _ _ _ _ = Some _ |- _ ] =>
                rewrite H in *
            end; simpl in * ).

  Lemma sym_read_word_ptsto32_correct : forall args uvars vars cs hyps pe ve m stn,
    sym_read_word_ptsto32 hyps args pe = Some ve ->
    AllProvable funcs uvars vars hyps ->
    match 
      applyD (exprD funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars pe (tvType ptrIndex) , exprD funcs uvars vars ve (tvType wordIndex) with
      | Some p , Some v =>
        ST.HT.smem_get_word (IL.implode stn) p m = Some v
      | _ , _ => False
    end.
  Proof.
    simpl; intros; expose.
    unfold ST.satisfies in H3. PropXTac.propxFo.
  Qed.

  Lemma sym_write_word_ptsto32_correct : forall args uvars vars cs hyps pe ve v m stn args',
    sym_write_word_ptsto32 hyps args pe ve = Some args' ->
    AllProvable funcs uvars vars hyps ->
    exprD funcs uvars vars ve (tvType wordIndex) = Some v ->
    match
      applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars pe (tvType ptrIndex)with
      | Some p =>
        match 
          applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args' _ (SDenotation ptsto32_ssig)
          with
          | None => False
          | Some pr => 
            match ST.HT.smem_set_word (IL.explode stn) p v m with
              | None => False
              | Some sm' => ST.satisfies cs pr stn sm'
            end
        end
      | _ => False
    end.
  Proof.
    simpl; intros; expose.

    unfold ST.satisfies in *. PropXTac.propxFo. 
    case_eq (smem_set_word (IL.explode stn) t v m).
    intros. unfold ptsto32. PropXTac.propxFo.
    eapply smem_set_get_word_eq; eauto.
    eapply IL.implode_explode.
    eapply smem_set_get_valid_word; eauto.
  Qed.

  Definition SymEval_ptsto32 : E.SymEval_word wtypes wordIndex_ptrIndex funcs ptsto32_ssig :=
    {| E.sym_read_word := sym_read_word_ptsto32 : list (expr (E.wtypes wtypes ptrIndex wordIndex)) -> _
     ; E.sym_write_word := sym_write_word_ptsto32 
     ; E.sym_read_word_correct := sym_read_word_ptsto32_correct
     ; E.sym_write_word_correct := sym_write_word_ptsto32_correct
     |}.

End BedrockEvaluator.
*)
