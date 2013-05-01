Require Import AutoSep Ascii Wrap.

Set Implicit Arguments.

Definition W_of_ascii (ch : ascii) : W := N_of_ascii ch.
Coercion W_of_ascii : ascii >-> W.

(** Derived command to check whether a string matches a constant. *)


Section StringEq.
  Variables str len pos output : string.
  Variable const : string.

  Variable A : Type. (* Type for a single unified [Al] quantifier in the block spec *)
  Variable precondition : A -> vals -> HProp.
  Variable postcondition : A -> vals -> W -> HProp.

  Fixpoint StringEq' (const : string) (offset : nat) : chunk :=
    match const with
      | "" => output <- 1
      | String ch const' =>
        Rp <- pos + offset;;
        Rp <-*8 str + Rp;;
        If (Rp = ch) {
          StringEq' const' (S offset)
        } else {
          output <- 0
        }
    end%SP.

  Lemma himp_refl : forall specs (P Q : HProp),
    P = Q
    -> himp specs P Q.
    intros; subst; reflexivity.
  Qed.

  Hint Extern 1 (himp _ _ _) =>
    try (apply himp_star_frame; try reflexivity);
    apply himp_refl;
      match goal with
        | [ H : _ |- _ ] => apply H
      end; intros; autorewrite with sepFormula; reflexivity.

  Lemma precondition_sel : forall a V, precondition a (sel V) = precondition a V.
    auto.
  Qed.

  Lemma postcondition_sel : forall a V, postcondition a (sel V) = postcondition a V.
    auto.
  Qed.

  Hint Rewrite precondition_sel postcondition_sel : sepFormula.

  Definition StringEqSpec' (const : string) (offset : nat) :=
    Al bs, Al x : A,
    PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |]
      * [| wordToNat (V pos) + offset + String.length const <= wordToNat (V len) |]%nat
    POST[R] postcondition x V R.

  Lemma bound_narrow : forall len (len' : W) pos offset spacing,
    len = wordToNat len'
    -> (wordToNat pos + offset + S spacing <= wordToNat len')%nat
    -> pos ^+ natToW offset < natToW len.
    intros; subst; unfold natToW; rewrite natToWord_wordToNat; auto.
    pre_nomega.
    rewrite wordToNat_wplus.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize offset); eapply goodSize_weaken; eauto.
    instantiate (1 := len'); auto.
    eapply goodSize_weaken; eauto.
    rewrite wordToNat_natToWord_idempotent; auto.
    instantiate (1 := len'); auto.
    change (goodSize offset); eapply goodSize_weaken; eauto.
    instantiate (1 := len'); auto.
  Qed.
  
  Implicit Arguments bound_narrow [len len' pos offset spacing].

  Ltac evalu :=
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => generalize dependent H
           end;
    evaluate auto_ext; intros;
    try match goal with
          | [ H : length _ = wordToNat _, H' : (_ <= _)%nat |- _ ] => specialize (bound_narrow H H'); intro
        end;
    evaluate auto_ext; intros;
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
           end;
    try match goal with
          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
        end.

  Ltac t := try app; simp; handle_IH; evalu; finish.

  Notation StringEqVcs := (fun _ ns _ => (~In "rp" ns) :: In str ns :: In len ns :: In pos ns :: In output ns
    :: not (str = len) :: not (str = pos) :: not (str = output)
    :: not (len = pos) :: not (len = output)
    :: not (pos = output)
    :: (forall a V V',
      (forall x, x <> output -> sel V x = sel V' x)
      -> precondition a V = precondition a V')
    :: (forall a V V' r,
      (forall x, x <> output -> sel V x = sel V' x)
      -> postcondition a V r = postcondition a V' r)
    :: nil).

  Definition StringEq'' (offset : nat) : chunk.
    refine (WrapC (StringEq' const offset)
      (StringEqSpec' const offset)
      (StringEqSpec' const offset)
      StringEqVcs
      _ _); [
        abstract (wrap0; generalize dependent offset; generalize dependent st; generalize dependent pre;
          induction const;
            (propxFo;
              match goal with
                | [ _ : interp _ (Postcondition _ _) |- _ ] =>
                  app; [ post; handle_IH; finish
                    | post; t ]
                | _ => t
              end))
        | abstract (generalize dependent offset; induction const; wrap0;
          try match goal with
                | [ H : _ |- vcs _ ] => apply H; wrap0; post
              end; t) ].
  Defined.

  Definition StringEqSpec :=
    Al bs, Al x : A,
    PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |]
      * [| wordToNat (V pos) + String.length const <= wordToNat (V len) |]%nat
    POST[R] postcondition x V R.

  Definition StringEq : chunk.
    refine (WrapC (StringEq'' O)
      StringEqSpec
      StringEqSpec
      StringEqVcs
      _ _); abstract (wrap0; try app; simp; handle_IH; finish).
  Defined.

End StringEq.
