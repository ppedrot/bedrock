Module A.

  Definition t := nat.

End A.

Module B.

  Include A.

End B.

Lemma e : A.t = B.t.
Proof using .
  eauto.
Qed.
