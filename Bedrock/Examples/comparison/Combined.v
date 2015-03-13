Require Import Bedrock.Examples.AutoSep Bedrock.Examples.Malloc Bedrock.Examples.comparison.Server.


Definition program := link mallocM m.

Theorem closed : Imports program = LabelMap.empty _.
Proof using .
  reflexivity.
Qed.

Theorem ok : moduleOk program.
Proof using .
  link mallocMOk ok.
Qed.

Require Import Bedrock.AMD64_gas.

Definition compiled := moduleS program.
Unset Extraction AccessOpaque.  Recursive Extraction compiled.
