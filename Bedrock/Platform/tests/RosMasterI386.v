Require Import Bedrock.Bedrock Bedrock.Platform.tests.RosMasterDriver Bedrock.I386_gas.

Definition compiled := moduleS E.m.
Unset Extraction AccessOpaque.  Recursive Extraction compiled.
