Set Implicit Arguments.

Require Import StringSet.
Require Import Equalities.
Module K := Make_UDT StringKey.
Module M := StringSet.
Require Import FSetProperties.
Include (Properties M).
Require Import FSetFacts.
Include (Facts M).
Require Import FSetFacts1.
Module Include bug_4066_workaround := UWFacts_fun K M.
