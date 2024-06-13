Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Logic.FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.Common. 
Require Import FinProof.Lib.BoolEq.
Require Import FinProof.MonadTransformers21.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Solidity.stdTypes.

Require Import UrsusTVM.Solidity.tvmTypes.
Require Import UrsusTVM.Solidity.tvmFunc.
Require Import UrsusTVM.Solidity.tvmNotations.
Require Import UrsusTVM.Solidity.tvmCells.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import UrsusQC.CommonQCEnvironment.

Extract Constant defNumTests => "10".

#[global]
Instance IDefault_booleq : XBoolEquable bool IDefault := {
    eqb _ _ := true
}.


(* Import MonadNotation.
Open Scope monad_scope.

#[global]
Instance Prod_gensized : Gen (prod nat nat) := {
    arbitrary :=
        a <- (arbitrary : G nat) ;;
        b <- (arbitrary : G nat) ;;
        if (a =? b)%nat then ret (a, b + 1) else ret (a, b)
}.

Definition prop1 (p : nat * nat) : Prop := Nat.eqb (fst p) (snd p) = false.

Require Import UrsusQC.ConvertPropToChecker.

ConvertPropToChecker prop1.
QuickCheck prop1_QC. *)
