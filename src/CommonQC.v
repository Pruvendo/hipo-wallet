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

Require Import UrsusEnvironment.Solidity.current.Environment.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Common.
Require Import HipoWallet.
Import HipoWallet.

Import MonadNotation.
Open Scope monad_scope.

Require Import UrsusQC.CommonQCEnvironment.
Require Import UrsusQC.VMStateGenerator.

Extract Constant defNumTests => "10".

#[global]
Instance IDefault_booleq : XBoolEquable bool IDefault := {
    eqb _ _ := true
}.

#[global]
Instance Ledger_Shrink : Shrink (LedgerLRecord rec) := {
    shrink l := Datatypes.nil : Datatypes.list (LedgerLRecord rec)
}.

Notation " f '::>' g" := 
    ((_ : EmbeddedType f (@field_type f _ _ g))) 
    (at level 20, only parsing, left associativity).
Notation "f ':>' g" := 
    ((@TransEmbedded _ _ (@field_type _ _ _ g) f (_ : EmbeddedType _ (@field_type _ _ _ g)))) 
    (at level 21, only parsing, left associativity).

(* set *)
Notation "r '<--' v 'with' et":= (@injEmbed _ _ et v r) (at level 22, only parsing).

(* get *)
Notation "'-->' r 'with' et":= (@projEmbed _ _ et r) (at level 22, only parsing).

Definition Contract := LedgerLRecord rec ::> Ledger_MainState. 
Definition Parent := Contract :> _parent.
Definition Owner := Contract :> _owner.
Definition Unstaking := Contract :> _unstaking.
Definition Tokens := Contract :> _tokens.

Definition with_positive_int
    {n : N}
    (et : EmbeddedType (LedgerLRecord rec) (XBInteger n))
    (l : LedgerLRecord rec) : G (LedgerLRecord rec) :=
        let v := --> l with et in
        let positive := if (xIntGeb v 0%Z) then v else (xIntMult ((-1)%Z : XBInteger n) v) in
        ret (l <-- positive with et).

Definition pack_slice (f : TvmBuilder -> option TvmBuilder) : TvmSlice :=
    xMaybeMapDefault
        builder_to_slice_
        (f (Wrap_TvmBuilder EmptyPrecell))
        default.

Definition pack_address (addr : address) : TvmSlice := pack_slice (fun x => builder_store_ x addr).

Definition with_slice_address_sized
    (et : EmbeddedType (LedgerLRecord rec) TvmSlice)
    (size : nat)
    (l : LedgerLRecord rec) : G (LedgerLRecord rec) :=
        addr <- (arbitrarySized size : G address) ;;
        let slice_address := pack_address addr in
        ret (l <-- slice_address with et).

Definition ledger_gen_sized (size : nat) : G (LedgerLRecord rec) :=
    arbitrarySized size
        >>= with_positive_int Unstaking
        >>= with_positive_int Tokens
        >>= with_slice_address_sized Parent size
        >>= with_slice_address_sized Owner size.

#[global]
Instance Ledger_GenSized : GenSized (LedgerLRecord rec) := {
    arbitrarySized size := ledger_gen_sized size
}.
