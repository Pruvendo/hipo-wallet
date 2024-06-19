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

Definition max_key_with_default
    {K V : Type}
    `{XDefault K}
    `{XOrdered bool K}
    (map : mapping K V)
    : K :=
        xMaybeMapDefault (fun x => x) (xHMapMaxKey map) default.

Definition map_next_key_gen
    {n : N}
    {V : Type}
    (map : mapping (XUBInteger n) V)
    (size : nat)
    : G (XUBInteger n) :=
        let max_key := max_key_with_default map in
            d <- (arbitrarySized size : G (XUBInteger n)) ;;
            ret (xIntPlus max_key (xIntPlus d xInt1)).

Definition mapping_gen_sized 
  {K V : Type}
  (gk : G K)
  (gv : G V)
  (eq_dec : forall k1 k2 : K, {k1 = k2} + {k1 <> k2})
  (size : nat)
  : G (mapping K V) :=
    mapping_size <- ((arbitrarySized size) : G nat) ;;
    keys <- vectorOf mapping_size gk ;;
    values <- vectorOf mapping_size gv ;;
    let keys' := nodup eq_dec keys in
      @ret G _ _ (xHMapFromList (combine keys' values)) : G (mapping K V).
    
Definition non_empty_map_gen
  {n : N}
  {V : Type}
  (gv : G V)
  (size : nat)
  : G (mapping (XUBInteger n) V) := 
    element <- gv ;;
    map <- ((mapping_gen_sized (arbitrarySized size) gv uint_eq_dec size) : G (mapping (XUBInteger n) V)) ;;
    id <- (map_next_key_gen map size : G (XUBInteger n)) ;;
    ret
      (let (ids, elements) := split (xHMapToList map) in
        xHMapFromList (combine 
                      (nodup uint_eq_dec (id :: ids)) 
                      (element :: elements))).

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
Definition Staking := Contract :> _staking.

Definition with_positive_int
    {n : N}
    (et : EmbeddedType (LedgerLRecord rec) (XBInteger n))
    (l : LedgerLRecord rec) : G (LedgerLRecord rec) :=
        let v := --> l with et in
        let positive := if (xIntGeb v 0%Z) then v else (xIntMult ((-1)%Z : XBInteger n) v) in
        ret (l <-- positive with et).

Definition store_builder_ {A : Type} `{SolTypable A} (a : A) (b : TvmBuilder) := builder_store_ b a.

Definition pack_builder (f : TvmBuilder -> option TvmBuilder) : TvmBuilder :=
    xMaybeMapDefault id (f (Wrap_TvmBuilder EmptyPrecell)) default.

Definition pack_slice (f : TvmBuilder -> option TvmBuilder) : TvmSlice :=
    xMaybeMapDefault
        builder_to_slice_
        (f (Wrap_TvmBuilder EmptyPrecell))
        default.

Definition pack_cell (f : TvmBuilder -> option TvmBuilder) : TvmCell :=
    xMaybeMapDefault
        builder_to_cell_
        (f (Wrap_TvmBuilder EmptyPrecell))
        default.

Definition pack_slice_address (addr : address) : TvmSlice := pack_slice (store_builder_ addr).

Definition with_slice_address_sized
    (et : EmbeddedType (LedgerLRecord rec) TvmSlice)
    (size : nat)
    (l : LedgerLRecord rec) : G (LedgerLRecord rec) :=
        addr <- (arbitrarySized size : G address) ;;
        let slice_address := pack_slice_address addr in
        ret (l <-- slice_address with et).

Definition with_bool
    (et : EmbeddedType (LedgerLRecord rec) bool)
    (l : LedgerLRecord rec) : G (LedgerLRecord rec) :=
        ret (l <-- false with et).

Definition cell_uint256_gen_sized (size : nat) : G (TvmCell) :=
    v <- (arbitrarySized size : G uint256) ;;
    ret (pack_cell (store_builder_ v)). 

Definition mapping_uint32_cell_gen_sized (size : nat) : G (mapping uint32 TvmCell) :=
    non_empty_map_gen (cell_uint256_gen_sized size) size.

Definition with_staking (size : nat) (l : LedgerLRecord rec) : G (LedgerLRecord rec) :=
    m <- mapping_uint32_cell_gen_sized size ;;
    ret (l <-- (pack_cell (store_builder_ m)) with Staking).

Definition ledger_gen_sized (size : nat) : G (LedgerLRecord rec) :=
    arbitrarySized size
        >>= with_positive_int Unstaking
        >>= with_positive_int Tokens
        >>= with_slice_address_sized Parent size
        >>= with_slice_address_sized Owner size
        >>= with_staking size.

Sample (with_staking 0 default).

#[global]
Instance Ledger_GenSized : GenSized (LedgerLRecord rec) := {
    arbitrarySized size := ledger_gen_sized size
}.
