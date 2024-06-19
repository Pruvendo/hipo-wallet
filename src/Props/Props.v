Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import Common.
Require Import CommonQC.
Require Import UrsusQC.ConvertPropToChecker.
Require Import UrsusQC.CreateDiagnostics.
Require Import HipoWallet.
Import HipoWallet.

Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Structures.Monad.
Import QuickChick.

Import MonadNotation.
Open Scope monad_scope.

Definition slice_decode_with_default (A : Type) `{SolTypable A} `{XDefault A} (slice : TvmSlice) : A :=
    xMaybeMapDefault fst (slice_decode_ A slice) default.

Definition cell_decode_with_default (A : Type) `{SolTypable A} `{XDefault A} (cell : TvmCell) : A :=
    xMaybeMapDefault fst (slice_decode_ A (cell_to_slice_ cell)) default.

Definition cr_get_or_default {b : bool} {A : Type} `{XDefault A} (cr : ExecGenDefs.ControlResult A b) : A.
destruct cr; [exact a | | |].
all: exact(default).
Defined.

Definition uint32_to_int256 (n : uint32) : int256.
destruct n.
constructor.
exact (Z.of_N n).
Defined.


Definition pack_slice_save_coins (query_id: int64)
(coins :int256)
(round_since : int32) : TvmSlice :=
    (Wrap_TvmSlice
            (precell_push
                (precell_push
                    (precell_push 
                        EmptyPrecell 
                        (pack_sized 64 (query_id : int64)))
                    (pack_sized 256 (coins : int256)))
                (pack_sized 32 (round_since : int32)))).

Definition pack_slice_tokens_minted
(query_id: uint64)
(amount :int256)
(coins :uint256)
(addr :address)
(round_since : uint32) : TvmSlice :=
    pack_slice
        (store_builder_ query_id >=>
        store_builder_ amount >=>
        store_builder_ coins >=>
        store_builder_ addr >=>
        store_builder_ round_since).

(* (xMaybeMapDefault builder_to_slice_ (
        
builder_store_  (        
        xMaybeMapDefault  Datatypes.id  (builder_store_  (Wrap_TvmBuilder EmptyPrecell) query_id) default) 
                 amount  ) default).
 *)   

Definition pack_slice_unstake_tokens (query_id: int64)
(amount :int256)
(return_excess : int256)  (*address*)
(custom_payload : int256) (*TVMSlice*)
: TvmSlice :=
    (Wrap_TvmSlice
            (precell_push
                (precell_push
                (precell_push
                    (precell_push 
                        EmptyPrecell 
                        (pack_sized 64 (query_id : int64)))
                    (pack_sized 256 (amount : int256)))
                    (pack_sized 256 (return_excess : int256))) (*address*)
                    (pack_sized 256 (custom_payload : int256)))). (*TVMSliace*)


Definition pack_slice_tokens_burned (query_id: int64)
(amount: int256)
(coins :int256) : TvmSlice :=
    (Wrap_TvmSlice
            (precell_push
                (precell_push
                    (precell_push 
                        EmptyPrecell 
                        (pack_sized 64 (query_id : int64)))
                    (pack_sized 256 (amount : int256)))
                (pack_sized 256 (coins : int256)))).
Definition TBO3_def
(query_id: int64)
 (amount: int256)
 (coins :int256)
 (l: LedgerLRecord rec): Prop.
 elpi read_fields(l) "parent".
(*   set (src' :=  xMaybeMapDefault fst  (slice_decode_ (mapping int32 int256) parent)  default).
 *)  set (s:= pack_slice_tokens_burned query_id amount coins).
  add_computation (l) (tokens_burned rec def parent s).
 elpi read_fields(l) "unstaking".
 elpi read_fields(l') "unstaking".
 condition (xIntGeb unstaking 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (tokens_burned rec def parent s)) l) = false).
 conclusion (unstaking' = xIntMinus unstaking amount).
Defined.

(* works *)
(* ConvertPropToChecker TBO3_def.
QuickCheck TBO3_def_QC. *)

Definition UTO3_def
 (src:TvmSlice)(query_id: int64)
 (amount :int256)
 (return_excess : int256)  (*address*)
 (custom_payload : int256)
 (l: LedgerLRecord rec): Prop.
 set (s:= pack_slice_unstake_tokens query_id amount return_excess custom_payload).
 add_computation (l) (unstake_tokens rec def src s).
 elpi read_fields(l) "tokens".
 elpi read_fields(l') "tokens".
 condition (xIntGeb tokens 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (unstake_tokens rec def src s)) l) = false).
 conclusion (tokens' = xIntMinus tokens amount).
Defined.

Definition UTO4_def
 (src:TvmSlice)(query_id: int64)
 (amount :int256)
 (return_excess : int256)  (*address*)
 (custom_payload : int256)
 (l: LedgerLRecord rec): Prop.
 set (s:= pack_slice_unstake_tokens query_id amount return_excess custom_payload).
 add_computation (l) (unstake_tokens rec def src s).
 elpi read_fields(l) "unstaking".
 elpi read_fields(l') "unstaking".
 condition (xIntGeb unstaking 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (unstake_tokens rec def src s)) l) = false).
 conclusion (unstaking' = xIntPlus unstaking amount).
Defined.

Definition MTO3_def
 (query_id: uint64)
 (amount :int256)
 (coins :uint256)
 (addr :address)
 (round_since : uint32)
 (round_since_value : uint256)
 (l0: LedgerLRecord rec): Prop.
 elpi read_fields(l0) "staking".
 set (staking' := 
        cr_get_or_default (eval_state 
            (Uinterpreter 
                (udict_set_builder rec def 
                    staking 
                    32%Z 
                    (uint32_to_int256 round_since) 
                    (pack_builder (store_builder_ round_since_value)))) l0)).
 set (l := l0 <-- staking' with Staking).
 (* old version *)
 (* set (staking := cell_decode_with_default (mapping uint32 TvmCell) (--> l0 with Staking)).
 set (staking_value := pack_cell (store_builder_ round_since_value)).
 set (staking' := pack_cell (store_builder_ (staking[round_since] ← staking_value))).
 set (l := l0 <-- staking' with Staking). *)
 set (s:= pack_slice_tokens_minted query_id amount coins addr round_since).
 elpi read_fields(l) "parent".
 add_computation (l) (tokens_minted rec def parent s).
 elpi read_fields(l) "tokens".
 elpi read_fields(l') "tokens".
 condition (xIntGeb tokens 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (tokens_minted rec def parent s)) l) = false).
 conclusion (tokens' = xIntPlus tokens amount).
Defined.

Close Scope xprod_scope.

(* works *)
(* ConvertPropToChecker MTO3_def.
QuickCheck MTO3_def_QC. *)

(* Definition show_result {b : bool} {A : Type} `{Show A} (cr : ExecGenDefs.ControlResult A b) : string.
destruct cr.
{ exact ("value" ++ show a). }
{ exact "break". }
{ exact "return". }
exact ("error" ++ show e).
Defined.

#[global]
Instance ControlResult_Show {b : bool} {A : Type} `{Show A} : Show (ExecGenDefs.ControlResult A b) := {
    show cr := show_result cr
}. *)

(*
Definition SCO2_def
 (src:TvmSlice)(query_id: int64)
 (coins :int256)
 (round_since : int32)
 (l: LedgerLRecord rec): Prop.
 set (s:= pack_slice_save_coins query_id coins round_since).
 add_computation (l) (save_coins rec def src s).
 elpi read_fields(l) "staking".
 elpi read_fields(l') "staking".
 condition (xIntGeb unstaking 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (save_coins rec def src s)) l) = false).
 conclusion (unstaking' = xIntMinus unstaking amount).
Defined.

 Definition MTO4_def
 (src:TvmSlice)(query_id: int64)
 (amount :int256)
 (coins :int256)
 (addr :int256) (* address*)
 (round_since : int32)
 (l: LedgerLRecord rec): Prop.
 set (s:= pack_slice_tokens_minted query_id amount coins addr round_since).
 add_computation (l) (tokens_minted rec def src s).
 elpi read_fields(l) "tokens".
 elpi read_fields(l') "tokens".
 condition (xIntGeb tokens 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (tokens_minted rec def src s)) l) = false).
 conclusion (tokens' = xIntPlus tokens amount).
Defined.
 *)