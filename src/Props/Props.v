Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import Common.
Require Import HipoWallet.
Import HipoWallet.

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
(query_id: int64)
(amount :int256)
(coins :int256)
(addr :int256) (* address*)
(round_since : int32) : TvmSlice :=

(* (xMaybeMapDefault builder_to_slice_ (
        
builder_store_  (        
        xMaybeMapDefault  Datatypes.id  (builder_store_  (Wrap_TvmBuilder EmptyPrecell) query_id) default) 
                 amount  ) default).
 *)   
        (Wrap_TvmSlice
            (precell_push
                    (precell_push
                    (precell_push
                    (precell_push
                    (precell_push 
                        EmptyPrecell 
                        (pack_sized 64 (query_id : int64)))
                    (pack_sized 256 (amount : int256)))
                    (pack_sized 256 (coins : int256)))
                    (pack_sized 256 (addr : int256))) (*address*)
                (pack_sized 32 (round_since : int32)))).


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