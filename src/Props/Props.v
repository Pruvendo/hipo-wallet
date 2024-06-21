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
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Import MonadNotation.
Open Scope monad_scope.

Definition gen_uint_with_zero (n : N) : G (XUBInteger n) :=
    freq [ (1%nat, ret xInt0 : G (XUBInteger n)) ; (3%nat, arbitrarySized 4 : G (XUBInteger n)) ].

Definition gen_int_with_zero (n : N) : G (XBInteger n) :=
    freq [ (1%nat, ret xInt0 : G (XBInteger n)) ; (3%nat, arbitrarySized 4 : G (XBInteger n)) ].

Definition gen_positive_int (n : N) : G (XBInteger n) :=
    v <- (arbitrarySized 4 : G (XBInteger n)) ;;
    ret (xIntAbs v).

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

Definition pack_slice_save_coins
(query_id : uint64)
(coins : int256)
(addr : address)
(round_since : uint32) : TvmSlice :=
    pack_slice
        (store_builder_ query_id >=>
        store_builder_ coins >=>
        store_builder_ addr >=>
        store_builder_ round_since).

Definition pack_slice_tokens_minted
(query_id: uint64)
(amount :int256)
(coins :int256)
(addr :address)
(round_since : uint32) : TvmSlice :=
    pack_slice
        (store_builder_ query_id >=>
        store_builder_ amount >=>
        store_builder_ coins >=>
        store_builder_ addr >=>
        store_builder_ round_since).

Definition pack_slice_unstake_tokens
(query_id: uint64)
(amount :int256)
(return_excess : address)
: TvmSlice :=
    pack_slice
        (store_builder_ query_id >=>
        store_builder_ amount >=>
        store_builder_ return_excess).


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
 set (s:= pack_slice_tokens_burned query_id amount coins).
 add_computation (l) (tokens_burned rec def parent s).
 elpi read_fields(l) "unstaking".
 elpi read_fields(l') "unstaking".
 condition (xIntGeb unstaking 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (tokens_burned rec def parent s)) l) = false).
 conclusion (unstaking' = xIntMinus unstaking amount).
Defined.

ConvertPropToChecker TBO3_def.
QuickCheck TBO3_def_QC.

Close Scope xprod_scope.

Definition UTO3_def
 (query_id : uint64)
 (amount_ : int256)
 (v : int256)
 (l0: LedgerLRecord rec): Prop.
 set (amount := xIntPlus xInt1 amount_).
 set (l := l0 <-- xIntPlus v amount with Tokens).
 elpi read_fields (l) "owner".
 set (s:= pack_slice_unstake_tokens query_id amount (slice_decode_with_default address owner)).
 add_computation (l) (unstake_tokens rec def owner s).
 elpi read_fields(l) "tokens".
 elpi read_fields(l') "tokens".
 condition (xIntGeb tokens 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (unstake_tokens rec def owner s)) l) = false).
 conclusion (tokens' = xIntMinus tokens amount).
Defined.

ConvertPropToChecker UTO3_def.
QuickCheck (forAll (gen_positive_int 256) (fun amount =>
            forAll (gen_positive_int 256) (fun v => 
            fun query_id l => UTO3_def_QC query_id amount v l))).

Definition UTO4_def
 (query_id : uint64)
 (amount_ : int256)
 (v : int256)
 (l0: LedgerLRecord rec): Prop.
 set (amount := xIntPlus xInt1 amount_).
 set (l := l0 <-- xIntPlus v amount with Tokens).
 elpi read_fields (l) "owner".
 set (s:= pack_slice_unstake_tokens query_id amount (slice_decode_with_default address owner)).
 add_computation (l) (unstake_tokens rec def owner s).
 elpi read_fields(l) "unstaking".
 elpi read_fields(l') "unstaking".
 condition (xIntGeb unstaking 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (unstake_tokens rec def owner s)) l) = false).
 conclusion (unstaking' = xIntPlus unstaking amount).
Defined.

ConvertPropToChecker UTO4_def.
QuickCheck (forAll (gen_positive_int 256) (fun amount =>
            forAll (gen_positive_int 256) (fun v => 
            fun query_id l => UTO4_def_QC query_id amount v l))).

Definition MTO3_def
 (query_id: uint64)
 (amount :int256)
 (coins :int256)
 (addr :address)
 (round_since : uint32)
 (round_since_value_ : int256)
 (l0: LedgerLRecord rec): Prop.
 set (round_since_value := xIntPlus round_since_value_ coins).
 set (staking := cell_decode_with_default (mapping uint32 TvmCell) (--> l0 with Staking)).
 set (staking_value := pack_cell (store_builder_ round_since_value)).
 set (staking' := pack_cell (store_builder_ (staking[round_since] ← staking_value))).
 set (l := l0 <-- staking' with Staking).
 set (s:= pack_slice_tokens_minted query_id amount coins addr round_since).
 elpi read_fields(l) "parent".
 add_computation (l) (tokens_minted rec def parent s).
 elpi read_fields(l) "tokens".
 elpi read_fields(l') "tokens".
 condition (xIntGeb tokens 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (tokens_minted rec def parent s)) l) = false).
 conclusion (tokens' = xIntPlus tokens amount).
Defined.

ConvertPropToChecker MTO3_def.
QuickChick (forAll (gen_uint_with_zero 32) (fun round_since =>
            forAll (gen_int_with_zero 256) (fun round_since_value =>
                fun a1 a2 a3 a4 a7 => MTO3_def_QC a1 a2 a3 a4 round_since round_since_value a7))).

Definition MTO4_def
 (query_id: uint64)
 (amount :int256)
 (coins : int256)
 (addr : address)
 (round_since : uint32)
 (round_since_value_ : int256)
 (l0: LedgerLRecord rec): Prop.
 set (round_since_value := xIntPlus round_since_value_ coins).
 elpi read_fields(l0) "staking".
 set (staking' := 
        if (Common.eqb round_since xInt0 : bool) then staking else
            cr_get_or_default (eval_state 
                (Uinterpreter 
                    (udict_set_builder rec def 
                        staking 
                        32%Z 
                        (uint32_to_int256 round_since) 
                        (pack_builder (store_builder_ round_since_value)))) l0)).
 set (l := l0 <-- staking' with Staking).
 set (s:= pack_slice_tokens_minted query_id amount coins addr round_since).
 elpi read_fields(l) "parent".
 add_computation (l) (tokens_minted rec def parent s).
 elpi read_fields(l') "staking".
 set (x := 
    cr_get_or_default (eval_state 
        (Uinterpreter 
            (udict_get rec def 
                staking'' 
                32%Z 
                (uint32_to_int256 round_since))) l')).

 condition (ExecGenDefs.isError (eval_state (Uinterpreter (tokens_minted rec def parent s)) l) = false).
 conclusion (slice_decode_ int256 (fst x) = None 
        \/ slice_decode_ int256 (fst x) = 
            Some (xIntMinus round_since_value coins, Wrap_TvmSlice EmptyPrecell)).
Defined.

ConvertPropToChecker MTO4_def.
QuickChick (forAll (gen_uint_with_zero 32) (fun round_since =>
            forAll (gen_int_with_zero 256) (fun round_since_value =>
                fun a1 a2 a3 a4 a7 => MTO4_def_QC a1 a2 a3 a4 round_since round_since_value a7))).

Definition SCO2_def
(query_id: uint64)
(coins : int256)
(addr :address)
(round_since : uint32)
(round_since_value : int256)
(l0: LedgerLRecord rec): Prop.
 elpi read_fields(l0) "staking".
 set (staking' := 
       if (Common.eqb round_since xInt0 : bool) then staking else
           cr_get_or_default (eval_state 
               (Uinterpreter 
                   (udict_set_builder rec def 
                       staking 
                       32%Z 
                       (uint32_to_int256 round_since) 
                       (pack_builder (store_builder_ round_since_value)))) l0)).
 set (l := l0 <-- staking' with Staking).
 set (s:= pack_slice_save_coins query_id coins addr round_since).
 elpi read_fields(l) "parent".
 add_computation (l) (save_coins rec def parent s).
 elpi read_fields(l') "staking".
 set (x := 
    cr_get_or_default (eval_state 
        (Uinterpreter 
            (udict_get rec def 
                staking'' 
                32%Z 
                (uint32_to_int256 round_since))) l')).

 condition (ExecGenDefs.isError (eval_state (Uinterpreter (save_coins rec def parent s)) l) = false).
 conclusion (slice_decode_ int256 (fst x) = 
    Some (xIntPlus (if (Common.eqb round_since xInt0 : bool) then xInt0 else round_since_value) coins, Wrap_TvmSlice EmptyPrecell)).
Defined.

ConvertPropToChecker SCO2_def.
QuickChick (forAll (gen_uint_with_zero 32) (fun round_since =>
                fun a1 a2 a3 a5 a6 => SCO2_def_QC a1 a2 a3 round_since a5 a6)).