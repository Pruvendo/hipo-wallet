Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UrsusQC.CommonQCEnvironment.
Require Import UrsusContractCreator.UrsusFieldUtils.
Require Import UrsusContractCreator.BaseContracts.EverContract.

Set UrsusPrefixTactic "PrefixTestOptimized".


#[translation = off]
#[quickchick = off]
#[language = func]
Contract HipoWallet ;
Sends To  ; 
Inherits EverBaseContract ;
Types ;
Constants 

Definition reserve_at_most  : int256 := 2%Z
Definition chain_base       : int256 := 0%Z
Definition unstake_auto     : int256 := 0%Z
Definition unstake_best     : int256 := 2%Z

Definition err_insufficient_fee       : _NErrorType := 101
Definition err_insufficient_funds     : _NErrorType := 102
Definition err_access_denied          : _NErrorType := 103
Definition err_only_basechain_allowed : _NErrorType := 104
Definition err_receiver_is_sender     : _NErrorType := 105
Definition err_invalid_op             : _NErrorType := 107
Definition err_invalid_comment        : _NErrorType := 108
Definition err_invalid_parameters     : _NErrorType := 109

Definition gas_unstake_tokens       : int256 := 9040%Z 
Definition gas_proxy_reserve_tokens : int256 := 6538%Z
Definition gas_reserve_tokens       : int256 := 15521%Z
Definition gas_mint_bill            : int256 := 7757%Z
Definition gas_assign_bill          : int256 := 5960%Z
Definition gas_burn_bill            : int256 := 6558%Z
Definition gas_bill_burned          : int256 := 12316%Z
Definition gas_burn_tokens          : int256 := 16627%Z
Definition gas_proxy_tokens_burned  : int256 := 7307%Z
Definition gas_tokens_burned        : int256 := 7179%Z 
Definition gas_send_tokens          : int256 := 10678%Z
Definition gas_receive_tokens       : int256 := 11691%Z

Definition gas_upgrade_wallet : int256       := 7618%Z
Definition gas_proxy_migrate_wallet : int256 := 7978%Z
Definition gas_migrate_wallet : int256       := 12802%Z
Definition gas_proxy_merge_wallet : int256   := 7841%Z
Definition gas_merge_wallet : int256         := 7443%Z

Definition op_receive_tokens        : int32  := 0x178d4519%Z
Definition op_transfer_notification : int256 := 0x7362d09c%Z
Definition op_proxy_reserve_tokens  : int32  := 0x688b0213%Z
Definition op_gas_excess            : int256 := 0xd53276db%Z
Definition op_unstake_tokens        : int32  := 0x595f07bc%Z
Definition op_proxy_migrate_wallet  : int32  := 0x0cb246bb%Z
Definition op_send_tokens           : int32  := 0x0f8a7ea5%Z
Definition op_tokens_minted         : int32  := 0x5445efee%Z
Definition op_save_coins            : int32  := 0x4cce0e74%Z
Definition op_rollback_unstake      : int32  := 0x1b77fd1a%Z
Definition op_tokens_burned         : int32  := 0x5b512e25%Z
Definition op_unstake_all           : int32  := 0x5ae30148%Z
Definition op_upgrade_wallet        : int32  := 0x01d9ae1c%Z
Definition op_merge_wallet          : int32  := 0x63d3a76c%Z
Definition op_withdraw_surplus      : int32  := 0x23355ffb%Z
Definition op_withdraw_jettons      : int32  := 0x768a50b2%Z
Definition op_top_up                : int32  := 0x5372158c%Z

Definition send_remaining_value     : int256 := 64%Z
Definition send_bounce_if_failed    : int256 := 16%Z
Definition send_pay_gas_separately  : int256 := 1%Z
Definition send_unreserved_balance  : int256 := 28%Z
Definition send_ignore_errors       : int256 := 2%Z
;

Record Contract := {
    (* tmp_tuple:(TvmBuilder ** TvmBuilder ** int) ; *)
    owner: TvmSlice;
    parent: TvmSlice (* TvmSlice *);
    tokens: int256;
    staking: TvmCell;
    unstaking: int256
} .

(* Require Import UMLang.UrsusCoercions. *)

SetUrsusOptions.

UseLocal Definition _ := [ TvmBuilder ; 
                           optional TvmBuilder; 
                           address ; 
                           int256 ;
                           uint256 ;
                           int64 ;
                           uint64 ;
                           bool; 
                           (TvmSlice ** TvmCell);
                           TvmCell ; 
                           TvmSlice ; 
                           (optional (TvmCell ** TvmSlice));
                           (optional (address ** TvmSlice));
                           (int256 ** int256 ** int256 ** int256); 
                           (uint256 ** uint256);
                           (int256 ** int256 ** int256); 
                           (TvmCell ** int256); 
                           (* N; *)
                           (TvmBuilder ** TvmBuilder ** int256) ;
                           (optional (int256 ** TvmSlice)) ].

(* builder to_builder(slice s) inline {
    return begin_cell().store_slice(s);
} *)
#[returns = b]
Ursus Definition to_builder(s:TvmSlice): UExpression TvmBuilder true.
{
    ::// b -> store(s) .
    refine __return__.
}
return.
Defined.
Sync.


(* () send_raw_message(cell msg, int mode) impure asm "SENDRAWMSG"; *)
Ursus Definition send_raw_message (msg:TvmCell) (mode:int256): UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* () send_msg(int bounceable?, builder dst, builder state_init, builder body, int coins, int mode) impure inline_ref {
    cell msg = begin_cell()
        .store_uint(bounceable? ? 0x18 : 0x10, 6) ;; 011000 or 010000
        .store_builder(dst)
        .store_coins(coins)
        .store_uint(0, 1 + 4 + 4 + 64 + 32)
        .store_state_init(state_init)
        .store_body(body)
        .end_cell();
    send_raw_message(msg, mode);
}
(*  *)() send_msg(int bounceable?, builder dst, builder state_init, builder body, int coins, int mode) impure inline_ref { *)
Ursus Definition send_msg (bounceable:bool)(dst:TvmBuilder)(state_init:TvmBuilder)
                          (body:TvmBuilder)(coins:int256)(mode:int256): UExpression PhantomType true.
{
     ::// var0 msg : TvmBuilder ; _ | .
     ::// msg -> store(bounceable ? {0x18:uint256} : {0x10:uint256} , {6:uint256} ) .
     ::// msg -> store (dst) .
     ::// msg -> store (coins) .
     ::// msg -> store ( {0:uint256} , {1:uint256} + {4:uint256} + {4:uint256} + {64:uint256} + {32:uint256} ) .
     ::// msg -> store (state_init) .
     ::// msg -> store (body) .
     ::// send_raw_message (msg -> toCell() , mode) .
     refine __return__.
}
return.
Defined.
Sync.

(* (cell, slice, int) udict_delete_get?(cell dict, int key_len, int index) asm(index dict key_len) "DICTUDELGET" "NULLSWAPIFNOT"; *)
Ursus Definition udict_delete_get(dict:TvmCell)(key_len:int256)(index:uint32): UExpression (TvmCell ** int256) false.
{
    refine __return__.
}
return.
Defined.
Sync.


(* int addr_none?(slice s) asm "b{00} PUSHSLICE SDEQ"; *)
Ursus Definition addr_none (c:TvmSlice): UExpression bool false.
{
    refine __return__.
}
return.
Defined.
Sync.

Ursus Definition tvm_set_data (c: TvmCell): UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.


Ursus Definition tvm_get_data: UExpression TvmCell false.
{
    refine __return__.
}
return.
Defined.
Sync.

UseLocal Definition _ := [(option (TvmSlice ** TvmCell))].
(* (slice, cell) load_maybe_ref(slice s) asm( -> 1 0) "LDOPTREF"; *)
#[returns=ret]
Ursus Definition load_maybe_ref (s:TvmSlice) : UExpression (option (TvmSlice ** TvmCell)) false.
{
    ::// ret := {} .
    refine __return__.
}
return.
Defined.
Sync.

(* slice skip_dict(slice s) asm "SKIPDICT"; *)
Ursus Definition skip_dict (s:TvmSlice) : UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* forall X -> (X, ()) ~impure_touch(X x) impure asm "NOP"; *)
Ursus Definition impure_touch (s:TvmSlice) : UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* int (int cells, int bits, int seconds, int is_mc?) asm "GETSTORAGEFEE"; *)
Ursus Definition get_storage_fee (cells:int256)(bits:int256)(seconds:int256)(is_mc:bool):UExpression int256 false. 
{
    refine __return__.
}
return.
Defined.
Sync.

(* int wallet_storage_fee() inline_ref { *)
#[returns=ret]
Ursus Definition wallet_storage_fee:UExpression int256 false.
{
    ::// var0 cells:int256:= {1%Z} + {1%Z};_|.
    ::// var0 bits:int256:= {267%Z} + {267%Z} + {124%Z};_|. 
    ::// var0 duration:int256:= {60%Z} * {60%Z} * {24%Z} * {365%Z} * {5%Z}; _|.

    ::// ret := get_storage_fee(cells, bits, duration, {false}) .

    refine __return__.
}
return .
Defined.
Sync.

(* int get_compute_fee(int gas_used, int is_mc?) asm "GETGASFEE"; *)
Ursus Definition get_compute_fee(x:int256)(y:bool):UExpression int256 false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* int get_simple_forward_fee(int cells, int bits, int is_mc?) asm "GETFORWARDFEESIMPLE"; *)
Ursus Definition get_simple_forward_fee(cells:int256)(bits:int256)(is_mc:bool):UExpression int256 false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* int send_tokens_fee() { *)
#[returns=_ret]
Ursus Definition send_tokens_fee : UExpression int256 false.
{
    (* int storage_fee = wallet_storage_fee(); *)
    ::// var0 storage_fee :_:= wallet_storage_fee();_|.
    (* int compute_gas = gas::send_tokens + gas::receive_tokens; *)
    ::// var0 compute_gas :_:= gas_send_tokens + gas_receive_tokens;_|.
    (* int compute_fee = get_compute_fee(compute_gas, false); *)
    ::// var0 compute_fee:_:= get_compute_fee(compute_gas, {false});_|.
    (* int forward_fee = get_simple_forward_fee(1 + 1, 267 + 267 + 4 + 1 + 4, false); *)
    ::// var0 forward_fee:_:= get_simple_forward_fee({1%Z} + {1%Z}, {267%Z} + {267%Z} + {4%Z} + {1%Z} + {4%Z}, {false});_|.
    (* return storage_fee + compute_fee + forward_fee; *)
    ::// _ret := storage_fee + compute_fee + forward_fee .

    refine __return__.

}
return.
Defined.
Sync.

(* int equal_TvmSlicebits(slice a, slice b) asm "SDEQ"; *)
Ursus Definition equal_TvmSlicebits(src:TvmSlice)(owner:TvmSlice) : UExpression bool false.
{
    refine __return__. 
}
return.
Defined.
Sync.

(* slice my_address() asm "MYADDR"; *)
Ursus Definition my_address : UExpression TvmSlice false.
{
    refine __return__. 
}
return.
Defined.
Sync.

(* forall X -> X null() asm "PUSHNULL"; *)
Ursus Definition null  : UExpression int256 false.
{
    refine __return__.
}
return.
Defined.
Sync.

Ursus Definition nullB  : UExpression TvmBuilder false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* () raw_reserve(int amount, int mode) impure asm "RAWRESERVE"; *)
Ursus Definition raw_reserve(amount:int256)(mode:int256) : UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* cell create_wallet_data(builder owner, slice parent) inline { *)
#[returns=_result]
Ursus Definition create_wallet_data (owner:TvmBuilder)(parent:TvmSlice) : UExpression TvmCell true.
{
(* return begin_cell()
        .store_builder(owner)
        .store_slice(parent)
        .store_coins(0) ;; tokens
        .store_dict(null()) ;; staking
        .store_coins(0) ;; unstaking
        .end_cell(); *)
     ::// var0 b : TvmBuilder ; _ | .
     ::// b -> store(owner) .
     ::// b -> store (parent) .
     ::// b -> store ({0:uint256} ) .
     ::// b -> store ( null() ) .
     ::// b -> store ({0:uint256} ) .
     ::// _result := b -> toCell ().
    refine __return__.
}    
return .
Defined.
Sync.

(* builder create_state_init(cell code, cell data) inline { *)
#[returns = b]
Ursus Definition create_state_init (code:TvmCell)(data:TvmCell) : UExpression TvmBuilder true.
{
(* return begin_cell()
        .store_uint(6, 5) ;; 00110
        .store_ref(code)
        .store_ref(data); *)
     ::// b -> store({6:uint256}  , {5:uint256}  ) .
     ::// b -> store (code) .
     ::// b -> store (data) .
     refine __return__.
}
return .
Defined.
Sync.

(* builder create_address(int wc, int addr) inline_ref { *)
#[returns=b]
Ursus Definition create_address (wc:int256)(addr:int256) : UExpression TvmBuilder true.
{
(* return begin_cell()
        .store_uint(4, 3) ;; 100
        .store_int(wc, 8)
        .store_uint(addr, 256); *)
     ::// b -> store({4:uint256} , {3:uint256} ) .
     ::// b -> store (wc , {8%Z:int256} ) .
     ::// b -> store (addr , {256:uint256} ) .
    refine __return__.
}
return .
Defined.
Sync.

(* cell end_cell(builder b) asm "ENDC"; *)
(* Ursus Definition end_cell (b:TvmBuilder) : UExpression TvmCell false.
{
    refine __return__.
}
return .
Defined.
Sync. *)

Check tvm_hash.

(* int TvmCellhash(cell c) asm "HASHCU"; *)
Ursus Definition TvmCellhash (b:TvmCell) : UExpression int256 false.
{
    refine __return__.
}
return .
Defined.
Sync.

(* (builder, builder, int) create_wallet_address(builder owner, slice parent, cell wallet_code) inline_ref { *)
#[returns=_result]
Ursus Definition create_wallet_address (owner:TvmBuilder)(parent:TvmSlice)(wallet_code:TvmCell) 
                                       : UExpression (TvmBuilder ** TvmBuilder ** int256) true.
{
    (* cell wallet_data = create_wallet_data(owner, parent); *)
    ::// var0 wallet_data : TvmCell := create_wallet_data(  {owner} , parent ) ; _ | .  

    (* builder state_init = create_state_init(wallet_code, wallet_data);  *)
    ::// var0 state_init:TvmBuilder := create_state_init(wallet_code, wallet_data); _ | .
    (* int addr = state_init.end_cell().TvmCellhash(); *)
    ::// var0 addr:int256 := TvmCellhash(state_init -> toCell())  ;_|.                          
    (* builder wallet = create_address(chain::base, addr); *)
    ::// var0 wallet : TvmBuilder := create_address( chain_base , addr );_|.
    ::// _result := [wallet, state_init, addr] .
    refine __return__.
}
return .
Defined.
Sync.

Locate "tvm->code".

(* cell my_code() asm "MYCODE"; *)
Ursus Definition my_code : UExpression TvmCell false .
{
    refine __return__.
}
return \\ tvm->code () \\.
Defined.
Sync.

(* (int, int) parse_std_addr(slice s) asm "REWRITESTDADDR"; *)
Ursus Definition parse_std_addr (s:TvmSlice) : UExpression (int256 ** int256) false .
{
    refine __return__.
}
return .
Defined.
Sync.

(* cell udict_set_builder(cell dict, int key_len, int index, builder value) asm(value index dict key_len) "DICTUSETB"; *)
Ursus Definition udict_set_builder(z:TvmCell)(x:int256)(round_since:uint32)(y:TvmBuilder):UExpression TvmCell false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* (slice, int) idict_get?(cell dict, int key_len, int index) asm(index dict key_len) "DICTIGET" "NULLSWAPIFNOT"; *)
Ursus Definition udict_get(dict:TvmCell)(key_len:int256)(index:uint32):UExpression (TvmSlice ** int256) false.
{
    refine __return__.
}
return.
Defined.
Sync.

(* int get_forward_fee(int cells, int bits, int is_mc?) asm "GETFORWARDFEE"; *)
Ursus Definition get_forward_fee(x:uint256)(y:uint256)(z:bool):UExpression int256 false.
{
    refine __return__.
}
return .
Defined.
Sync.

#[returns=ret]
Ursus Definition unstake_tokens_fee:UExpression int256 false.
{
    (* int compute_gas = *)
    ::// var0 compute_gas:int256 :=  
    gas_unstake_tokens +
    gas_proxy_reserve_tokens +
    gas_reserve_tokens +
    gas_mint_bill +
    gas_assign_bill +
    gas_burn_bill +
    gas_bill_burned +
    gas_burn_tokens +
    gas_mint_bill +   
    gas_assign_bill + 
    gas_burn_bill +   
    gas_bill_burned + 
    gas_burn_tokens + 
    gas_proxy_tokens_burned +
    gas_tokens_burned ;_|.
    (* int compute_fee = get_compute_fee(compute_gas, false); *)
    ::// var0 compute_fee:_:= get_compute_fee(compute_gas, {false}); _| .

    (* int s_fwd_fee = get_forward_fee(0, 0, false);
    int m_fwd_fee = get_forward_fee(1, 1023, false);
    int l_fwd_fee = get_forward_fee(1 + 3, 1023 ** 2, false); *)
    ::// var0 s_fwd_fee:_:= get_forward_fee({0}, {0}, {false}); _| .
    ::// var0 m_fwd_fee:_:= get_forward_fee({1}, {1023}, {false}); _| .
    ::// var0 l_fwd_fee:_:= get_forward_fee({1} + {3}, {1023} ** {2}, {false}); _| .

    (* int forward_fee = *)
    ::// var0 forward_fee :_:=
        m_fwd_fee + (* ;; proxy_reserve_tokens *)
        m_fwd_fee + (* ;; reserve_tokens *)
        l_fwd_fee + (* ;; mint_bill *)
        l_fwd_fee + (* ;; assign_bill *)
        s_fwd_fee + (* ;; ownership_assigned *)
        s_fwd_fee + (* ;; burn_bill *)
        m_fwd_fee + (* ;; bill_burned *)
        m_fwd_fee + (* ;; burn_tokens *)
        l_fwd_fee + (* ;; mint_bill - second try *)
        l_fwd_fee + (* ;; assign_bill - second try *)
        s_fwd_fee + (* ;; burn_bill - second try *)
        m_fwd_fee + (* ;; bill_burned - second try *)
        m_fwd_fee + (* ;; burn_tokens - second try *)
        m_fwd_fee + (* ;; proxy_tokens_burned *)
        m_fwd_fee;_|. (* ;; tokens_burned *)

    ::// ret := compute_fee + forward_fee .

    refine __return__.
}
return .
Defined.
Sync.

#[returns=ret]
Ursus Definition upgrade_wallet_fee:UExpression int256 false.
{
    (* int compute_gas = *)
    :://var0 compute_gas:int256:= 
        gas_upgrade_wallet +
        gas_proxy_migrate_wallet +
        gas_migrate_wallet +
        gas_proxy_merge_wallet +
        gas_merge_wallet;_|.
    :://var0 compute_fee:_:= get_compute_fee(compute_gas, {false});_|.

    (* int m_fwd_fee = get_forward_fee(1, 1023, false); *)
    :://var0 m_fwd_fee:_:= get_forward_fee({1}, {1023}, {false});_|.

    (* int l_fwd_fee = get_forward_fee(1 + 3, 1023 ** 2, false); *)
    :://var0 l_fwd_fee:_:= get_forward_fee({1} + {3}, {1023} ** {2}, {false});_|.

   (*  int forward_fee = *)
    :://var0 forward_fee:_:=
        m_fwd_fee + (* ;; proxy_migrate_wallet *)
        m_fwd_fee + (* ;; migrate_wallet *)
        m_fwd_fee + (* ;; proxy_merge_wallet *)
        l_fwd_fee;_|. (* ;; merge_wallet *)

    ::// ret := compute_fee + forward_fee .

refine __return__.
}
return.
Defined.
Sync.

Locate "revert".

(* Ursus Definition throw(src:uint256):UExpression PhantomType true.
{
    refine // require_ ({false}, {src: }).
    refine __return__.
}
return .
Defined. 
Sync.*)

(* slice skip_bits(slice s, int len) asm "SDSKIPFIRST"; *)
Ursus Definition skip_bits(x:int256):UExpression TvmSlice false.
{ 
refine __return__.
}
return .
Defined.
Sync.

(* int get_original_fwd_fee(int fwd_fee, int is_mc?) asm "GETORIGINALFWDFEE"; *)
Ursus Definition get_original_fwd_fee(x:TvmSlice)(y:bool):UExpression int256 false.
{ 
refine __return__.
}
return .
Defined.
Sync.

(* [int, cell] get_incoming_value() asm "INCOMINGVALUE"; *)
Ursus Definition get_incoming_value : UExpression (int256 ** TvmCell) false.
{ 
refine __return__.
}
return .
Defined.
Sync.

Locate "first".

(* forall X, Y -> X pair_first([X, Y] p) *)
(* #[returns=ret]
Ursus Definition pair_first(x:(int256 ** TvmCell)) : UExpression int256 false.
{
  ::// var0 (f:int256 , s:TvmCell) := x;_|.
  ::// ret := f.
refine __return__.
}
return .
Defined.
Sync. *)

(*******************************************************************************)

(* () save_data() impure inline_ref {
    begin_cell()
        .store_slice(owner)
        .store_slice(parent)
        .store_coins(tokens)
        .store_dict(staking)
        .store_coins(unstaking)
        .end_cell()
        .set_data();
} *)

  Ursus Definition save_data : UExpression PhantomType true.
{   
    (* begin_cell() *)
    ::// var0 b : TvmBuilder ; _ |.
    (* .store_slice(owner) *)
    ::// b -> store (owner) .
    (* .store_slice(parent) *)
    ::// b -> store (parent) .
    (* .store_coins(tokens) *)
    ::// b -> store (tokens) .
    (* .store_dict(staking) *)
    ::// b -> store (staking) .
    (* .store_coins(unstaking) *)
    ::// b -> store (unstaking) .
    (* .set_data(); *)
    ::// tvm_set_data (b -> toCell()) .

    refine __return__.
}
return.
Defined.
Sync. 

#[returns = addr_slice]
Ursus Definition load_msg_addr (s: ULValue TvmSlice): UExpression TvmSlice true.
{
    ::// var0 a : address := s -> load (address) ; _ | .
    ::// var0 b : TvmBuilder; _ |.
    ::// b -> store (a) ; _ |.
    ::// addr_slice := b -> toCell() -> toSlice () .
    refine __return__.
}
return.
Defined.
Sync.


(* () load_data() impure inline_ref {
    slice ds = get_data().begin_parse();
    owner = ds~load_msg_addr();
    parent = ds~load_msg_addr();
    tokens = ds~load_coins();
    staking = ds~load_dict();
    unstaking = ds~load_coins();
    ds.end_parse();
} *)

Ursus Definition load_data : UExpression PhantomType true.
{
    (* slice ds = get_data().begin_parse(); *)
    ::// var0 ds: TvmSlice  := tvm_get_data () -> toSlice(); _ | .
    (* owner = ds~load_msg_addr(); *)
    ::// owner := load_msg_addr (ds).
    (* parent = ds~load_msg_addr(); *)
    ::// parent := load_msg_addr (ds) .
    (* tokens = ds~load_coins(); *)
    ::// tokens := ds -> load (int256).
    (* staking = ds~load_dict(); *)
    ::// staking := ds -> load (TvmCell).
    (* unstaking = ds~load_coins(); *)
    ::// unstaking := ds -> load (int256).
    refine __return__.
}
return.
Defined.
Sync.

UseLocal Definition _ := [uint64; (optional (uint64 ** TvmSlice)); uint32; (optional (uint32 ** slice_))].

#[write = s]
Ursus Definition save_coins (src:TvmSlice) (s:TvmSlice): UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:uint64 := s -> load(uint64);_|. 
    (* int coins = s~load_coins(); *)
    ::// var0 coins: _ := s -> load(int256);_|.
    (* s~load_msg_addr(); ;; skip owner address *)
    ::// var0 __ : _ := load_msg_addr (s) ; _ | .
    (* int round_since = s~load_uint(32); *)
    ::// var0 round_since : _ := s -> load(uint32);_|. 
    (* s.end_parse(); *)

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, parent)); *)
    ::// require_ (equal_TvmSlicebits(src, parent)  , err_access_denied ) ; _ | .
    (* ( slice v, int f? ) = staking.udict_get?(32, round_since); *)
    :://var0 ( v:TvmSlice, f:int256 ) := udict_get(staking , {32%Z}, round_since);_|.
    ::// if (f ) then { ->/> } .
    {
        (* coins += v~load_coins(); *)
        refine// coins += v -> load (int256) | . 
        (* v.end_parse(); *)
    }
    (* staking~udict_set_builder(32, round_since, begin_cell().store_coins(coins)); *)
    ::// var0 r:TvmBuilder;_|.
    ::// r -> store (coins) .
    ::// udict_set_builder( staking , {32%Z} , round_since, r ) .

    refine __return__.
}
return.
Defined.
Sync.

#[write = s]
Ursus Definition send_tokens (src:TvmSlice) (s:TvmSlice) (fwd_fee:int256): UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id: _ := s -> load(uint64); _ | . 
    (* int amount = s~load_coins(); *)
    ::// var0 amount: _ := s -> load(int256);_ | . 
    (*  slice recipient = s~load_msg_addr(); *)    
    ::// var0 recipient_address : address := s -> load (address) ; _ | .
    ::// var0 recipient_builder : TvmBuilder; _ |.
    ::// recipient_builder -> store (recipient_address) ; _ |.
    ::// var0 recipient:_:= recipient_builder -> toCell() -> toSlice () ; _ | .

    (* slice return_excess = s~load_msg_addr(); *)
    ::// var0 return_address : address := s -> load (address) ; _ | .
    ::// var0 return_builder : TvmBuilder; _ |.
    ::// return_builder -> store (return_address) ; _ |.
    ::// var0 return_excess:_:= return_builder -> toCell() -> toSlice () ; _ | .

    (* s~load_maybe_ref(); ;; skip custom_payload *)
    ::// load_maybe_ref(s) .                           

    (* int forward_ton_amount = s~load_coins(); *)
    ::// var0 forward_ton_amount:int256:= s->load(int256);_|.

    (* slice forward_payload = s; *)
    ::// var0 forward_payload:_:=s;_|.

    (* s~skip_dict(); ;; check either field *)
    ::// skip_dict(s).

    (* s~impure_touch(); *)
    :://impure_touch(s).

    (* if return_excess.addr_none?() {
        return_excess = src;
    } *)
    :://if(addr_none(return_excess)) then {->>} .  
       { ::// return_excess := src | . }

(*    ::// var0 ( recipient_wc , _ ) := parse_std_addr(slice) ;_|. *)
    ::// var ( recipient_wc:int256, tmp:int256 ) := parse_std_addr(recipient);_|.
    (* ( builder wallet, builder state_init, _ ) = create_wallet_address(recipient.to_builder(), parent, my_code()); *)

    ::// var0 ( wallet:TvmBuilder , state_init:TvmBuilder , tmp1:int256 ) 
         := create_wallet_address( to_builder(recipient) , parent, my_code() ) ;_|.

    (* int incoming_ton = get_incoming_value().pair_first(); *)
    ::// var0 incoming_ton:int256:= first ( get_incoming_value() ); _ | . 

    (* int fee = send_tokens_fee() + forward_ton_amount + (forward_ton_amount ? 2 : 1) ** fwd_fee; *) 
    ::// var0 fee:int256:= send_tokens_fee() + forward_ton_amount + ((forward_ton_amount == {0%Z} ) ? {2%Z} : {1%Z}) * fwd_fee ;_|.

    (* int enough_fee? = incoming_ton >= fee; *)
    ::// var0 enough_fee:bool:= incoming_ton >= fee;_|.

(*     throw_unless(err_only_basechain_allowed, recipient_wc == chain::base);
    throw_unless(err_access_denied, equal_TvmSlicebits(src, owner));
    throw_unless(err_insufficient_fee, enough_fee?);
    throw_unless(err_insufficient_funds, amount <= tokens);
    throw_if(err_receiver_is_sender, equal_TvmSlicebits(recipient, owner)); (* ????????????????? *)
 *)

   ::// require_ (recipient_wc  ==  chain_base , err_only_basechain_allowed );_ | .
   ::// require_ (equal_TvmSlicebits(src, owner) , err_access_denied ) ;_ | .
   ::// require_ (enough_fee  , err_insufficient_fee ) ;_ | .
   ::// require_ (amount <= tokens  , err_insufficient_funds ) ;_ | .
   ::// require_ (equal_TvmSlicebits(recipient, owner)  , err_receiver_is_sender ) ;_ | .

    (* tokens -= amount; *)
    ::// tokens -= amount.

    (* builder receive = begin_cell() *)
         ::// var0 receive : TvmBuilder ; _ |.
        (* .store_uint(op::receive_tokens, 32) *)
         ::// {receive} -> store ( op_receive_tokens , {32:uint256} ) .
        (* .store_uint(query_id, 64) *)
         ::// {receive} -> store (query_id(* , 64 *)) .
       (* .store_coins(amount) *)
         ::// {receive} -> store (amount ) .
        (* .store_slice(owner) *)
        ::// {receive} -> store (owner) .
        (* .store_slice(return_excess) *)
        ::// {receive} -> store (return_excess) .
        (* .store_coins(forward_ton_amount) *)
        ::// {receive} -> store (forward_ton_amount) .
        (* .store_slice(forward_payload); *)
        ::// {receive} -> store (forward_payload) .
    (* send_msg(true, wallet, state_init, receive, 0, send_remaining_value); *)
       refine //send_msg ({true},wallet,state_init,{receive},{0%Z},send_remaining_value).
    refine __return__. 
}
return.
Defined.
Sync.

(* () receive_tokens(slice src, slice s) impure inline { *)
#[write = s]
Ursus Definition receive_tokens (src:TvmSlice) (s:TvmSlice): UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_:=s -> load(uint64);_|. 

    (* int amount = s~load_coins(); *)
    ::// var0 amount:_:=s -> load(int256);_|.

    (* slice sender = s~load_msg_addr(); *)
    ::// var0 sender_address : address := s -> load (address) ; _ | .
    ::// var0 sender_builder : TvmBuilder; _ |.
    ::// sender_builder -> store (sender_address) ; _ |.
    ::// var0 sender:_:= sender_builder -> toCell() -> toSlice () ; _ | .

    (* slice return_excess = s~load_msg_addr(); *)
    ::// var0 return_address : address := s -> load (address) ; _ | .
    ::// var0 return_builder : TvmBuilder; _ |.
    ::// return_builder -> store (return_address) ; _ |.
    ::// var0 return_excess:_:= return_builder -> toCell() -> toSlice () ; _ | .

    (* int forward_ton_amount = s~load_coins(); *)
    ::// var0 forward_ton_amount:_:=s -> load(int256);_|.

    ::// var0 forward_payload:_ := s;_|.

    (* ( _, _, int wallet_addr ) = create_wallet_address(sender.to_builder(), parent, my_code()); *)
    ::// var0 ( a:TvmBuilder, b:TvmBuilder, wallet_addr:int256 ) :=
        create_wallet_address( to_builder(sender) , parent, my_code() ) ;_|.
     ::// var0 ( src_wc:int256, src_addr:int256 ) := parse_std_addr(src);_|.

    (* throw_unless(err_access_denied, (src_wc == chain::base) & (src_addr == wallet_addr)); *)
    ::// require_ ( src_wc == chain_base , err_access_denied ) ;_ | .
   
    ::// tokens += amount.

    ::// if(forward_ton_amount) then { ->/> }.
       {
        (* builder notification = begin_cell() *)
         ::// var0 notification : TvmBuilder ; _ |.
        (* .store_uint(op::transfer_notification, 32) *)
         ::// notification -> store (op_receive_tokens , {32:uint256} ) .
        (* .store_uint(query_id, 64) *)
         ::// notification -> store (query_id , {64:uint256} ) .
            (* .store_slice(sender) *)
        ::// notification -> store (sender) .
            (* .store_slice(forward_payload); *)
        ::// notification -> store (forward_payload) .

        ::// send_msg({false}, to_builder(owner), nullB(), notification, forward_ton_amount,
            send_pay_gas_separately + send_bounce_if_failed ) | .
       }

    ::// raw_reserve(wallet_storage_fee ( ), reserve_at_most).

    (* builder excess = begin_cell() *)
         ::// var0 excess : TvmBuilder ; _ |.
        (* .store_uint(op::gas_excess, 32) *)
         ::// excess -> store (op_gas_excess , {32:uint256} ) .
        (* .store_uint(query_id, 64); *)
         ::// excess -> store (query_id , {64:uint256} ) .

         ::// send_msg({false}, to_builder(return_excess) , nullB(), 
                      excess, {0%Z}, send_unreserved_balance + send_ignore_errors) .

    refine __return__. 
}
return.
Defined.
Sync.

UseLocal Definition _ := [(optional (uint256 ** slice_));int32; (optional (int64 ** slice_)) ; (optional (int32 ** slice_)) ; (optional (int256 ** slice_))].

#[write = s]
Ursus Definition tokens_minted(src:TvmSlice)(s:TvmSlice):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_:=s -> load(int64);_|.
   (*  int amount = s~load_coins(); *)
    ::// var0 amount:_:=s -> load(int256);_|.
    (* int coins = s~load_coins(); *)
    ::// var0 coins:_:=s -> load(uint256);_|.
    (* s~load_msg_addr(); ;; skip owner address *) 
    ::// var0 xxx : address := s -> load (address) ; _ | .
    ::// var0 yyy : TvmBuilder; _ |.
    ::// yyy -> store (xxx) ; _ |.
    ::// var0 zzz :_:= yyy -> toCell() -> toSlice () ; _ | .

    (* int round_since = s~load_uint(32); *)
    ::// var0 round_since:_:=s -> load(uint32);_|. 
    (* s.end_parse(); *)

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, parent)); *)
    ::// require_ (equal_TvmSlicebits(src, parent) , err_access_denied ) ;_|.

    ::// tokens += amount .

    ::// if(round_since) then { ->/> }.
    {
       (*  ( slice v, _ ) = ~udict_delete_get?(32, round_since); *)
       ::// var0 (v:TvmCell , __: int256) := udict_delete_get(staking,{32%Z},round_since); _ |.
       (*  int staking_coins = v~load_coins(); *)
       ::// var0 staking_coins: _ := s -> load(uint256);_|.
        (* v.end_parse(); *)
        ::// staking_coins -= coins.
        ::// if(staking_coins) then { ->/> } | .
        {
           ::// var0 r:TvmBuilder;_|.
           ::// r -> store (coins) .
            (* staking~udict_set_builder(32, round_since, begin_cell().store_coins(staking_coins)); *)
           ::// udict_set_builder( staking , {32%Z} , round_since, r ) | .
        }
    }

    (* raw_reserve(wallet_storage_fee(), reserve::at_most); *)
    ::// raw_reserve(wallet_storage_fee ( ), reserve_at_most ).

   (*  builder notification = begin_cell() *)
         ::// var0 notification : TvmBuilder ; _ |.
       (*  .store_uint(op::transfer_notification, 32) *)
         ::// notification -> store ( op_transfer_notification , {32:uint256}  ) .
        (* .store_uint(query_id, 64) *)
         ::// notification -> store (query_id , {64:uint256}) .
        (* .store_coins(amount) *)
        ::// notification -> store (amount) .
        (* .store_slice(owner) *)
        ::// notification -> store (owner) .
        (* .store_int(false, 1); *)
        ::// notification -> store ({false} , {1:uint256}) . 
    refine __return__.
}
return.
Defined.
Sync.

UseLocal Definition _ := [slice_;option(TvmSlice ** TvmCell)].


Ursus Definition isEmpty(s:option(TvmSlice ** TvmCell)):UExpression bool false.
{
    refine __return__.
}
return.
Defined.
Sync.

#[write = s]
Ursus Definition unstake_tokens (src:TvmSlice) (s:TvmSlice): UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_:=s -> load(int64);_|. 
    (* int amount = s~load_coins(); *)
    ::// var0 amount:_:=s -> load(int256);_|.

    (* slice return_excess = s~load_msg_addr(); *)
    ::// var0 return_address : address := s -> load (address) ; _ | .
    ::// var0 return_builder : TvmBuilder; _ |.
    ::// return_builder -> store (return_address) ; _ |.
    ::// var0 return_excess:_ := return_builder -> toCell() -> toSlice () ; _ |.

    (* cell custom_payload = s~load_maybe_ref(); *)
    ::// var0 custom_payload:_:= load_maybe_ref(s) ;_| .  

   (*  s.end_parse(); *)

    (* int mode = unstake::auto; *)
    ::// var0 mode:int256:= unstake_auto;_|.
    (* int ownership_assigned_amount = 0; *)
    ::// var0 ownership_assigned_amount:int256 := {0%Z};_|.   

    (* ifnot custom_payload.null?() { *)
    ::// if (! isEmpty (custom_payload) ) then { ->/> } . 
      {
        (* slice ss = custom_payload.begin_parse(); *)
        ::// var0 ss: TvmSlice := s ; _ | .
        (* mode = ss~load_uint(4); *)
        ::// mode := ss -> load(int256) . (* TODO : what is 4 ? *)

        (* ownership_assigned_amount = ss~load_coins(); *)
        ::// ownership_assigned_amount := ss -> load(int256) | .
       (*  ss.end_parse(); *)
    }

    (* int incoming_ton = get_incoming_value().pair_first(); *)
    ::// var0 incoming_ton:int256 := first ( get_incoming_value() );_|.

    (* int fee = unstake_tokens_fee() + ownership_assigned_amount; *)
    ::// var0 fee:int256 := unstake_tokens_fee() + ownership_assigned_amount;_|.

    (* int enough_fee? = incoming_ton >= fee; *)
    ::// var0 enough_fee:_:= incoming_ton >= fee;_|.

    (* int valid? = equal_TvmSlicebits(return_excess, owner) | (return_excess.addr_none?()); *)
    ::// var0 valid:_:= equal_TvmSlicebits(return_excess, owner) || addr_none(return_excess) ;_|.
      (* valid? &= (mode >= unstake::auto) & (mode <= unstake::best); *)
    ::// valid := valid && (mode >= unstake_auto ) && (mode <= unstake_best ) . 

(*  throw_unless(err_access_denied, equal_TvmSlicebits(src, owner) | equal_TvmSlicebits(src, my_address()));
    throw_unless(err_invalid_parameters, valid?);
    throw_unless(err_insufficient_fee, enough_fee?);
    throw_unless(err_insufficient_funds, (amount > 0) & (amount <= tokens)); *)

    ::// require_ ((equal_TvmSlicebits(src, owner)) 
                || (equal_TvmSlicebits(src, my_address())) , err_access_denied ) ;_|. 

    ::// require_ (valid  , err_invalid_parameters ) ;_|. 
    ::// require_ (enough_fee  , err_insufficient_fee ) ;_|. 
    ::// require_ ( (amount > {0%Z}) && (amount <= tokens)  , err_insufficient_funds ) ;_|. 

    ::// tokens -= amount .
    ::// unstaking += amount .

    (* builder reserve = begin_cell() *)
    ::// var0 reserve : TvmBuilder ; _ |.
        (* .store_uint(op::proxy_reserve_tokens, 32) *)
    ::// reserve -> store (op_proxy_reserve_tokens , {32:uint256} ) .
        (* .store_uint(query_id, 64) *)
    ::// reserve -> store (query_id , {64:uint256}) .
        (* .store_coins(amount) *)
    ::// reserve -> store (amount) .     
        (* .store_slice(owner) *)
    ::// reserve -> store (owner) .
       (*  .store_uint(mode, 4) *)
    ::// reserve -> store (mode , {4:uint256}) .
        (* .store_coins(ownership_assigned_amount); *)
    ::// reserve -> store (ownership_assigned_amount) .     
    ::// send_msg({true}, to_builder(parent) , nullB(), reserve, {0%Z}, send_remaining_value).
refine __return__.
}
return .
Defined.
Sync.

#[write = s]
Ursus Definition rollback_unstake(src:TvmSlice)(s:TvmSlice):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64);_| .
    (* int amount = s~load_coins(); *)
    ::// var0 amount:_ := s -> load(int256);_ | .
    (* s.end_parse(); *)

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, parent)); *)
    ::// require_ (equal_TvmSlicebits(src, parent) , err_access_denied );_| .

    ::// tokens += amount.
    ::// unstaking -= amount.

    (* builder excess = begin_cell() *)
    ::// var0 excess : TvmBuilder ; _ |.
    (* .store_uint(op::gas_excess, 32) *)
    ::// excess -> store (op_gas_excess (* , 32 *)) .
    (* .store_uint(query_id, 64); *)
    ::// excess -> store (query_id (* 64 *)) .
    ::// send_msg({false}, to_builder(owner), nullB(), excess, {0%Z}, send_remaining_value + send_ignore_errors).


refine __return__.
}
return .
Defined.
Sync.

#[write = s]
Ursus Definition tokens_burned (src:TvmSlice) (s:TvmSlice): UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64);_| .
    (* int amount = s~load_coins(); *)
    ::// var0 amount:_ := s -> load(int256);_ | .
    (* int coins = s~load_coins(); *)
    ::// var0 coins:_ := s -> load(int256);_ | .
    (* s.end_parse(); *)

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, parent)); *)
    ::// require_ (equal_TvmSlicebits(src, parent) , err_access_denied );_| .

    ::// unstaking -= amount .

    (* raw_reserve(wallet_storage_fee(), reserve::at_most); *)
    ::// raw_reserve(wallet_storage_fee ( ), reserve_at_most ).

    (* builder notification = begin_cell() *)
    ::// var0 notification : TvmBuilder ; _ |.
       (*  .store_uint(op::withdrawal_notification, 32) *)
    ::// notification -> store ( op_transfer_notification , {32:uint256} ) .
        (* .store_uint(query_id, 64) *)
    ::// notification -> store (query_id, {32:uint256} ) .
        (* .store_coins(amount) *)
    ::// notification -> store (amount) .
        (* .store_coins(coins); *)
    ::// notification -> store (coins) .
    ::// send_msg({false}, to_builder(owner), nullB(), notification, coins, send_unreserved_balance + send_ignore_errors). 
refine __return__.
}
return .
Defined.
Sync.


(* AL: not working from here *)
Ursus Definition unstake_all (src:TvmSlice) (s:TvmSlice): UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64 );_| .
    (* s.end_parse(); *)

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, parent) | equal_TvmSlicebits(src, owner)); *)
    ::// require_ (equal_TvmSlicebits(src, parent) || equal_TvmSlicebits(src, owner) , err_access_denied );_| .

    (* builder unstake = begin_cell() *)
    ::// var0 unstake : TvmBuilder ; _ |.
       (*  .store_uint(op::unstake_tokens, 32) *)
    ::// unstake -> store (op_unstake_tokens , {32:uint256} ) .
        (* .store_uint(query_id, 64) *)
    ::// unstake -> store (query_id, {64:uint256}) .
        (* .store_coins(tokens) *)
    ::// unstake -> store (tokens) .
        (* .store_uint(0, 3); ;; 00 (addr_none) + 0 (custom_payload) *)
    ::// unstake -> store ({0:uint256}, {3:uint256}) .
    ::// send_msg({false}, to_builder(my_address()) , nullB(), unstake, {0%Z}, send_remaining_value).
refine __return__.
}
return .
Defined.
Sync.

  Ursus Definition upgrade_wallet(src:TvmSlice)(s:TvmSlice):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64);_| .
    (* s.end_parse(); *)

    (* int incoming_ton = get_incoming_value().pair_first(); *)
    ::// var0 incoming_ton : int256 := first( get_incoming_value() );_|.

    ::// var0 fee:_ := upgrade_wallet_fee();_|.
    (* int fee = upgrade_wallet_fee(); *)

    (* int enough_fee? = incoming_ton >= fee; *)
    ::// var0 enough_fee:_:= incoming_ton >= fee;_|.

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, owner) | equal_TvmSlicebits(src, parent)); *)
    ::// require_(equal_TvmSlicebits(src, owner) || equal_TvmSlicebits(src, parent) , 
          err_access_denied);_|.
    (* throw_unless(err_insufficient_fee, enough_fee?); *)
    ::// require_(enough_fee , err_insufficient_fee );_|.

    (* builder migrate = begin_cell() *)
    ::// var0 migrate : TvmBuilder ; _ |.
        (* store_uint(op::proxy_migrate_wallet, 32) *)
    ::// migrate -> store (op_proxy_migrate_wallet , {32:uint256} ) .
        (* .store_uint(query_id, 64) *)
    ::// migrate -> store (query_id, {64:uint256}) .
        (* .store_coins(tokens) *)
    ::// migrate -> store (tokens) .
        (* .store_slice(owner); *)
    ::// migrate -> store (owner) .
    ::// send_msg({true}, to_builder(parent) , nullB(), migrate, {0%Z}, send_unreserved_balance).
  
    (* tokens = 0; *)
    ::// tokens := {0%Z} .
refine __return__.
}
return .
Defined.
Sync.


  Ursus Definition merge_wallet(src:TvmSlice)(s:TvmSlice):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64);_| .
    (* int new_tokens = s~load_coins(); *)
    ::// var0 new_tokens:_ := s -> load(int256);_ | .

    (* s.end_parse(); *)

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, parent)); *)
    ::// require_ (equal_TvmSlicebits(src, parent) , err_access_denied );_|.

    ::// tokens += new_tokens. 

    ::// raw_reserve(wallet_storage_fee(), reserve_at_most ) .

    (* builder excess = begin_cell() *)
    ::// var0 excess : TvmBuilder ; _ |.
        (* .store_uint(op::gas_excess, 32) *)
    ::// excess -> store ( op_gas_excess , {32:uint256} ) .
         (* .store_uint(query_id, 64); *)
    ::// excess -> store (query_id , {64:uint256} ) .
    ::// send_msg({false}, to_builder(owner) , nullB(), excess, {0%Z}, send_unreserved_balance + send_ignore_errors).
refine __return__.
}
return .
Defined.
Sync.


Ursus Definition withdraw_surplus(src:TvmSlice)(s:TvmSlice):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64);_| .
    (* slice return_excess = s~load_msg_addr(); *)
    ::// var0 return_address : address := s -> load (address) ; _ | .
    ::// var0 return_builder : TvmBuilder; _ |.
    ::// return_builder -> store (return_address) ; _ |.
    ::// var0 return_excess:_ := return_builder -> toCell() -> toSlice () ; _ |.
    (* s.end_parse(); *)

    (* if return_excess.addr_none?() {
        return_excess = src;
    } *)
    ::// if(addr_none(return_excess)) then { ->> }.
    {
        ::// return_excess := src | .
    }

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, owner)); *)
    ::// require_ (equal_TvmSlicebits(src, owner) , err_access_denied );_|.
    ::// raw_reserve(wallet_storage_fee(), reserve_at_most);_|.

    (* builder excess = begin_cell() *)
    ::// var0 excess : TvmBuilder ; _ |.
        (* .store_uint(op::gas_excess, 32) *)
    ::// excess -> store (op_gas_excess , {32:uint256} ) .
        (* .store_uint(query_id, 64); *)
    ::// excess -> store (query_id , {64:uint256} ) .
    ::// send_msg({false}, to_builder(return_excess) , nullB(), excess, {0%Z}, send_unreserved_balance + send_ignore_errors).
    ::// revert_ ({0}) .
refine __return__.
}
return .
Defined.
Sync.

Ursus Definition withdraw_jettons(src:TvmSlice)(s:TvmSlice):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64);_| .
    (* slice child_wallet = s~load_msg_addr(); *)
    ::// var0 child_address : address := s -> load (address) ; _ | .
    ::// var0 child_builder : TvmBuilder; _ |.
    ::// child_builder -> store (child_address) ; _ |.
    ::// var0 child_wallet:_ := child_builder -> toCell() -> toSlice () ; _ |.
    (* int tokens = s~load_coins(); *)
    ::// var0 tokens:_ := s -> load(int256);_ | .
    (* cell custom_payload = s~load_maybe_ref(); *)
    ::// var0 custom_payload:_:= load_maybe_ref(s) ;_| .  
    (* s.end_parse(); *)

    (* throw_unless(err_access_denied, equal_TvmSlicebits(src, owner)); *)
    ::// require_ (equal_TvmSlicebits(src, owner) , err_access_denied);_|.

    (* builder send = begin_cell() *)
    ::// var0 send' : TvmBuilder ; _ |.
        (* .store_uint(op::send_tokens, 32) *)
    ::// send' -> store (op_send_tokens , {32:uint256}) .
        (* .store_uint(query_id, 64) *)
    ::// send' -> store (query_id , {64:uint256}) .
        (* .store_coins(tokens) *)
    ::// send' -> store (tokens) .
        (* .store_slice(owner) *)
    ::// send' -> store (owner) .
        (* .store_slice(owner) *)
    ::// send' -> store (owner) .
       (*  .store_maybe_ref(custom_payload) *)
    ::// send' -> store ( custom_payload ) .   
        (* .store_coins(0) *)
    ::// send' -> store ({}) .
        (* .store_int(false, 1); *)
    ::// send' -> store ({false} , {1:uint256}) .
    ::// send_msg({true}, to_builder(child_wallet), nullB(), send' , {0%Z}, send_remaining_value).

    ::// revert_ ({0}).
refine __return__.
}
return .
Defined.
Sync.

Ursus Definition on_bounce(src:TvmSlice)(s:TvmSlice):UExpression PhantomType true.
{
    (* s~load_uint(32); *)
    ::// var0 xxx:_ := s -> load(int32);_| .
    (* int op = s~load_uint(32); *)
    ::// var0 op:_ := s -> load(int32);_| .
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_ := s -> load(int64);_| .

    ::// if(op == op_receive_tokens ) then { ->/> } .
    {
        (* int amount = s~load_coins(); *)
       ::// var0 amount:_ := s -> load(int256);_ | .
       ::// tokens += amount | .
    }

    ::// if(op == op_proxy_reserve_tokens ) then { ->/> } .
     {   (* int amount = s~load_coins(); *)
       ::// var0 amount:_ := s -> load(int256);_ | .
        (* tokens += amount; *)
       ::// tokens += amount .
       ::// unstaking -= amount | .
    }

    ::// if(op ==  op_proxy_migrate_wallet ) then { ->/> } .
    {   (*  int amount = s~load_coins(); *)
       ::// var0 amount:_ := s -> load(int256);_ | .
        (* tokens += amount; *)
       ::// tokens += amount | .
    }

    ::// if(op == op_send_tokens ) then { ->> } .
    {
       (* ;; do nothing *)
       ::// tokens := tokens | .
    }

   (*  ;; send back excess gas to owner which is usually the original sender *)
   (*  builder excess = begin_cell() *)
    ::// var0 excess : TvmBuilder ; _ |.
        (* .store_uint(op::gas_excess, 32) *)
    ::// excess -> store (op_gas_excess , {32:uint256} ) .
        (* .store_uint(query_id, 64); *)
    ::// excess -> store (query_id , {64:uint256}) .
    ::// send_msg({false}, to_builder(owner), nullB(), excess, {0%Z}, send_remaining_value + send_ignore_errors) .
refine __return__.
}
return .
Defined.
Sync.

UseLocal Definition _ := [uint16].

Ursus Definition route_internal_message(flags:int256)(src:TvmSlice)(s:TvmSlice)(cs:TvmSlice):UExpression PhantomType true.
{
    (* if flags & 1 { *)
    ::// if(flags && {1%Z}) then { ->/> } . 
    {    (* return on_bounce(src, s); *)
        ::// exit_ (on_bounce(src, s)) | .
    }

    (* int op = s~load_uint(32); *)
    ::// var0 op :_ := s -> load(int32);_| .

    ::// if(op == op_send_tokens ) then { ->/> } .
     {   (* cs~load_msg_addr(); ;; skip dst *)
        ::// var0 _address : address := s -> load (address) ; _ | .
        ::// var0 _builder : TvmBuilder; _ |.
        ::// _builder -> store (_address) ; _ |.
        ::// var0 __address:_ := _builder -> toCell() -> toSlice () ; _ |.
        (* cs~load_coins(); ;; skip value *)
        ::// var0 x1:_ := s -> load(int256);_ | .
        (* cs~skip_bits(1); ;; skip extracurrency collection *)
        ::// (* cs~ *)skip_bits({}) .
        (* cs~load_coins(); ;; skip ihr fee *)
        ::// var0 x2:_ := s -> load(int256);_ | .
        (* int fwd_fee = get_original_fwd_fee(cs~load_coins(), false); ;; use fwd_fee to estimate forward_payload cost *)
        ::// var0 fwd_fee:_:= get_original_fwd_fee((* cs->load(int256) *) {} , {false});_| .
        ::// send_tokens( src ,  s ,  fwd_fee ) | .
    }

    (* if op == op::receive_tokens { *)
    ::// if(op == op_send_tokens ) then { ->/> } .
    {
        ::// exit_ receive_tokens(src, s) | .
    }

    (* if op == op::tokens_minted {
        return tokens_minted(src, s);
    } *)
    ::// if(op == op_tokens_minted ) then { ->/> } .
    {
        ::// exit_ tokens_minted(src, s) | .
    }

    (* if op == op::save_coins {
        return save_coins(src, s);
    } *)
    ::// if(op == op_save_coins ) then { ->/> } .
    {
        ::// exit_ save_coins(src, s) | .
    }

    (* if op == op::unstake_tokens {
        return unstake_tokens(src, s);
    } *)
    ::// if(op == op_unstake_tokens ) then { ->/> } .
    {
        ::// exit_ unstake_tokens(src, s) | .
    }

    (* if op == op::rollback_unstake {
        return rollback_unstake(src, s);
    } *)
    ::// if(op == op_rollback_unstake ) then { ->/> } .
    {
        ::// exit_ rollback_unstake(src, s) | .
    }

    (* if op == op::tokens_burned {
        return tokens_burned(src, s);
    } *)
    ::// if(op == op_tokens_burned ) then { ->/> } .
    {
        ::// exit_ tokens_burned(src, s) | .
    }

    (* if op == op::unstake_all {
        return unstake_all(src, s);
    } *)
    ::// if(op == op_unstake_all ) then { ->/> } .
    {
        ::// exit_ unstake_all(src, s) | .
    }

    (* if op == op::upgrade_wallet {
        return upgrade_wallet(src, s);
    } *)
    ::// if(op == op_upgrade_wallet ) then { ->/> } .
    {
        ::// exit_ upgrade_wallet(src, s) | .
    }

   (*  if op == op::merge_wallet {
        return merge_wallet(src, s);
    } *)
    ::// if(op == op_merge_wallet ) then { ->/> } .
    {
        ::// exit_ merge_wallet(src, s) | .
    }

    (* if op == op::withdraw_surplus {
        return withdraw_surplus(src, s);
    } *)
    ::// if(op == op_withdraw_surplus ) then { ->/> } .
    {
        ::// exit_ withdraw_surplus(src, s) | .
    }

    (* if op == op::withdraw_jettons {
        return withdraw_jettons(src, s);
    } *)
    ::// if(op == op_withdraw_jettons ) then { ->/> } .
    {
        ::// exit_ withdraw_jettons(src, s) | .
    }

    (* if op == op::top_up {
        throw(0); ;; top up TON balance, do nothing
    } *)
    ::// if(op == op_top_up ) then { ->/> } .
    {
        ::// revert_({0}) | . 
    }

    ::// if(op == {0%Z} ) then { ->/> } .
    {  (* int c = s~load_uint(8); *)
      ::// var0 c :_ := s -> load(int256 (* 8 *));_| .
        (* s.end_parse(); *)

        ::// c |= {0x20%Z} .  (* ; ;; convert to lowercase *) 

(*      if c == "w"u { (* ASCII-code of "w" *)
            return unstake_all(src, "0000000000000000"s);
        } *)

       ::// if(c == {} (* "w"u *) ) then { ->/> } . (* TODO *)
        {
             ::// var0 bnul : TvmBuilder;_|.
             ::// bnul -> store ({0:uint16});_|.
             ::// exit_ unstake_all(src, bnul -> toCell() -> toSlice() (* "0000000000000000"s *)) | . (* TODO *)
        }

        ::// require_ ( {false}, err_invalid_comment ) | .
    }

    ::// require_( {false}, err_invalid_op ) .
refine __return__.
}
return .
Defined.
Sync.

Ursus Definition recv_internal(in_msg_full:TvmCell)(s:TvmSlice):UExpression PhantomType true.
{
    (* slice cs = in_msg_full.begin_parse(); *) 
    ::// var0 cs: TvmSlice := in_msg_full -> toSlice() ; _ | .  

    (* int flags = cs~load_uint(4); *)
    ::// var0 flags :_ := cs -> load(int256 (* 4 *));_| .

    (* slice src = cs~load_msg_addr(); *)
    ::// var0 src_address : address := cs -> load (address) ; _ | .
    ::// var0 src_builder : TvmBuilder; _ |.
    ::// src_builder -> store (src_address) ; _ |.
    ::// var0 src:_ := src_builder -> toCell() -> toSlice () ; _ |.

    ::// load_data().
    ::// route_internal_message(flags, src, s, cs) .
    ::// save_data() .
refine __return__.
}
return .
Defined.
Sync.

(* (int, slice, slice, cell) get_wallet_data () method_id { *)

  Ursus Definition get_wallet_data:UExpression (int256 ** TvmSlice ** TvmSlice ** TvmCell) true.
{
    ::// load_data() .
refine __return__.
}
return  (* tokens, owner, parent, my_code() *)  .
Defined.
Sync.

(* (int, cell, int) get_wallet_state() method_id { *)
  Ursus Definition get_wallet_state:UExpression (int256 ** TvmCell ** int256) true.
{
    ::// load_data() .
refine __return__.
}
return (* ( tokens, staking, unstaking ) *) .
Defined.
Sync.

(* var get_wallet_fees() method_id { *)
(* #[returns=ret] *)
  Ursus Definition method_id : UExpression (int256 ** int256 ** int256 ** int256) false.
{
    (* int forward_fee = get_forward_fee(1 + 3, 1023 ** 2, false); *)
    ::// var0 forward_fee:_:=get_forward_fee({1} + {3}, {1023} ** {2}, {false});_|.
    (* ::// ret := ( send_tokens_fee() + forward_fee
        , unstake_tokens_fee()
        , upgrade_wallet_fee()
        , wallet_storage_fee()
        ). *)
refine __return__.
}
return . 
Defined.
Sync.


EndContract Implements .
GenerateLocalState 0 HipoWallet.
GenerateLocalState 1 HipoWallet.
GenerateLocalState HipoWallet.








