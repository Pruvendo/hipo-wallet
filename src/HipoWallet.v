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
Constants ;
(* Definition MAX_UINT256 : uint256 := 1
Definition MAX_UINT256_3 : uint256 := 5 
Definition kokoko : string := "kokoko" 
Definition Bool : bool := true; *)

Record Contract := {
    owner: TvmSlice;
    parent: TvmSlice;
    tokens: int256;
    staking: TvmCell;
    unstaking: int256
} .

SetUrsusOptions.

UseLocal Definition _ := [ TvmBuilder ; 
                           optional TvmBuilder; 
                           address ; 
                           int256 ;
                           uint256 ;
                          int64 ;
                          uint64 ;
                          bool;
                           TvmCell ; 
                           TvmSlice ; 
                           (optional (TvmCell ** TvmSlice));
                           (optional (address ** TvmSlice));
PhantomType;
                           (optional (int256 ** TvmSlice)) ].

Print Instances SolTypable.
Locate "int".

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

(* TVM stubs *)


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

(* ************************************************************************* *)

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
    ::// var0 owner_address : address := ds -> load (address) ; _ | .
    ::// var0 owner_builder : TvmBuilder; _ |.
    ::// owner_builder -> store (owner_address) ; _ |.
    ::// owner := owner_builder -> toCell() -> toSlice () .
    (* parent = ds~load_msg_addr(); *)
    ::// var0 parent_address : address := ds -> load (address) ; _ | .
    ::// var0 parent_builder : TvmBuilder; _ |.
    ::// parent_builder -> store (parent_address) ; _ |.
    ::// parent := parent_builder -> toCell() -> toSlice () .
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

Ursus Definition load_maybe_ref : UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.

Ursus Definition skip_dict : UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.

Ursus Definition impure_touch : UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.

Ursus Definition send_tokens_fee : UExpression int256 false.
{
    refine __return__.
}
return \\ tokens.
Defined.
Sync.

Ursus Definition equal_slice_bits(src:slice_)(owner:slice_) : UExpression bool false.
{
    refine __return__. 
}
return true.
Defined.
Sync.

Ursus Definition my_address : UExpression slice_ false.
{
    refine __return__. 
}
return \\ parent.
Defined.
Sync.

Ursus Definition send_tokens(src:slice_)(s:slice_)(fwd_fee:uint256):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id: _ := s -> load(int256); _ | . (* ????????????????? *)
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
    ::// load_maybe_ref() .                            (* ????????????????? *)

    (* int forward_ton_amount = s~load_coins(); *)
    ::// var0 forward_ton_amount:_:= s->load(int256);_|.

    (* slice forward_payload = s; *)
    ::// var0 forward_payload:_:=s;_|.

    (* s~skip_dict(); ;; check either field *)
    ::// skip_dict().                (* ????????????????? *)

    (* s~impure_touch(); *)
    :://impure_touch().                (* ????????????????? *)

    (* if return_excess.addr_none?() {
        return_excess = src;
    } *)
    :://if({} (* return_excess->isEmpty() *)) then {->>} .  (* ????????????????? *)
       { ::// return_excess := src | . }

    (* ( int recipient_wc, _ ) = parse_std_addr(recipient); *)
(*    ::// var0 ( recipient_wc , _ ) := parse_std_addr(slice) ;_|. parse_std_addr(recipient); *)

(*     ( builder wallet, builder state_init, _ ) = create_wallet_address(recipient.to_builder(), parent, my_code()); *)

    (* int incoming_ton = get_incoming_value().pair_first(); *)
    ::// var0 incoming_ton:int256:= {} (* get_incoming_value().pair_first() *); _ | .

    (* int fee = send_tokens_fee() + forward_ton_amount + (forward_ton_amount ? 2 : 1) * fwd_fee; *)
    ::// var0 fee:int256:= send_tokens_fee() + forward_ton_amount (* + (forward_ton_amount ? {2} : {1}) * fwd_fee *);_|.

    (* int enough_fee? = incoming_ton >= fee; *)
    ::// var0 enough_fee:bool:= incoming_ton >= fee;_|.

(*     throw_unless(err::only_basechain_allowed, recipient_wc == chain::base);
    throw_unless(err::access_denied, equal_slice_bits(src, owner));
    throw_unless(err::insufficient_fee, enough_fee?);
    throw_unless(err::insufficient_funds, amount <= tokens);
    throw_if(err::receiver_is_sender, equal_slice_bits(recipient, owner));
 *)

   ::// require_ ((* recipient_wc *) {true} == {true} (* chain::base , err::only_basechain_allowed *) ) ;_ | .
   ::// require_ (equal_slice_bits(src, owner) (*, err::access_denied *) ) ;_ | .
   ::// require_ (enough_fee (* , err::insufficient_fee *) ) ;_ | .
   ::// require_ (amount <= tokens (* , err::insufficient_funds *) ) ;_ | .
   ::// require_ (equal_slice_bits(recipient, owner) (* , err::receiver_is_sender *) ) ;_ | .

    (* tokens -= amount; *)
    ::// tokens -= amount.

    (* builder receive = begin_cell() *)
         ::// var0 b : TvmBuilder ; _ |.
        (* .store_uint(op::receive_tokens, 32) *)
         ::// b -> store ({}(* op::receive_tokens, 32 *)) .
        (* .store_uint(query_id, 64) *)
         ::// b -> store (query_id(* , 64 *)) .
       (* .store_coins(amount) *)
         ::// b -> store (amount ) .
        (* .store_slice(owner) *)
        ::// b -> store (owner) .
        (* .store_slice(return_excess) *)
        ::// b -> store (return_excess) .
        (* .store_coins(forward_ton_amount) *)
        ::// b -> store (forward_ton_amount) .
        (* .store_slice(forward_payload); *)
        ::// b -> store (forward_payload) .
     (* send_msg(true, wallet, state_init, receive, 0, send::remaining_value); *)
    refine __return__. 
}
return.
Defined.
Sync.

Ursus Definition get_storage_fee : UExpression int256 false.
{
    refine __return__.
}
return \\ tokens.
Defined.
Sync.

Ursus Definition wallet_storage_fee:UExpression int256 false.
{
    ::// var0 cells:uint256:= {1} + {1};_|.
    ::// var0 bits:uint256:= {267} + {267} + {124};_|. 
    ::// var0 duration:uint256:= {60} * {60} * {24} * {365} * {5}; _|.
    refine __return__.
}
return  \\ tokens(* get_storage_fee(cells, bits, duration, false) *).
Defined.
Sync.

Ursus Definition raw_reserve(amount:int256)(mode:int256) : UExpression PhantomType false.
{
    refine __return__.
}
return.
Defined.
Sync.




Ursus Definition receive_tokens(src:slice_)(s:slice_):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_:=s -> load(int256);_|. (* ????????????????????? *)

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
    (* ( int src_wc, int src_addr ) = parse_std_addr(src); *)

    (* throw_unless(err::access_denied, (src_wc == chain::base) & (src_addr == wallet_addr)); *)
    ::// require_ (((* src_wc *) {true} == {true} (* chain::base *)) 
                       && ((* src_addr *) {true} == {true} (* wallet_addr *)) (* , err::access_denied *) ) ;_ | .

    ::// tokens += amount.

    ::// if(forward_ton_amount) then { ->/> }.
       {
        (* builder notification = begin_cell() *)
         ::// var0 notification : TvmBuilder ; _ |.
        (* .store_uint(op::transfer_notification, 32) *)
         ::// notification -> store ({}(* op::receive_tokens, 32 *)) .
        (* .store_uint(query_id, 64) *)
         ::// notification -> store (query_id(* , 64 *)) .
            (* .store_slice(sender) *)
        ::// notification -> store (sender) .
            (* .store_slice(forward_payload); *)
        ::// notification -> store (forward_payload) | .
        (* send_msg(false, owner.to_builder(), null(), notification, forward_ton_amount,
            send::pay_gas_separately + send::bounce_if_failed ); *)
       }

    ::// raw_reserve(wallet_storage_fee ( ), {} (* reserve::at_most *)).

    (* builder excess = begin_cell() *)
         ::// var0 excess : TvmBuilder ; _ |.
        (* .store_uint(op::gas_excess, 32) *)
         ::// excess -> store ({} (* op::gas_excess, 32 *)) .
        (* .store_uint(query_id, 64); *)
         ::// excess -> store (query_id(* , 64 *)) .
(*     send_msg(false, return_excess.to_builder(), null(), excess, 0, send::unreserved_balance + send::ignore_errors); *)

    refine __return__. 
}
return.
Defined.
Sync.

Ursus Definition udict_set_builder(x:int256)(round_since:int256)(y:TvmBuilder):UExpression PhantomType true.
{
    ::// require_ ({true});_|.
    refine __return__.
}
return.
Defined.
Sync.

Ursus Definition tokens_minted(src:slice_)(s:slice_):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_:=s -> load(int256);_|. (* ????????????????????? *)
   (*  int amount = s~load_coins(); *)
    ::// var0 amount:_:=s -> load(int256);_|.
    (* int coins = s~load_coins(); *)
    ::// var0 coins:_:=s -> load(int256);_|.
    (* s~load_msg_addr(); ;; skip owner address *) 
    ::// var0 xxx : address := s -> load (address) ; _ | .
    ::// var0 yyy : TvmBuilder; _ |.
    ::// yyy -> store (xxx) ; _ |.
    ::// var0 zzz :_:= yyy -> toCell() -> toSlice () ; _ | .

    (* int round_since = s~load_uint(32); *)
    ::// var0 round_since:_:=s -> load(int256);_|. (* ????????????????????? *)
    (* s.end_parse(); *)

    (* throw_unless(err::access_denied, equal_slice_bits(src, parent)); *)
    ::// require_ (equal_slice_bits(src, parent) (*, err::access_denied *) ) ;_|.

    ::// tokens += amount .

    ::// if(round_since) then { ->/> }.
    {
       (*  ( slice v, _ ) = staking~udict_delete_get?(32, round_since); *)
       (*  int staking_coins = v~load_coins(); *)
       ::// var0 staking_coins:_:=s -> load(int256);_|.
        (* v.end_parse(); *)
        ::// staking_coins -= coins.
        ::// if(staking_coins) then { ->/> } | .
        {
            ::// var0 qqq : TvmBuilder ; _ |.
            (* staking~udict_set_builder(32, round_since, begin_cell().store_coins(staking_coins)); *)
           ::// (* staking~ *) udict_set_builder({}, {} (* round_since *) , {} (* qqq -> store(staking_coins)*)) | .
        }
    }

    (* raw_reserve(wallet_storage_fee(), reserve::at_most); *)
    ::// raw_reserve(wallet_storage_fee ( ), {} (* reserve::at_most *)).

   (*  builder notification = begin_cell() *)
         ::// var0 notification : TvmBuilder ; _ |.
       (*  .store_uint(op::transfer_notification, 32) *)
         ::// notification -> store ({}(* op::transfer_notification, 32 *)) .
        (* .store_uint(query_id, 64) *)
         ::// notification -> store (query_id(* 64 *)) .
        (* .store_coins(amount) *)
        ::// notification -> store (amount) .
        (* .store_slice(owner) *)
        ::// notification -> store (owner) .
        (* .store_int(false, 1); *)
        ::// notification -> store ({false} (*  *)) . (* ????????????????????? *)
    refine __return__.
}
return.
Defined.
Sync.

Ursus Definition save_coins(src:slice_)(s:slice_):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_:=s -> load(int256);_|. (* ????????????????????? *)
    (* int coins = s~load_coins(); *)
    ::// var0 coins:_:=s -> load(int256);_|.
    (* s~load_msg_addr(); ;; skip owner address *)
    ::// var0 xxx : address := s -> load (address) ; _ | .
    ::// var0 yyy : TvmBuilder; _ |.
    ::// yyy -> store (xxx) ; _ |.
    ::// var0 zzz :_:= yyy -> toCell() -> toSlice () ; _ | .
    (* int round_since = s~load_uint(32); *)
    ::// var0 round_since:_:=s -> load(int256);_|. (* ????????????????????? *)
    (* s.end_parse(); *)

    (* throw_unless(err::access_denied, equal_slice_bits(src, parent)); *)
    ::// require_ (equal_slice_bits(src, parent) (* , err::access_denied *) ) ; _ | .

    (* ( slice v, int f? ) = staking.udict_get?(32, round_since); *)
    ::// if ({true})(* f? *) then { ->> } .
    {
        (* coins += v~load_coins(); *)
        ::// coins += {} (* v -> load (int256) *) | .
        (* v.end_parse(); *)
    }
    (* staking~udict_set_builder( 32 , round_since, begin_cell().store_coins(coins)); *)
    ::// (* staking~ *)udict_set_builder( {} (* 32 *) , round_since, {} (* begin_cell().store_coins(coins) *)) | .
}
return.
Defined.
Sync.

Ursus Definition get_compute_fee(x:int256)(y:bool):UExpression int256 false.
{
    refine __return__.
}
return \\ tokens.
Defined.
Sync.

Ursus Definition get_forward_fee(x:uint256)(y:uint256)(z:bool):UExpression int256 false.
{
    refine __return__.
}
return \\ tokens.
Defined.
Sync.

Ursus Definition unstake_tokens_fee:UExpression int256 false.
{
    (* int compute_gas = *)
    ::// var0 compute_gas:int256 := {} ;_|.
(*         gas::unstake_tokens +
        gas::proxy_reserve_tokens +
        gas::reserve_tokens +
        gas::mint_bill +
        gas::assign_bill +
        gas::burn_bill +
        gas::bill_burned +
        gas::burn_tokens +
        gas::mint_bill +   ;; second try
        gas::assign_bill + ;; second try
        gas::burn_bill +   ;; second try
        gas::bill_burned + ;; second try
        gas::burn_tokens + ;; second try
        gas::proxy_tokens_burned +
        gas::tokens_burned; *)
    (* int compute_fee = get_compute_fee(compute_gas, false); *)
    ::// var0 compute_fee:_:= get_compute_fee(compute_gas, {false}); _| .

    (* int s_fwd_fee = get_forward_fee(0, 0, false);
    int m_fwd_fee = get_forward_fee(1, 1023, false);
    int l_fwd_fee = get_forward_fee(1 + 3, 1023 * 2, false); *)
    ::// var0 s_fwd_fee:_:= get_forward_fee({0}, {0}, {false}); _| .
    ::// var0 m_fwd_fee:_:= get_forward_fee({1}, {1023}, {false}); _| .
    ::// var0 l_fwd_fee:_:= get_forward_fee({1} + {3}, {1023} * {2}, {false}); _| .

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
    refine __return__.
}
return \\ tokens. (* compute_fee + forward_fee; *)
Defined.
Sync.


Ursus Definition unstake_tokens(src:slice_)(s:slice_):UExpression PhantomType true.
{
    (* int query_id = s~load_uint(64); *)
    ::// var0 query_id:_:=s -> load(int256);_|. (* ????????????????????? *)
    (* int amount = s~load_coins(); *)
    ::// var0 amount:_:=s -> load(int256);_|.

    (* slice return_excess = s~load_msg_addr(); *)
    ::// var0 return_address : address := s -> load (address) ; _ | .
    ::// var0 return_builder : TvmBuilder; _ |.
    ::// return_builder -> store (return_address) ; _ |.
    ::// var0 return_excess:_ := return_builder -> toCell() -> toSlice () ; _ |.

    (* cell custom_payload = s~load_maybe_ref(); *)
    ::// var0 custom_payload:_:= (* s -> *)load_maybe_ref() ;_| .  (* ????????????????? *)

   (*  s.end_parse(); *)

    (* int mode = unstake::auto; *)
    ::// var0 mode:int256:= {} (* unstake::auto *);_|.
    (* int ownership_assigned_amount = 0; *)
    ::// var0 ownership_assigned_amount:int256 := {};_|.   (* ????????????????? *)

    (* ifnot custom_payload.null?() { *)
    ::// if (!{true})(* custom_payload.null?() *) then { ->/> } .
      {
        (* slice ss = custom_payload.begin_parse(); *)
        ::// var0 ss: TvmSlice := tvm_get_data () (* custom_payload *) -> toSlice() ; _ | .  (* ????????????????? *)
        (* mode = ss~load_uint(4); *)
        ::// mode := ss -> load(int256 (* 4 *)) .

        (* ownership_assigned_amount = ss~load_coins(); *)
        ::// ownership_assigned_amount := ss -> load(int256) | .
       (*  ss.end_parse(); *)
    }

    (* int incoming_ton = get_incoming_value().pair_first(); *)
    ::// var0 incoming_ton:int256 := {} (* get_incoming_value().pair_first() *);_|.

    (* int fee = unstake_tokens_fee() + ownership_assigned_amount; *)
    ::// var0 fee:int256 := unstake_tokens_fee() + ownership_assigned_amount;_|.

    (* int enough_fee? = incoming_ton >= fee; *)
    ::// var0 enough_fee:_:= incoming_ton >= fee;_|.

    (* int valid? = equal_slice_bits(return_excess, owner) | (return_excess.addr_none?()); *)
    ::// var0 valid:_:= equal_slice_bits(return_excess, owner) || {} (*return_excess.addr_none?()*);_|.
      (* valid? &= (mode >= unstake::auto) & (mode <= unstake::best); *)
    (* TODO may be there arent boolean operations for int256? *)
    (* (* ::// valid &= (mode >= tokens (* unstake::auto *)) && (mode <= tokens (* unstake::best *)) . *) *)

(*  throw_unless(err::access_denied, equal_slice_bits(src, owner) | equal_slice_bits(src, my_address()));
    throw_unless(err::invalid_parameters, valid?);
    throw_unless(err::insufficient_fee, enough_fee?);
    throw_unless(err::insufficient_funds, (amount > 0) & (amount <= tokens)); *)

    ::// require_ ((equal_slice_bits(src, owner)) 
                 || (equal_slice_bits(src, my_address() (* , err::access_denied *)) ) ) ;_|. 
    ::// require_ (valid (* , err::invalid_parameters *)) ;_|. 
    ::// require_ (enough_fee (* , err::insufficient_fee *)) ;_|. 
    (* TODO may be there arent boolean operations for int256? *)
    ::// require_ ( {true} (* (amount > {0}) && (amount <= tokens) *) (* , err::insufficient_funds *)) ;_|. 

    ::// tokens -= amount .
    ::// unstaking += amount .

    (* builder reserve = begin_cell() *)
    ::// var0 reserve : TvmBuilder ; _ |.
        (* .store_uint(op::proxy_reserve_tokens, 32) *)
    ::// reserve -> store ({} (* op::proxy_reserve_tokens, 32 *)) .
        (* .store_uint(query_id, 64) *)
    ::// reserve -> store (query_id (* 64 *)) .
        (* .store_coins(amount) *)
    ::// reserve -> store (amount) .     
        (* .store_slice(owner) *)
    ::// reserve -> store (owner) .
       (*  .store_uint(mode, 4) *)
    ::// reserve -> store (mode (* 4 *)) .
        (* .store_coins(ownership_assigned_amount); *)
    ::// reserve -> store (ownership_assigned_amount) .     
    (* send_msg(true, parent.to_builder(), null(), reserve, 0, send::remaining_value); *)
refine __return__.
}
return .
Defined.
Sync.

() rollback_unstake(slice src, slice s) impure inline {
    int query_id = s~load_uint(64);
    int amount = s~load_coins();
    s.end_parse();

    throw_unless(err::access_denied, equal_slice_bits(src, parent));

    tokens += amount;
    unstaking -= amount;

    builder excess = begin_cell()
        .store_uint(op::gas_excess, 32)
        .store_uint(query_id, 64);
    send_msg(false, owner.to_builder(), null(), excess, 0, send::remaining_value + send::ignore_errors);
}





