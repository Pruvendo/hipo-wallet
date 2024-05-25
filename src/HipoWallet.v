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
                          int64 ;
                           TvmCell ; 
                           TvmSlice ; 
                           (optional (TvmCell ** TvmSlice));
                           (optional (address ** TvmSlice));
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

}





