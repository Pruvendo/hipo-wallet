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