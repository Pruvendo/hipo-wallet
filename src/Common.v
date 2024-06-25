Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import HipoWallet.
Import HipoWallet.

Definition rec := LocalStateLRecord.

Goal LedgerLRecord rec -> True.
intros ll. destruct_ledger ll.  
Abort.

#[global, program]
Instance listInfinite : listInfiniteFunRec_gen XList.
Next Obligation.
(* TODO: we need to analyze all while/for cycles
   and find upper bound for number of iterations *)
exact (repeat PhantomPoint 0).
Defined.

Definition computed : LocalStateLRecord := Eval vm_compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 

Definition EverMessageDefault: EverMessage := Eval vm_compute in default.
Definition VMStateDefault : VMStateLRecord  := Eval vm_compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval vm_compute in default. 

Elpi Accumulate rec_def lp:{{
  get_rec {{ rec }}.
  get_def {{ def }}.
}}.

AddPropLibraryBindings.

(* build call graph for analyzing dependencies *)
Elpi BuildStaticCallGraph HipoWallet.
Definition graph := Eval compute in updateTreeList HipoWalletStaticTreeList.

(* names of functions for which we need to create eval *)
(* if all functions are needed, we can read this info from ContractMeta3 *)
Compute (List.map ItemName (ContractMethods ContractMeta3)).
Definition roots_eval : Datatypes.list string := (
                                       "send_msg"::
                                       "wallet_storage_fee"::
                                       "send_tokens_fee"::
                                       "create_wallet_data"::
                                       "create_state_init"::
                                       "create_address"::
                                       "create_wallet_address"::
                                       "unstake_tokens_fee"::
                                       "upgrade_wallet_fee"::
                                       "save_data"::
                                       "load_msg_addr"::
                                       "load_data"::
                                       "save_coins"::
                                       "send_tokens"::
                                       "receive_tokens"::
                                       "tokens_minted"::
                                       "unstake_tokens"::
                                       "rollback_unstake"::
                                       "tokens_burned"::
                                       "unstake_all"::
                                       "upgrade_wallet"::
                                       "merge_wallet"::
                                       "withdraw_surplus"::
                                       "withdraw_jettons"::
                                       "on_bounce"::
                                       "route_internal_message"::
                                       "recv_internal"::
                                       "get_wallet_data"::
                                       "get_wallet_fees"::
                                       "get_wallet_state":: Datatypes.nil)%list.
(* names of functions for which we need to create exec*)
Definition roots_exec : Datatypes.list string := (
                                       "send_msg"::
                                       "wallet_storage_fee"::
                                       "send_tokens_fee"::
                                       "create_wallet_data"::
                                       "create_state_init"::
                                       "create_address"::
                                       "create_wallet_address"::
                                       "unstake_tokens_fee"::
                                       "upgrade_wallet_fee"::
                                       "save_data"::
                                       "load_msg_addr"::
                                       "load_data"::
                                       "save_coins"::
                                       "send_tokens"::
                                       "receive_tokens"::
                                       "tokens_minted"::
                                       "unstake_tokens"::
                                       "rollback_unstake"::
                                       "tokens_burned"::
                                       "unstake_all"::
                                       "upgrade_wallet"::
                                       "merge_wallet"::
                                       "withdraw_surplus"::
                                       "withdraw_jettons"::
                                       "on_bounce"::
                                       "route_internal_message"::
                                       "recv_internal"::
                                       "get_wallet_data"::
                                       "get_wallet_fees"::
                                       "get_wallet_state":: Datatypes.nil)%list .

(* add all dependencies of roots *)
Definition execs_for_roots_ := Eval compute in (execs_for_roots roots_eval roots_exec graph).
Definition evals_for_roots_ := Eval compute in (evals_for_roots roots_eval roots_exec graph).

(* compute import-map: what imports are needed for each proof *)
(* instead of Datatypes.nil, you can add "common" evals and execs -- which all proofs must import *)
Definition imports_execs_ := Eval compute in (imports_execs Datatypes.nil Datatypes.nil graph).
Definition imports_evals_ := Eval compute in (imports_evals Datatypes.nil Datatypes.nil graph).

Elpi Command AddExternalCallUnfolds.
Elpi Accumulate Db readers_utils.
Elpi Accumulate lp:{{

  :before "fold-map:start"
  fold-map (global C) A (global C) A1 :- 
    coq.gref->id C ID,
    if (rex.match "λ.*" ID)
    (A1 = [ID|A]) (A1 = A).

  pred compute_new_unfolds i:string, o:string.
  compute_new_unfolds S NUNF :-
    coq.locate S (const C),
    coq.env.const C (some T) _,
    fold-map T [] _ RES,
    if (RES = []) (NUNF = "")
    (std.string.concat ", " RES NUNF',
    NUNF is " unfold " ^ NUNF' ^ "."),
    coq.say NUNF.

  pred process_old_unfolds i:term, o:term.
  process_old_unfolds {{Datatypes.nil}} {{Datatypes.nil}}.
  process_old_unfolds 
    {{Datatypes.cons (lp:S, lp:OUNF) lp:R }}
    {{Datatypes.cons (lp:S, lp:UNF) lp:R' }} :-
      process_old_unfolds R R',
      term->string_cut S S',
      compute_new_unfolds S' NUNF,
      term->string_cut OUNF OUNF',
      UNF' is OUNF' ^ NUNF,
      coq.string->term UNF' UNF.

  main [str S] :-
    coq.locate S (const C),
    coq.env.const C (some T) _,
    process_old_unfolds T T',
    std.assert-ok! (coq.elaborate-skeleton T' _ TFINAL) "Error",
    coq.env.add-const "unfold_strings_" TFINAL _ _ _.
}}.
Elpi Typecheck.
Elpi Export AddExternalCallUnfolds.

(* compute unfold-map: what unfolds are needed for each eval/exec *)
Definition unfold_strings_' := Eval compute in (create_unfold_strings roots_eval roots_exec graph).

AddExternalCallUnfolds unfold_strings_'.

(* compute terminals (functions that don't call other functions) for use in matryoshka *)
Definition terminals := Eval compute in compute_terminals HipoWalletStaticTreeList.

(* starting state definition, nullify state variables, local state and isCommitted field *)
Definition stl (l: LedgerLRecord rec ) : LedgerLRecord rec := 
  Eval vm_compute in let vm_state := getPruvendoRecord Ledger_VMState l in
   {$$ {$$ {$$ l with Ledger_MainState := default $$} 
                                   with Ledger_LocalState := default $$}
                                   with Ledger_VMState := {$$ vm_state
                                      with VMState_ι_isCommitted := false $$} $$}.

