Require Import UrsusEnvironment.Solidity.current.Environment.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Import UrsusQC.ConvertPropToChecker.
Require Import UrsusQC.CreateDiagnostics.
Require Import UrsusQC.CommonQCEnvironment.
Require Import UrsusQC.VMStateGenerator.

Require Import CommonQC.
Require Import Common.

Require Import UrsusTVM.Solidity.tvmCellsBase.

Require Import HipoWallet.
Import HipoWallet.

Import MonadNotation.
Open Scope monad_scope.

Definition P7_v00_def
 (src:TvmSlice)(s:TvmSlice)
 (l: LedgerLRecord rec): Prop.
 add_computation (l) (tokens_burned rec def src s).
 elpi read_fields(l) "unstaking".
 elpi read_fields(l') "unstaking".
 condition (xIntGeb unstaking 0%Z = true).
 condition (ExecGenDefs.isError (eval_state (Uinterpreter (tokens_burned_simplified rec def src s)) l) = false).
 conclusion (xIntGeb unstaking' 0%Z = true).
Defined.

Close Scope xprod_scope.

Definition gen_slice (size : nat) : G TvmSlice :=
    a <- (arbitrarySized size : G Z) ;;
    b <- (arbitrarySized size : G Z) ;;
    c <- (arbitrarySized size : G Z) ;;
    ret (Wrap_TvmSlice
            (precell_push
                (precell_push
                    (precell_push 
                        EmptyPrecell 
                        (pack_sized 64 (a : int64)))
                    (pack_sized 256 (b : int256)))
                (pack_sized 256 (c : int256)))).

Definition int256_positive (size : nat) : G int256 :=
    i <- (arbitrarySized size : G int256) ;;
    if (xIntGeb i 0%Z : bool) then ret i else ret (xIntMult ((-1)%Z : int256) i).

Definition create_ledger 
    (l : LedgerLRecord rec)
    (parent : TvmSlice)
    (unstaking : int256) : LedgerLRecord rec :=
        let contract := getPruvendoRecord Ledger_MainState l in
        {$$ l with Ledger_MainState := 
            {$$ {$$ contract with _parent := parent $$}
                             with _unstaking := unstaking $$} $$}.

Definition gen_ledger (size : nat) : G (LedgerLRecord rec) :=
    unstaking <- int256_positive size ;;
    parent <- gen_slice size ;;
    l <- (arbitrarySized size : G (LedgerLRecord rec)) ;;
    ret (create_ledger l parent unstaking).

#[global]
Instance Slice_Gen : GenSized TvmSlice := {
    arbitrarySized size := gen_slice size
}.

(* Old getter/setter notations *)

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

(* Path to _parent variable *)
Definition Parent := LedgerLRecord rec ::> Ledger_MainState :> _parent.


(* Convert prop to checkable prop *)
ConvertPropToChecker P7_v00_def.

(* All Discarded *)
QuickCheck P7_v00_def_QC.

(* All passed *)
QuickCheck (forAll (gen_ledger 0) (fun l => fun s => P7_v00_def_QC (--> l with Parent) s l) ).