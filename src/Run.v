Require Import HipoWallet.
Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import UrsusContractCreator.UrsusEndContract.
Require Export UrsusContractCreator.UrsusStartContract.
Require Import UrsusContractCreator.Templates.
Require Import Common.

SetUrsusOptions.


Set Project Root "/home/ivan/devel/wallet-spec" .
Set Project Source Path  "/src/".
Set Header Name "Common" .
Set Temporary Path "src/_Templates".
Set Execs Path "Execs".
Set Evals Path "Evals".
Set Common Path "/src/".

Elpi FormingExecs HipoWallet.
Elpi FormingEvals HipoWallet.
