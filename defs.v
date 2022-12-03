(*
* Importing the Libraries
*)
Require Import Init.Decimal.
Require Import Reals.
Require Import Floats.
Require Import List.
Require Import Coq.Strings.String.
From ORACLE Require Export Hexadecimal.

(*
* IMPORTANT
* weight is interpreted as float
* reads and writes : float
* What to do if the address doesn't exist in the mapping?
*)

(*
* Definitions
*)
Record ConsumerInfo :=
{
    Credit : nat;
    LatestRead : nat;
    Weight : nat;
    WeightNext : nat;
    WeightTimeLock : nat
    
}.

Definition Owner := address.
Definition Data := float.
Definition TotalCost := nat.
Definition TotalRevenue := nat.
Definition Writes := nat.
Definition Reads := nat.
Definition BaseFee := nat.
Definition MaxFee := nat.
Definition MaxFeeNext := nat.
Definition MaxFeeTimeLock := nat.
Definition LatestCost := nat.
Definition LatestWrite := nat.
Definition TotalCredit := nat.
Definition AllConsumers := list (address * ConsumerInfo).


Inductive ValueOption (type : Type) : Type :=
    | Some (val : type)
    | None.


Inductive Events : Type :=
    | DataWritten (newData : float) (newCost : nat) (timeStamp : nat) (caller : address)
    | DataRead (consumer : address) (timeStamp : nat) (weight : nat) (data : float)
    | WeightAdjustmentScheduled (consumer : address) (caller : address) (weightNext : nat) (timeStamp : nat) (weightTimelock : nat) 
    | WeightAdjusted (consumer : address) (caller : address) (timeStamp : nat) (weight : nat)
    | MaxFeeAdjustmentScheduled (maxFeeNextNew : nat) (caller : address) (timeStamp : nat) (maxFeeTimelock : nat) 
    | MaxFeeAdjusted (caller : address) (timeStamp : nat) (maxFee : nat)
    | BaseFeeAdjusted (caller : address) (writes : nat) (reads : nat) (fee : nat)
    | CreditDeposited (consumer : address) (deposit : nat)
    | CreditWithdrawn (amount : nat) (caller : address)
    | RevenueWithdrawn (receiver : address) (amount : nat) (caller : address)
    | Reset (cost : nat) (revenue : nat).

Definition Trace : Type :=
    list (Events).
(*
 * Oracle State represented as (data, totalCost, totalRev, writes, reads, baseFee,
    maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, totalCredit, allConsumers)
 *)
Definition OracleState : Type :=
    (Data * TotalCost * TotalRevenue * Writes * Reads * BaseFee * MaxFee * MaxFeeNext * 
    MaxFeeTimeLock * LatestCost * LatestWrite * TotalCredit * AllConsumers).

(*
 * Oracle Parameters represented as (owner, description, timeLockPeriod)
 *)
Definition OracleParameters : Type :=
    (Owner * string * nat).

Definition Oracle : Type :=
    (OracleState * OracleParameters).

Definition State : Type :=
(Oracle * Trace).
