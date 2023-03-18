(*
 * Importing the Libraries
 *)
Require Import Init.Decimal.
Require Import Reals.
Require Import Floats.
Require Import List.
Require Import Coq.Strings.String.
From OracleFormalization Require Export Hexadecimal.

(*
 * IMPORTANT
 * weight is interpreted as float
 * reads and writes : float
 * What to do if the address doesn't exist in the mapping?
 *)

Inductive Event : Type :=
    | DataWritten (newData : float) (newCost : nat) (caller : address)
    | DataRead (consumer : address) (weight : nat) (data : float)
    | WeightAdjustmentScheduled (consumer : address) (caller : address) (weightNext : nat) (timeStamp : nat) (weightTimelock : nat) 
    | WeightAdjusted (consumer : address) (caller : address) (timeStamp : nat) (weight : nat)
    | MaxFeeAdjustmentScheduled (maxFeeNextNew : nat) (caller : address) (timeStamp : nat) (maxFeeTimelock : nat) 
    | MaxFeeAdjusted (caller : address) (timeStamp : nat) (maxFee : nat)
    | BaseFeeAdjusted (caller : address) (writes : nat) (reads : nat) (fee : nat)
    | CreditDeposited (consumer : address) (deposit : nat)
    | CreditWithdrawn (amount : nat) (caller : address)
    | RevenueWithdrawn (receiver : address) (amount : nat) (caller : address)
    | Reset (cost : nat) (revenue : nat).

Definition Trace : Type := list (Event).

Record ConsumerInfo :=
{
    credit         : nat;
    latestRead     : nat;
    weight         : nat;
    weightNext     : nat;
    weightTimeLock : nat
}.

Definition AllConsumers   := list (address * ConsumerInfo).

Record OracleState :=
{
    data           : float;
    time           : nat;
    totalCost      : nat;
    totalRevenue   : nat;
    writes         : nat;
    reads          : nat;
    baseFee        : nat;
    maxFee         : nat;
    maxFeeNext     : nat;
    maxFeeTimeLock : nat;
    latestCost     : nat;
    latestWrite    : nat;
    totalCredit    : nat;
    allConsumers   : AllConsumers
}.

Record OracleParameters :=
{
    owner         : address;
    description   : string;
    lockingPeriod : nat
}.

Record State :=
{
    oracleState      : OracleState;
    oracleParameters : OracleParameters;
    trace            : Trace
}.
