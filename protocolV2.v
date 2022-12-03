(*
 * Importing the Libraries
 *)
Require Import Init.Decimal.
Require Import Reals.
Require Import Floats.
Require Import List.
Require Import Coq.Strings.String.
From ORACLE Require Export defs.


(*
 * HELPER FUNCTIONS
 *)
Definition max_nat (num1 : nat) (num2 : nat) : nat :=
    if (num1 <? num2)
    then
        num2
    else
        num1.

Definition min_nat (num1 : nat) (num2 : nat) : nat :=
    if (num1 <? num2)
    then
        num1
    else
        num2.

Definition get_total_revenue (state : State) : nat :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleState) with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
          maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
          totalCredit, allConsumers) =>  totalRevenue
        end
    end.

Definition get_consumers (state : State) : AllConsumers :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleState) with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
            maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
            totalCredit, allConsumers) =>  allConsumers
            end
    end.


Definition get_latest_write (state : State) : LatestWrite :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleState) with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
            maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
            totalCredit, allConsumers) => latestWrite
        end
    end.


Definition get_base_fee (state : State) : nat :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleState) with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
            maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
            totalCredit, allConsumers) => baseFee
        end
    end.

Definition get_owner (state : State) : address :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (owner, _, _) => owner
        end
    end.

Definition get_description (state : State) : string :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (_, description, _) => description
        end
    end.

Definition get_locking_period (state : State) : nat :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (_, _, lockingPeriod) => lockingPeriod
        end
    end.

    
Definition get_trace (state : State) : list (Events) :=
    match (state) with
    | ((oracleState, oracleParameters), trace) => trace
    end.

(* 
 * This function checks if a consumer with the address 'consumer' exists in the target list
 *)
 Fixpoint consumer_exists (consumer : address) (type : Type) (targetList : list (address * type)) : bool :=
    match (targetList) with
    | nil => false
    | (addr, _) :: targetList' => 
        match (compare_address (addr) (consumer)) with
        | true => true
        | _ => consumer_exists (consumer) (type) (targetList')
        end
    end.


(* 
 * This function checks if the targetList is empty or not
 *)
Definition not_empty (type : Type) (targetList : list (address * type)) : Prop :=
    match targetList with
    | nil => False
    | (addr, _) :: targetList' => True
    end.

(*
 * Assuming the element already exists in the array and only one such address exists
 *)
Fixpoint modify_list (type : Type) (targetList : list (address * type)) (targetAddress : address) (elem : type) (current_list : list (address * type)) : list (address * type) :=
    match targetList with
    | nil => current_list
    | (addr, oldElem) :: targetList' => 
        if (compare_address (addr) (targetAddress))
        then
            current_list ++ ((addr, elem) :: nil) ++ targetList'
        else
            modify_list (type) (targetList') (targetAddress) (elem) (current_list ++ ((addr, oldElem) :: nil))
    end.

Fixpoint get_consumer_info (allConsumers : list (address * ConsumerInfo)) (targetAddress : address) : ConsumerInfo :=
    match allConsumers with
    | nil => 
        Build_ConsumerInfo (0) (0) (0) (0) (0)
    | (addr, info) :: allConsumers' =>
        if (compare_address (addr) (targetAddress))
        then
            info 
        else
            get_consumer_info (allConsumers') (targetAddress)
    end.

Definition get_latest_read_consumer (consumer : address) (state : State) : nat :=
    let consumerInfo := get_consumer_info (get_consumers (state)) (consumer) in
        consumerInfo.(LatestRead).

Definition register_consumer (consumer : address) (consumerList : AllConsumers) (credit : nat) (latestRead : nat)
                             (weight : nat) (weightNext : nat) (weightTimelock : nat) : AllConsumers :=
    let newConsumer := Build_ConsumerInfo (credit) (latestRead) (weight) (weightNext) (weightTimelock) in
    (consumer, newConsumer) :: consumerList.


(*
 * Function Definitions
 *)

Definition constructor (owner : address) (description : string) 
                        (lockingPeriod : nat) (baseFee : nat) : State :=
    let oracleState := (0 % float, 0, 0, 0, 0, baseFee, 
                        (baseFee * 3), 0, 0, 0, 
                        0, 0, nil) in
        let oracleParameters := (owner, description, lockingPeriod) in
            ((oracleState, oracleParameters), nil).


Definition write_data (state : State) (newData : float) (newCost : nat) (timeStamp : nat) (caller : address) : State :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match oracleParameters with
        | (owner, _, _) =>
            if (compare_address (owner) (caller))
            then
                match oracleState with
                | (data, totalCost, b, writes, c, d, e, f, g, latestCost, latestWrite, j, k) =>
                    let newOracleState := (newData, (totalCost + newCost), b, (writes + 1), c, d, e, f, g, 
                                            newCost, timeStamp, j, k) in
                        let newEvent := DataWritten (newData) (newCost) (timeStamp) (caller) in
                            ((newOracleState, oracleParameters), trace ++ (newEvent :: nil))
                end
            else
                state
        end
    end.

Definition weight_of (consumer : address) (allConsumers : AllConsumers) : nat :=
    let consumerInfo := get_consumer_info (allConsumers) (consumer) in
        consumerInfo.(Weight).
    

Definition fee_of (consumer : address) (weight : nat) (allConsumers : AllConsumers) (latestWrite : nat) (baseFee : nat) : nat :=
    let consumerInfo := get_consumer_info (allConsumers) (consumer) in
        if (latestWrite <? consumerInfo.(LatestRead))
        then
            0
        else
            (weight * baseFee).

Definition fee_of_public (consumer : address) (state : State) : nat :=
    match state with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleState) with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
          maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
          totalCredit, allConsumers) => 
            fee_of (consumer) (weight_of (consumer) (allConsumers)) (allConsumers) (latestWrite) (baseFee)
        end
    end.

Definition get_credit_consumer (consumer : address) (allConsumers : AllConsumers) : nat :=
    let consumerInfo := get_consumer_info (allConsumers) (consumer) in
        consumerInfo.(Credit).
    


Definition read_data (state : State) (consumer : address) (timeStamp : nat) : (State * ValueOption float) :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleState) with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
          maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
          totalCredit, allConsumers) =>
            let consumerInfo := get_consumer_info (allConsumers) (consumer) in 
            let weight := consumerInfo.(Weight) in
            let fee := fee_of (consumer) (weight) (allConsumers) (latestWrite) (baseFee) in
            let credit := consumerInfo.(Credit) in
                if (credit <? fee)
                then 
                    (state, None float)
                else
                    let newConsumerInfo := Build_ConsumerInfo (credit - fee) (timeStamp) 
                        (consumerInfo.(Weight)) (consumerInfo.(WeightNext)) (consumerInfo.(WeightTimeLock)) in
                    let newOracleState := (data, totalCost, (totalRevenue + fee), writes, (reads + weight),
                        baseFee, maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite,
                        (totalCredit - fee), modify_list (ConsumerInfo) (allConsumers) (consumer) (newConsumerInfo) (nil)) in
                        (((newOracleState, oracleParameters), trace ++ ((DataRead (consumer) (timeStamp) (weight) (data)) :: nil)), Some float (data))
        end
    end.

Definition inspectData (caller : address) (state : State) : ValueOption float :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (owner, _, _) =>
            if (compare_address (owner) (caller))
            then
                match (oracleState) with
                | (data, totalCost, totalRevenue, writes, reads, baseFee, 
                  maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                  totalCredit, allConsumers) => Some float (data)
                end
            else 
                None float
        end
    end.

Definition schedule_weight_adjustment (consumer : address) (caller : address) (weightNext : nat) (timeStamp : nat) (state : State) : State :=
    match state with
    | ((oracleState, oracleParameters), trace) =>
        match oracleState with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
          maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
          totalCredit, allConsumers) =>
            match (oracleParameters) with
            | (owner, _, lockingPeriod) =>
                if (compare_address (owner) (caller))
                then
                    let consumerInfo := get_consumer_info (allConsumers) (consumer) in  
                    let scheduleTime := timeStamp + lockingPeriod in
                    let newConsumerInfo := Build_ConsumerInfo (consumerInfo.(Credit)) (consumerInfo.(LatestRead))
                        (consumerInfo.(Weight)) (weightNext) (scheduleTime) in
                    let newConsumers := modify_list (ConsumerInfo) (allConsumers) (consumer) (newConsumerInfo) (nil) in
                    let newOracleState := 
                        (data, totalCost, totalRevenue, writes, reads, baseFee, 
                        maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                        totalCredit, newConsumers) in
                            ((newOracleState, oracleParameters), 
                            trace ++ ((WeightAdjustmentScheduled (consumer) (caller) (weightNext) (timeStamp) (scheduleTime)) :: nil))
                else
                    state
            end
        end
    end.


Definition adjust_weight (consumer : address) (caller : address) (timeStamp : nat) (state : State) : State :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (owner, _, _) =>
            if (compare_address (owner) (caller))
            then
                match (oracleState) with
                | (data, totalCost, totalRevenue, writes, reads, baseFee, 
                  maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                  totalCredit, allConsumers) =>
                    let consumerInfo := get_consumer_info (allConsumers) (consumer) in
                        if (timeStamp <? consumerInfo.(WeightTimeLock))
                        then
                            state
                        else
                            let newConsumerInfo := Build_ConsumerInfo (consumerInfo.(Credit)) (consumerInfo.(LatestRead))
                                (consumerInfo.(WeightNext)) (consumerInfo.(WeightNext)) (consumerInfo.(WeightTimeLock)) in
                            let newConsumers := modify_list (ConsumerInfo) (allConsumers) (consumer) (newConsumerInfo) (nil) in
                            let newOracleState := 
                                (data, totalCost, totalRevenue, writes, reads, baseFee, 
                                maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                                totalCredit, newConsumers) in
                                ((newOracleState, oracleParameters), trace ++ ((WeightAdjusted (consumer) (caller) (timeStamp) (newConsumerInfo.(Weight))) :: nil))
                end
            else
                state
        end
    end.


Definition schedule_max_fee_adjustment (maxFeeNextNew : nat) (caller : address) (timeStamp : nat) (state : State) : State :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (owner, _, lockingPeriod) =>
            if (compare_address (owner) (caller))
            then
                match (oracleState) with
                | (data, totalCost, totalRevenue, writes, reads, baseFee, 
                  maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                  totalCredit, allConsumers) =>
                    let newOracleState :=
                        (data, totalCost, totalRevenue, writes, reads, baseFee, 
                        maxFee, maxFeeNextNew, timeStamp + lockingPeriod, latestCost, latestWrite, 
                        totalCredit, allConsumers)
                    in
                        ((newOracleState, oracleParameters), trace ++ ((MaxFeeAdjustmentScheduled (maxFeeNextNew) (caller) (timeStamp) (timeStamp + lockingPeriod)) :: nil))
                end
            else
                state
        end
    end.

Definition adjust_max_fee (caller : address) (timeStamp : nat) (state : State) : State :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (owner, _, _) =>
            if (compare_address (owner) (caller))
            then
                match (oracleState) with
                | (data, totalCost, totalRevenue, writes, reads, baseFee, 
                  maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                  totalCredit, allConsumers) =>
                    if (timeStamp <? maxFeeTimelock)
                    then
                        state
                    else
                        let newOracleState :=
                            (data, totalCost, totalRevenue, writes, reads, baseFee, 
                            maxFeeNext, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                            totalCredit, allConsumers)
                        in
                            ((newOracleState, oracleParameters), trace ++ ((MaxFeeAdjusted (caller) (timeStamp) (maxFeeNext)) :: nil))
                end
            else
                state
        end
    end.



Definition adjust_base_fee (caller : address) (state : State) : State :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (owner, _, _) =>
            if (compare_address (owner) (caller))
            then
                match (oracleState) with
                | (data, totalCost, totalRevenue, writes, reads, baseFee, 
                  maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                  totalCredit, allConsumers) =>
                    let readsDiv :=
                        if (reads =? 0)
                        then
                            1
                        else
                            reads
                    in
                        let addCent :=
                            if (((((latestCost * writes) + totalCost) - totalRevenue) mod readsDiv) =? 0)
                            then
                                0
                            else
                                1 
                        in
                        let newBaseFee := min (((((latestCost * writes) + totalCost) - totalRevenue) / readsDiv) + addCent) (maxFee) in
                        let newOracleState :=
                            (data, totalCost, totalRevenue, 0, 0, newBaseFee, 
                            maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                            totalCredit, allConsumers) in
                            ((newOracleState, oracleParameters), trace ++ ((BaseFeeAdjusted (caller) (writes) (reads) (newBaseFee)) :: nil))
                end
            else
                state
        end
    end.

Definition deposit_credit (consumer : address) (state : State) (deposit : nat) : State :=
    match state with
    | ((oracleState, oracleParameters), trace) =>
        match oracleState with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
          maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
          totalCredit, allConsumers) =>
            let consumerInfo := get_consumer_info (allConsumers) (consumer) in
            let newAllConsumers :=
                if (consumerInfo.(Weight) =? 0)
                then
                    register_consumer (consumer) (allConsumers) (deposit) (0) (1) (0) (0)
                else
                    let newConsumerInfo := Build_ConsumerInfo ((consumerInfo.(Credit) + deposit))
                        (consumerInfo.(LatestRead)) (consumerInfo.(Weight)) (consumerInfo.(WeightNext))
                        (consumerInfo.(WeightTimeLock)) in
                    modify_list (ConsumerInfo) (allConsumers) (consumer) (newConsumerInfo) (nil)
            in
                let newOracleState := 
                    (data, totalCost, totalRevenue, writes, reads, baseFee, 
                    maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                    (totalCredit + deposit), newAllConsumers) in
                    ((newOracleState, oracleParameters), trace ++ ((CreditDeposited (consumer) (deposit)) :: nil))
        end
    end.


Definition withdraw_credit (amount : nat) (caller : address) (state : State) : State :=
    match state with
    | ((oracleState, oracleParameters), trace) =>
        match oracleState with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
          maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
          totalCredit, allConsumers) =>
            let consumerInfo := get_consumer_info (allConsumers) (caller) in
            if (consumerInfo.(Credit) <? amount)
            then
                state
            else
            let newConsumerInfo := Build_ConsumerInfo ((consumerInfo.(Credit) - amount)) (consumerInfo.(LatestRead))
                                    (consumerInfo.(Weight)) (consumerInfo.(WeightNext)) (consumerInfo.(WeightTimeLock)) in
            let newConsumers := modify_list (ConsumerInfo) (allConsumers) (caller) (newConsumerInfo) (nil) in
            let newOracleState := 
                (data, totalCost, totalRevenue, writes, reads, baseFee, 
                maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                (totalCredit - amount), newConsumers) in

                ((newOracleState, oracleParameters), trace ++ ((CreditWithdrawn (amount) (caller)) :: nil))
        end
    end.

Definition withdraw (receiver : address) (amount : nat) (caller : address) (state : State) : State :=
    match (state) with
    | ((oracleState, oracleParameters), trace) =>
        match (oracleParameters) with
        | (owner, _, _) =>
            if (compare_address (owner) (caller))
            then
                match (oracleState) with
                | (data, totalCost, totalRevenue, writes, reads, baseFee, 
                  maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                  totalCredit, allConsumers) =>
                    if ((totalRevenue - totalCredit) <? amount)
                    then
                        state
                    else
                        let newOracleState :=
                            (data, totalCost, (totalRevenue - amount), writes, reads, baseFee, 
                            maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                            totalCredit, allConsumers)
                        in
                            ((newOracleState, oracleParameters), trace ++ ((RevenueWithdrawn (receiver) (amount) (caller)) :: nil))
                end
            else
                state
        end
    end.

Definition reset_cost_and_revenue (state : State) : State :=
    match state with
    | ((oracleState, oracleParameters), trace) =>
        match oracleState with
        | (data, totalCost, totalRevenue, writes, reads, baseFee, 
          maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
          totalCredit, allConsumers) =>
            let (newTotalCost, newTotalRevenue) := 
                if ((totalRevenue <? totalCost))
                then
                    ((totalCost - totalRevenue), 0)
                else
                    (0, (totalRevenue - totalCost))
            in
                let newOracleState := 
                    (data, newTotalCost, newTotalRevenue, writes, reads, baseFee, 
                    maxFee, maxFeeNext, maxFeeTimelock, latestCost, latestWrite, 
                    totalCredit, allConsumers)
                in
                    ((newOracleState, oracleParameters), trace ++ ((Reset (totalCost) (totalRevenue)) :: nil))
        end
    end.


Definition execute (state : State) (event : Events) : State :=
    match event with
    | DataWritten (newData) (newCost) (timeStamp) (caller) => write_data (state) (newData) (newCost) (timeStamp) (caller)
    | DataRead (consumer) (timeStamp) (_) (_) => 
        let (newState, _) := read_data (state) (consumer) (timeStamp) 
        in
            newState
    | WeightAdjustmentScheduled (consumer) (caller) (weightNext) (timeStamp) (_) => 
        schedule_weight_adjustment (consumer) (caller) (weightNext) (timeStamp) (state)
    | WeightAdjusted (consumer) (caller) (timeStamp) (_) => adjust_weight (consumer) (caller) (timeStamp) (state)
    | MaxFeeAdjustmentScheduled (maxFeeNextNew) (caller) (timeStamp) (_) => schedule_max_fee_adjustment (maxFeeNextNew) (caller) (timeStamp) (state)
    | MaxFeeAdjusted (caller) (timeStamp) (_) => adjust_max_fee (caller) (timeStamp) (state)
    | BaseFeeAdjusted (caller) (_) (_) (_) => adjust_base_fee (caller) (state)
    | CreditDeposited (consumer) (deposit) => deposit_credit (consumer) (state) (deposit)
    | CreditWithdrawn (amount) (caller) => withdraw_credit (amount) (caller) (state)
    | RevenueWithdrawn (receiver) (amount) (caller) => withdraw (receiver) (amount) (caller) (state)
    | Reset (_) (_) => reset_cost_and_revenue (state)
    end.