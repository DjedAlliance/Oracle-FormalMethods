(*
 * Importing the Libraries
 *)
Require Import Init.Decimal.
Require Import Reals.
Require Import Floats.
Require Import List.
Require Import Coq.Strings.String.
From OracleFormalization Require Export Datatypes.

(*
 * HELPER FUNCTIONS
 *)

Definition get_total_revenue (state : State) : nat :=
    state.(oracleState).(totalRevenue).

Definition get_consumers (state : State) : AllConsumers :=
    state.(oracleState).(allConsumers).

Definition get_latest_write (state : State) : LatestWrite :=
    state.(oracleState).(latestWrite).

Definition get_base_fee (state : State) : BaseFee :=
    state.(oracleState).(baseFee).

Definition get_owner (state : State) : Owner :=
    state.(oracleParameters).(owner).

Definition get_description (state : State) : string :=
    state.(oracleParameters).(description).

Definition get_locking_period (state : State) : nat :=
    state.(oracleParameters).(lockingPeriod).

Definition get_trace (state : State) : Trace :=
    state.(trace).

(*
 * Assuming the element already exists in the array and only one such address exists
 *)
Fixpoint modify_list (type : Type) 
                     (targetList : list (address * type)) 
                     (targetAddress : address) 
                     (elem : type) 
                     (current_list : list (address * type)) : list (address * type) :=
    match targetList with
    | nil => current_list
    | (addr, oldElem) :: targetList' => 
        if (compare_address (addr) (targetAddress))
        then
            current_list ++ ((addr, elem) :: nil) ++ targetList'
        else
            modify_list (type) (targetList') (targetAddress) (elem) (current_list ++ ((addr, oldElem) :: nil))
    end.

Fixpoint get_consumer_info (allConsumers : list (address * ConsumerInfo)) 
                           (targetAddress : address) : ConsumerInfo :=
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

Definition register_consumer (consumer : address) 
                             (consumerList : AllConsumers) 
                             (credit : nat) 
                             (latestRead : nat)
                             (weight : nat) 
                             (weightNext : nat) 
                             (weightTimelock : nat) : AllConsumers :=
    let 
      newConsumer := Build_ConsumerInfo (credit) (latestRead) (weight) (weightNext) (weightTimelock) 
    in
      (consumer, newConsumer) :: consumerList.


(*
 * FUNCTIONS
 * Corresponds to those in the oracle smart contract
 *)

Definition constructor (owner : address) 
                       (description : string) 
                       (lockingPeriod : nat) 
                       (baseFee : nat) : State :=
    let oracleState := Build_OracleState (0 % float) (0) (0) (0) (0) (0) (baseFee) 
                                         (baseFee * 3) (0) (0) (0) (0) (0) (nil) 
    in
    let oracleParameters := Build_OracleParameters (owner) (description) (lockingPeriod) 
    in
      Build_State (oracleState) (oracleParameters) (nil).


Definition write_data (state : State) 
                      (newData : float) 
                      (newCost : nat) 
                      (caller : address) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in
    let oldTrace := state.(trace) in

    if (compare_address (oldOracleParams.(owner)) (caller))
    then
        let newOracleState := Build_OracleState (newData) 
                                                (oldOracleState.(timeStamp) + 1) 
                                                (oldOracleState.(totalCost) + newCost) 
                                                (oldOracleState.(totalRevenue))
                                                (oldOracleState.(writes) + 1) 
                                                (oldOracleState.(reads)) 
                                                (oldOracleState.(baseFee)) 
                                                (oldOracleState.(maxFee))
                                                (oldOracleState.(maxFeeNext)) 
                                                (oldOracleState.(maxFeeTimeLock)) 
                                                (newCost) 
                                                (oldOracleState.(timeStamp) + 1) 
                                                (oldOracleState.(totalCredit))
                                                (oldOracleState.(allConsumers)) 
        in
        let newEvent := DataWritten (newData) (newCost) (caller) in
          Build_State (newOracleState) (oldOracleParams) (oldTrace ++ (newEvent :: nil))
    else
        state.

Definition weight_of (consumer : address) (allConsumers : AllConsumers) : nat :=
    let consumerInfo := get_consumer_info (allConsumers) (consumer) 
    in consumerInfo.(weight).

Definition fee_of (consumer : address) 
                  (weight : nat) 
                  (allConsumers : AllConsumers) 
                  (latestWrite : nat) 
                  (baseFee : nat) : nat :=
    let consumerInfo := get_consumer_info (allConsumers) (consumer) 
    in
      if (latestWrite <? consumerInfo.(latestRead))
      then 0
      else (weight * baseFee).

Definition fee_of_public (consumer : address) (state : State) : nat :=
    fee_of (consumer) 
           (weight_of (consumer) (state.(oracleState).(allConsumers))) 
           (state.(oracleState).(allConsumers)) 
           (state.(oracleState).(latestWrite)) 
           (state.(oracleState).(baseFee)).

Definition get_credit_consumer (consumer : address) (allConsumers : AllConsumers) : nat :=
    let consumerInfo := get_consumer_info (allConsumers) (consumer) in
    consumerInfo.(credit).

Definition read_data (state : State) (consumer : address) : (State * option float) :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in
    let oldTrace := state.(trace) in
    let consumerInfo := get_consumer_info (oldOracleState.(allConsumers)) (consumer) in 
    let weight := consumerInfo.(weight) in
    let fee := fee_of (consumer) (weight) 
                      (oldOracleState.(allConsumers)) 
                      (oldOracleState.(latestWrite)) 
                      (oldOracleState.(baseFee)) 
    in
    let credit := consumerInfo.(credit) in
    let data := oldOracleState.(data) 
    in
        if (credit <? fee)
        then (state, None)
        else
            let newConsumerInfo := Build_ConsumerInfo (credit - fee) 
                                                      (oldOracleState.(timeStamp) + 1) 
                                                      (weight) 
                                                      (consumerInfo.(weightNext)) 
                                                      (consumerInfo.(weightTimeLock))
            in
            let newList := modify_list (ConsumerInfo) 
                                       (oldOracleState.(allConsumers)) 
                                       (consumer) 
                                       (newConsumerInfo) 
                                       (nil)
            in
            let newOracleState := Build_OracleState (data) 
                                                    (oldOracleState.(timeStamp) + 1) 
                                                    (oldOracleState.(totalCost)) 
                                                    (oldOracleState.(totalRevenue) + fee) 
                                                    (oldOracleState.(writes)) 
                                                    (oldOracleState.(reads) + weight) 
                                                    (oldOracleState.(baseFee)) 
                                                    (oldOracleState.(maxFee))
                                                    (oldOracleState.(maxFeeNext)) 
                                                    (oldOracleState.(maxFeeTimeLock)) 
                                                    (oldOracleState.(latestCost)) 
                                                    (oldOracleState.(latestWrite))
                                                    (oldOracleState.(totalCredit) - fee) 
                                                    (newList) 
            in
            let newState := Build_State (newOracleState) 
                                        (oldOracleParams) 
                                        (oldTrace ++ ((DataRead (consumer) (weight) (data)) :: nil)) 
            in
              (newState, Some (data)).

Definition inspectData (caller : address) (state : State) : option float :=
    let oldOracleState  := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) 
    in
        if (compare_address (oldOracleParams.(owner)) (caller))
        then Some (oldOracleState.(data))
        else None.

Definition schedule_weight_adjustment (consumer : address) 
                                      (caller : address) 
                                      (weightNext : nat) 
                                      (blockTimeStamp : nat) 
                                      (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) 
    in
    if (compare_address (oldOracleParams.(owner)) (caller))
    then
        let consumerInfo := get_consumer_info (oldOracleState.(allConsumers)) (consumer) in  
        let scheduleTime := (blockTimeStamp + (oldOracleParams.(lockingPeriod))) in
        let newConsumerInfo := Build_ConsumerInfo (consumerInfo.(credit)) 
                                                  (consumerInfo.(latestRead))
                                                  (consumerInfo.(weight)) 
                                                  (weightNext) 
                                                  (scheduleTime) 
        in
        let newConsumers := modify_list (ConsumerInfo) 
                                        (oldOracleState.(allConsumers)) 
                                        (consumer) 
                                        (newConsumerInfo) 
                                        (nil) 
        in
        let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                                (oldOracleState.(timeStamp)) 
                                                (oldOracleState.(totalCost)) 
                                                (oldOracleState.(totalRevenue))
                                                (oldOracleState.(writes)) 
                                                (oldOracleState.(reads)) 
                                                (oldOracleState.(baseFee)) 
                                                (oldOracleState.(maxFee)) 
                                                (oldOracleState.(maxFeeNext)) 
                                                (oldOracleState.(maxFeeTimeLock)) 
                                                (oldOracleState.(latestCost)) 
                                                (oldOracleState.(latestWrite)) 
                                                (oldOracleState.(totalCredit)) 
                                                (newConsumers) 
        in
        let was := WeightAdjustmentScheduled (consumer) 
                                             (caller) 
                                             (weightNext) 
                                             (blockTimeStamp) 
                                             (scheduleTime)
        in
        let newState := Build_State (newOracleState) 
                                    (oldOracleParams)
                                    (oldTrace ++ (was :: nil))
        in
          newState
    else state.

Definition adjust_weight (consumer : address) (caller : address) (blockTimeStamp : nat) (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) 
    in
    if (compare_address (oldOracleParams.(owner)) (caller))
    then
        let consumerInfo := get_consumer_info (oldOracleState.(allConsumers)) (consumer) in
            if (blockTimeStamp <? consumerInfo.(weightTimeLock))
            then state
            else
                let newConsumerInfo := Build_ConsumerInfo (consumerInfo.(credit)) 
                                                          (consumerInfo.(latestRead))
                                                          (consumerInfo.(weightNext)) 
                                                          (consumerInfo.(weightNext)) 
                                                          (consumerInfo.(weightTimeLock)) 
                in
                let newConsumers := modify_list (ConsumerInfo) 
                                                (oldOracleState.(allConsumers)) 
                                                (consumer) 
                                                (newConsumerInfo) 
                                                (nil) 
                in
                let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                                        (oldOracleState.(timeStamp)) 
                                                        (oldOracleState.(totalCost)) 
                                                        (oldOracleState.(totalRevenue))
                                                        (oldOracleState.(writes)) 
                                                        (oldOracleState.(reads)) 
                                                        (oldOracleState.(baseFee)) 
                                                        (oldOracleState.(maxFee)) 
                                                        (oldOracleState.(maxFeeNext)) 
                                                        (oldOracleState.(maxFeeTimeLock)) 
                                                        (oldOracleState.(latestCost)) 
                                                        (oldOracleState.(latestWrite)) 
                                                        (oldOracleState.(totalCredit)) 
                                                        (newConsumers) 
                in
                let wa := WeightAdjusted (consumer) (caller) (blockTimeStamp) (newConsumerInfo.(weight)) in
                let newState := Build_State (newOracleState) 
                                            (oldOracleParams)
                                            (oldTrace ++ (wa :: nil)) 
                in
                newState
    else state.

Definition schedule_max_fee_adjustment (maxFeeNextNew : nat) 
                                       (caller : address) 
                                       (blockTimeStamp : nat) 
                                       (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) 
    in
    if (compare_address (oldOracleParams.(owner)) (caller))
    then
        let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                                (oldOracleState.(timeStamp)) 
                                                (oldOracleState.(totalCost)) 
                                                (oldOracleState.(totalRevenue)) 
                                                (oldOracleState.(writes)) 
                                                (oldOracleState.(reads)) 
                                                (oldOracleState.(baseFee)) 
                                                (oldOracleState.(maxFee)) 
                                                (maxFeeNextNew) 
                                                (blockTimeStamp + (oldOracleParams.(lockingPeriod))) 
                                                (oldOracleState.(latestCost)) 
                                                (oldOracleState.(latestWrite)) 
                                                (oldOracleState.(totalCredit)) 
                                                (oldOracleState.(allConsumers)) 
        in
        let mfas := MaxFeeAdjustmentScheduled (maxFeeNextNew) 
                                              (caller) 
                                              (blockTimeStamp) 
                                              (blockTimeStamp + oldOracleParams.(lockingPeriod))
        in
        let newState := Build_State (newOracleState) 
                                    (oldOracleParams)
                                    (oldTrace ++ (mfas :: nil)) 
        in
        newState
    else state.

Definition adjust_max_fee (caller : address) (blockTimeStamp : nat) (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) in

    if (compare_address (oldOracleParams.(owner)) (caller))
    then
        if (blockTimeStamp <? oldOracleState.(maxFeeTimeLock))
        then
            state
        else
            let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                                    (oldOracleState.(timeStamp)) 
                                                    (oldOracleState.(totalCost)) 
                                                    (oldOracleState.(totalRevenue)) 
                                                    (oldOracleState.(writes)) 
                                                    (oldOracleState.(reads)) 
                                                    (oldOracleState.(baseFee)) 
                                                    (oldOracleState.(maxFeeNext)) 
                                                    (oldOracleState.(maxFeeNext)) 
                                                    (oldOracleState.(maxFeeTimeLock)) 
                                                    (oldOracleState.(latestCost)) 
                                                    (oldOracleState.(latestWrite)) 
                                                    (oldOracleState.(totalCredit)) 
                                                    (oldOracleState.(allConsumers)) 
            in
            let mfa := MaxFeeAdjusted (caller) 
                                      (blockTimeStamp)
                                      (oldOracleState.(maxFeeNext)) 
            in
            let newState := Build_State (newOracleState) 
                                        (oldOracleParams) 
                                        (oldTrace ++ (mfa :: nil)) 
            in
            newState
    else state.

Definition adjust_base_fee (caller : address) (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) in

    if (compare_address (oldOracleParams.(owner)) (caller))
    then
        let readsDiv :=
            if (oldOracleState.(reads) =? 0)
            then 1
            else oldOracleState.(reads) 
        in
        let latestCost := oldOracleState.(latestCost) in
        let writes := oldOracleState.(writes) in
        let totalCost := oldOracleState.(totalCost) in
        let totalRevenue := oldOracleState.(totalRevenue) in
        let maxFee := oldOracleState.(maxFee) in
        let addCent :=
            if (((((latestCost * writes) + totalCost) - totalRevenue) mod readsDiv) =? 0)
            then 0
            else 1 
        in
        let newBaseFee := 
            if (((latestCost * writes) + totalCost) <=? totalRevenue)
            then 0
            else min (((((latestCost * writes) + totalCost) - totalRevenue) / readsDiv) + addCent) 
                     (maxFee) 
        in
        let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                                (oldOracleState.(timeStamp)) 
                                                (totalCost) 
                                                (totalRevenue) 
                                                (0) 
                                                (0) 
                                                (newBaseFee) 
                                                (maxFee) 
                                                (oldOracleState.(maxFeeNext)) 
                                                (oldOracleState.(maxFeeTimeLock)) 
                                                (latestCost) 
                                                (oldOracleState.(latestWrite)) 
                                                (oldOracleState.(totalCredit)) 
                                                (oldOracleState.(allConsumers)) 
        in
        let bfa := BaseFeeAdjusted (caller) (writes) (oldOracleState.(reads)) (newBaseFee) in
        let newState := Build_State (newOracleState) 
                                    (oldOracleParams)
                                    (oldTrace ++ (bfa :: nil)) 
        in
        newState
    else state.

Definition deposit_credit (consumer : address) (state : State) (deposit : nat) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) in
    let consumerInfo := get_consumer_info (oldOracleState.(allConsumers)) (consumer) in
    let newAllConsumers :=
        if (consumerInfo.(weight) =? 0)
        then
            register_consumer (consumer) (oldOracleState.(allConsumers)) (deposit) (0) (1) (0) (0)
        else
            let newConsumerInfo := Build_ConsumerInfo ((consumerInfo.(credit) + deposit))
                                                      (consumerInfo.(latestRead)) 
                                                      (consumerInfo.(weight)) 
                                                      (consumerInfo.(weightNext))
                                                      (consumerInfo.(weightTimeLock)) 
            in
              modify_list (ConsumerInfo) 
                          (oldOracleState.(allConsumers)) 
                          (consumer) 
                          (newConsumerInfo) 
                          (nil) 
    in
    let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                            (oldOracleState.(timeStamp)) 
                                            (oldOracleState.(totalCost)) 
                                            (oldOracleState.(totalRevenue)) 
                                            (oldOracleState.(writes)) 
                                            (oldOracleState.(reads)) 
                                            (oldOracleState.(baseFee)) 
                                            (oldOracleState.(maxFee)) 
                                            (oldOracleState.(maxFeeNext)) 
                                            (oldOracleState.(maxFeeTimeLock)) 
                                            (oldOracleState.(latestCost)) 
                                            (oldOracleState.(latestWrite)) 
                                            (oldOracleState.(totalCredit) + deposit) 
                                            (newAllConsumers) 
    in
    let cd := CreditDeposited (consumer) (deposit) in
    let newState := Build_State (newOracleState) 
                                (oldOracleParams)
                                (oldTrace ++ (cd :: nil)) 
    in
      newState.

Definition withdraw_credit (amount : nat) (caller : address) (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) in
    let consumerInfo := get_consumer_info (oldOracleState.(allConsumers)) (caller) 
    in
    if (consumerInfo.(credit) <? amount)
    then
        state
    else
    let newConsumerInfo := Build_ConsumerInfo ((consumerInfo.(credit) - amount)) 
                                              (consumerInfo.(latestRead))
                                              (consumerInfo.(weight)) 
                                              (consumerInfo.(weightNext)) 
                                              (consumerInfo.(weightTimeLock)) 
    in
    let newConsumers := modify_list (ConsumerInfo) 
                                    (oldOracleState.(allConsumers)) 
                                    (caller) 
                                    (newConsumerInfo) 
                                    (nil) 
    in
    let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                            (oldOracleState.(timeStamp)) 
                                            (oldOracleState.(totalCost)) 
                                            (oldOracleState.(totalRevenue)) 
                                            (oldOracleState.(writes)) 
                                            (oldOracleState.(reads)) 
                                            (oldOracleState.(baseFee)) 
                                            (oldOracleState.(maxFee)) 
                                            (oldOracleState.(maxFeeNext)) 
                                            (oldOracleState.(maxFeeTimeLock)) 
                                            (oldOracleState.(latestCost)) 
                                            (oldOracleState.(latestWrite)) 
                                            (oldOracleState.(totalCredit) - amount) 
                                            (newConsumers) 
    in
    let cw := CreditWithdrawn (amount) (caller) in
    let newState := Build_State (newOracleState) 
                                (oldOracleParams)
                                (oldTrace ++ (cw :: nil)) 
    in
    newState.

Definition withdraw (receiver : address) (amount : nat) (caller : address) (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) 
    in
    if (compare_address (oldOracleParams.(owner)) (caller))
    then
        if ((oldOracleState.(totalRevenue) - oldOracleState.(totalCredit)) <? amount)
        then
            state
        else
            let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                                    (oldOracleState.(timeStamp)) 
                                                    (oldOracleState.(totalCost)) 
                                                    (oldOracleState.(totalRevenue) - amount) 
                                                    (oldOracleState.(writes)) 
                                                    (oldOracleState.(reads)) 
                                                    (oldOracleState.(baseFee)) 
                                                    (oldOracleState.(maxFee)) 
                                                    (oldOracleState.(maxFeeNext)) 
                                                    (oldOracleState.(maxFeeTimeLock)) 
                                                    (oldOracleState.(latestCost)) 
                                                    (oldOracleState.(latestWrite)) 
                                                    (oldOracleState.(totalCredit)) 
                                                    (oldOracleState.(allConsumers)) 
            in
            let rw := RevenueWithdrawn (receiver) (amount) (caller) in
            let newState := Build_State (newOracleState) 
                                        (oldOracleParams)
                                        (oldTrace ++ (rw :: nil)) 
            in
            newState
    else
        state.

Definition reset_cost_and_revenue (state : State) : State :=
    let oldOracleState := state.(oracleState) in
    let oldOracleParams := state.(oracleParameters) in 
    let oldTrace := state.(trace) in
    let (newTotalCost, newTotalRevenue) := 
        if (oldOracleState.(totalRevenue) <? oldOracleState.(totalCost))
        then
            ((oldOracleState.(totalCost) - oldOracleState.(totalRevenue)), 0)
        else
            (0, (oldOracleState.(totalRevenue) - oldOracleState.(totalCost))) 
    in
    let newOracleState := Build_OracleState (oldOracleState.(data)) 
                                            (newTotalCost) 
                                            (oldOracleState.(timeStamp)) 
                                            (newTotalRevenue) 
                                            (oldOracleState.(writes)) 
                                            (oldOracleState.(reads)) 
                                            (oldOracleState.(baseFee)) 
                                            (oldOracleState.(maxFee)) 
                                            (oldOracleState.(maxFeeNext)) 
                                            (oldOracleState.(maxFeeTimeLock)) 
                                            (oldOracleState.(latestCost)) 
                                            (oldOracleState.(latestWrite)) 
                                            (oldOracleState.(totalCredit)) 
                                            (oldOracleState.(allConsumers)) 
    in
    let reset := Reset (oldOracleState.(totalCost)) (oldOracleState.(totalRevenue)) in
    let newState := Build_State (newOracleState) 
                                (oldOracleParams)
                                (oldTrace ++ (reset :: nil)) 
    in
      newState.

Definition execute (state : State) (event : Event) : State :=
    match event with
    | DataWritten (newData) (newCost) (caller) => write_data (state) (newData) (newCost) (caller)
    | DataRead (consumer) (_) (_) => 
        let (newState, _) := read_data (state) (consumer)
        in newState
    | WeightAdjustmentScheduled (consumer) (caller) (weightNext) (timeStamp) (_) => 
        schedule_weight_adjustment (consumer) (caller) (weightNext) (timeStamp) (state)
    | WeightAdjusted (consumer) (caller) (timeStamp) (_) => 
        adjust_weight (consumer) (caller) (timeStamp) (state)
    | MaxFeeAdjustmentScheduled (maxFeeNextNew) (caller) (timeStamp) (_) => 
        schedule_max_fee_adjustment (maxFeeNextNew) (caller) (timeStamp) (state)
    | MaxFeeAdjusted (caller) (timeStamp) (_) => adjust_max_fee (caller) (timeStamp) (state)
    | BaseFeeAdjusted (caller) (_) (_) (_) => adjust_base_fee (caller) (state)
    | CreditDeposited (consumer) (deposit) => deposit_credit (consumer) (state) (deposit)
    | CreditWithdrawn (amount) (caller) => withdraw_credit (amount) (caller) (state)
    | RevenueWithdrawn (receiver) (amount) (caller) => withdraw (receiver) (amount) (caller) (state)
    | Reset (_) (_) => reset_cost_and_revenue (state)
    end.
