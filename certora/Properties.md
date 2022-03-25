Properties

- Valid States
  - Epoch states
    - Epoch `i` not started yet => `i > currentEpoch && (startTimestamp, endTimestamp) = (0, 0)`
    - Epoch `i` started, cannot be ended => `i == currentEpoch && block.timestamp >= startTimestamp && block.timestamp < endTimestamp`
    - Epoch `i` started, can be ended => `i == currentEpoch && block.timestamp > startTimestamp && block.timestamp > endTimestamp`
    - Epoch `i` ended => `i < currentEpoch && block.timestamp > endTimestamp`
  - Vault states (per epoch)
    - Uninitialized : Supply in vault is 0, no users, last accrue time is 0 
    - NotAccrued : TotalPoints less than actual supply*time in epoch
    - Accrued : TotalPoints correct, supply correct
  - User States (per epoch, per vault)
    - NotAccrued
    - Accrued
    - Claimed (per token)

- State Transitions
  - Epoch states :
    - Not Started => Started, cannot be ended on `startNewEpoch()` for `currentEpoch`
    - Started, cannot be ended => Started, can be ended after `SECONDS_PER_EPOCH` time
    - 

  - Vault States
    - Non-accrued vaults && epoch < current_epoch => can accrue once, totalPoints = supply*Seconds per epoch
    - Accrued vaults && epoch < current_epoch => No future changes to state

- Variable Transitions
  - currentEpoch increases monotonically
  - 

- High Level Properties
  - 

- Unit tests
  - forall epoch < currentEpoch, startTimeStamp = endTimeStamp - SECONDS_PER_EPOCH
  - forall epochs i, i+1, endTimeStamp(i) < startTimestamp(i+1)
  
