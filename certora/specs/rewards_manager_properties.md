# Rewards Manager Properties

### System Overview

Rewards Manager is a complicated rewards system. It is complicated mainly because 
1. it maintains a set of complicated states, and 
2. it interacts with external contracts.

The main concepts of the system:
1. epoch - a time span of 7 days (604800 seconds)
2. vault - a vault is defined by an asset which can be any ERC20 token
3. shares - user's stake in a specific vault
4. points - a score system measuring user's loyalty to a specific vault
5. rewards - user's rewards for their loyalty to a specific vault

The state variables and how they are updated:
1. `currentEpoch` - the id of the current epoch. The default value 0 means no epoch in the system. The first epoch id is 1, and increment by 1 for any new epoch. It's updated in the `startNextEpoch` function
2. `epochs` - a mapping from epoch id to `Epoch` struct that has a `startTimestamp` and `endTimestamp`. New epochs are created and inserted into the mapping in the `startNextEpoch` function. `Epoch` timestamps have no overlap and increase over time, but Epochs' timestamps may have gaps, i.e., the next Epoch's `startTimestamp` may be sometime after the current Epoch's `endTimestamp`.
3. `shares` - a 3-level mapping, `shares[epochId][vaultAddress][userAddress]`, which means that it's per epoch and vault. It's updated in a few functions: `notifyTransfer`, `accrueUser` and `claimBulkTokensOverMultipleEpochsOptimized`. The value should always reflect the tokens owned by a user at a given epoch.
4. `totalSupply` - a 2-level mapping, `totalSupply[epochId][vaultAddress]`. It should be the sum of the shares for the given epoch and vault. It's updated in `notifyTransfer` and `accrueVault` functions.
5. `points` - a 3-level mapping similar to `shares`, `points[epochId][vaultAddress][userAddress]`. It's updated in 2 functions: `accrueUser` and `claimBulkTokensOverMultipleEpochsOptimized`. 
6. `totalPoints` - a 2-level mapping similar to `totalSupply`, `totalPoints[epochId][vaultAddress]`. It is updated in the `accrueVault` function.
7. `pointsWithdrawn` - a 4-level mapping, `pointsWithdrawn[epochId][vaultAddress][userAddress][rewardToken]`. It's updated in 2 functions: `claimReward` and `claimBulkTokensOverMultipleEpochs`.
8. `rewards` - a 3-level mapping, `rewards[epochId][vaultAddress][tokenAddress]`. It's updated in `addReward` function.
9. `lastAccruedTimestamp` - a 2-level mapping, `lastAccruedTimestamp[epochId][vaultAddress]`. It's updated in `accrueVault` function.
10. `lastUserAccrueTimestamp` - a 3-level mapping, `lastUserAccrueTimestamp[epochId][vaultAddress][userAddress]`. It's updated in `accrueUser` function.
11. `lastVaultDeposit` - a mapping from vault to amount. It's actually never updated or read, hence it is redundant and can be removed.

External and public functions:
1. `startNextEpoch` - increment the `currentEpoch`, insert a new `Epoch` struct against the new `currentEpoch` id
2. `notifyTransfer` - update `shares` and `totalSupply` for the current epoch and the given vault.
3. `addReward` - update `rewards` for a given epoch, vault and token based on the actual amount transferred to the contract
4. `addRewards` - batch operation of `addReward`
5. `getVaultTimeLeftToAccrue` - calculate time left (in seconds) to accrue points for a vault at a given epoch.
6. `getTotalSupplyAtEpoch` - get the `totalSupply` for a given epoch and vault.
7. `accrueVault` - update `totalPoints` for a given epoch and vault based on the time left to accrue and `totalSupply`. It also updates the `lastAccruedTimestamp`
8. `claimReward` - calculate the user rewards based on the user points, total points, pointsWithdrawn, and rewards, and transfer the rewards to the user. 
9. `claimRewards` - batch operation of `claimReward`
10. `getBalanceAtEpoch` - get user points at a given epoch for a given vault
11. `getUserTimeLeftToAccrue` - get user's time left to accrue for a given epoch and vault
12. `accrueUser` - update `shares`, user `points` and `lastUserAccrueTimestamp`
13. `claimBulkTokensOverMultipleEpochs` - bulk claim rewards for multiple epochs and tokens
14. `claimBulkTokensOverMultipleEpochsOptimized` - bulk claim rewards and reset user data

## Property List
1. ***High-level property*** - (epochId_1 < epochId_2 && epochId <= currentEpoch) <=> epochs[epochId_1].endTimestamp < epochs[epochId_2].startTimestamp
2. ***High-level property*** - currentEpoch > 0 => epochs[currentEpoch].startTimestamp + 604800 = epochs[currentEpoch].endTimestamp
3. ***High-level property*** - currentEpoch > 0 => epochs[currentEpoch].startTimestamp <= block.timestamp
4. ***High-level property*** - totalPoints[epochId][vault] = sum(points[epochId][vault][user])
5. ***High-level property*** - totalSupply[epochId][vault] = sum(shares[epochId][vault][user])
6. ***High-level property*** - pointsWithdrawn[epochId][vault][user][token] <= points[epochId][vault][user]


