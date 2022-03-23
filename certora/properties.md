# Rewards Manager Spec, Properties and Analysis

### System Overview

Rewards Manager is a complex system compared to systems seen during the workshops. It's complexity is due to the style the contract is written in. It also maintains and update states in a not-straightforward manner using multiple functions that sometimes interact with other contracts. The contract also has gas-friendly functions which are complex. 


The states of the system are defined by: 

1. `epoch` - 7 days. This measure is used to divide the rewards in discrete equal periods.  
2. `vault` - a vault external contract that handles vault accounting.
3. `user` - address of the user.
4. `token` - address of some reward token.
4. `shares` - the user balance in the vault.
5. `points` - points to track user rewards share.
6. `pointsWithdrawn` - measure the amount of points withdrawn by the user so far for epoch, vault, user, token.
7. `totalPoints` - sum of all points over users.
8. `rewards` - total rewards for the vault.
9. `lastAccruedTimestamp` - last time a vault was accrued for a specific epoch.
10. `lastUserAccrueTimestamp` - last time a vault was accrued for a specific epoch and user.
11. `totalSupply` - tracks the sum of all deposits for a vault at an epoch and used to measure the share of rewards of a user.
12. `lastVaultDeposit` - unused mapping.

The transition between states depends on the correct implementation of these functions: 
1. `startNextEpoch` - only function responsible of updating `epochs` struct and `currentEpoch`.
2. `addReward` and `addRewards`  - only functions responsible of updating `rewards` state.
3. `notifyTransfer` - update `shares` and `totalSupply` after a transaction is recorded in the vault.
4. `getTotalSupplyAtEpoch` - compute `totalSupply` for the corresponding epoch, vault.
5. `getBalanceAtEpoch` - compute `shares` for the corresponding epoch, vault, user.
6. `getVaultTimeLeftToAccrue` return the time left to accrue for the epoch, vault pair.
7. `getUserTimeLeftToAccrue` return the time left to accrue for the epoch, vault, user.
8. `accrueUser` complex function updates: `shares`, `lastUserAccrueTimestamp`, `points` for epoch, vault, user.
9. `accrueVault` complex function updates: `totalSupply`, `lastAccruedTimestamp`, `totalPoints` for epoch, vault.
10. `claimReward` and `claimRewards`-  allow user to claim rewards and updates `pointsWithdrawn` for epoch, vault, token, user.
11. `claimBulkTokensOverMultipleEpochs` - Bulk claim all rewards for one vault from epochStart to epochEnd, requires user has not withdrawn in any previous epoch between epochStart to epochEnd.
12. `claimBulkTokensOverMultipleEpochsOptimized` - Gas optimized version of the previous function that deletes some `shares` and `points` mappings.



The state variables updates:
1. `currentEpoch` - only updated by `startNextEpoch`, it is always incremented by 1.
2. `epochs` - only updated by `startNextEpoch`, always the new `endTime` = new `startTime` + 1 week and new `startTime` = block.timestamp.
3. `shares` - It's updated in : `notifyTransfer`, `accrueUser` and `claimBulkTokensOverMultipleEpochsOptimized`. The value is correlated with tokens of the user held in the particular vault, but that accounting part is left to the vault contract itself.
4. `points` - It's updated in : `accrueUser` and `claimBulkTokensOverMultipleEpochsOptimized`. `accrueUser` increase `points`, `claimBulkTokensOverMultipleEpochsOptimized` make it zero. It's value is correlated to `share`
5. `pointsWithdrawn` - It's updated in : `claimReward***` functions. It is non decreasing, and can only surpass `points` if `claimBulkTokensOverMultipleEpochsOptimized` was called
6. `totalPoints` - It's updated in : `accrueUser` and `claimBulkTokensOverMultipleEpochsOptimized`. `accrueUser` increase `points`, `claimBulkTokensOverMultipleEpochsOptimized` make it zero. It's value is correlated to `share` and should always be greater than sum of `points`.
7.  `rewards` -  It's updated in `addReward*` functions. is non decreasing.
8. `lastAccruedTimestamp` - updated in `accrueVault`.
9. `lastUserAccrueTimestamp` - updated in `accrueUser`.
10. `totalSupply` - updated in `notifyTransfer` and `accrueVault` functions.





## Epoch properties
1. ***High-level property*** - Future Epochs non initialized : currentEpoch < epoch > 0 => epochs[epoch].startTimestamp  = epochs[epoch].endTimestamp = 0
2. ***State transition*** - Next epoch can only start after epochs[currentEpoch].endTimestamp
3. ***High-level property*** - currentEpoch >= epoch > 0 => epochs[epoch].startTimestamp + 604800 = epochs[epoch].endTimestamp
4. ***High-level property*** - currentEpoch >= epoch > 0  => epochs[epoch].startTimestamp <= block.timestamp

Note: Rules for properties 1-4 verified in the spec


## Shares and TotalSupply properties
5. ***High-level property*** - shares[epochId][vault][user] <= totalSupply[epochId][vault]
6. ***High-level property*** - Sum of ( shares[epochId][vault][user], user) <= totalSupply[epochId][vault]
7. ***High-level property*** - future `totalSupply` and `shares` are non initialized : epoch > currentEpoch => totalSupply[epochId][vault] = shares[epochId][vault][user] = 0




## Points and PointsWithdrawn and TotalPoints properties
8. ***High-level property*** - Sum of ( points[epochId][vault][user], user) <= totalPoints[epochId][vault]
9. ***High-level property*** - `pointsWithdrawn` are non decreasing after a function call other than `claimBulkTokensOverMultipleEpochsOptimized`
10. ***High-level property*** - future `totalPoints` and `points` are non initialized : epoch > currentEpoch => totalPoints[epochId][vault] = points[epochId][vault][user] = 0
11. ***High-level property*** - pointsWithdrawn[epochId][vault][user][token] <= points[epochId][vault][user] unless `claimBulkTokensOverMultipleEpochsOptimized` was walled.
12. ***Variable transition***  - `pointsWithdrawn` are non decreasing.



## Accrued Timestamp properties
13. ***Variable transition***  - `lastAccruedTimestamp`  is non decreasing.
14. ***Variable transition***  - `lastUserAccruedTimestamp`  is non decreasing.
15. ***Variable transition***  - `lastAccruedTimestamp` = block.timestamp after `accrueVault` is called.
16. ***Variable transition***  - `lastUserAccruedTimestamp` = block.timestamp after `accrueUser` is called.
17. ***High-level property*** - future `lastAccruedTimestamp` and `lastUserAccruedTimestamp` are non initialized : epoch > currentEpoch => lastAccruedTimestamp[epochId][vault] = lastUserAccruedTimestamp[epochId][vault][user] = 0

## rewards properties
18. ***Variable transition***  - `rewards`  is non decreasing.
19. ***High-level property*** - `rewards`  only updated via `addReward` or `addRewards`.

## unit tests

### startNextEpoch unit test
20. `startNextEpoch` - Increment current by 1.
21. `startNextEpoch` - correctly set startTime and endTime of new epoch.
22. `startNextEpoch` - can only be called after endTime of currentEpoch.



### addReward and addRewards unit test
23. `addReward` - correctly update `rewards` mapping and user token balance.
24. `addRewards` - correctly update `rewards` mapping and user token balance.


### notifyTransfer unit test
25. `notifyTransfer` - correctly update `shares`  and `totalSupply` mappings.

### getTotalSupplyAtEpoch and getBalanceAtEpoch unit test
26. `getTotalSupplyAtEpoch` - returns the correct supply at Epoch.
27. `getBalanceAtEpoch` - returns the correct balance at Epoch.

### getVaultTimeLeftToAccrue and getUserTimeLeftToAccrue unit test
28. `getVaultTimeLeftToAccrue` - returns the correct time Left to Accrue at Epoch.
29. `getVaultTimeLeftToAccrue` - return should always be less than 68400 seconds.
30. `getUserTimeLeftToAccrue` - returns the correct time Left to Accrue at Epoch.
31. `getUserTimeLeftToAccrue` - return should always be less than 68400 seconds.


### accrueUser unit test
32. `accrueUser` - can only be called for present or past epochs.
33. `accrueUser` - correctly updates `points`, `shares` and `lastUserAccruedTimestamp`.

### accrueVault unit test
34. `accrueVault` - can only be called for present or past epochs.
35. `accrueVault` - correctly updates `totalPoints`, `totalSupply` and `lastAccruedTimestamp`.


### claimReward and claimRewards unit test
36. `claimReward` and `claimRewards` can only be called for past epochs.
37. `claimReward` correctly update `pointsWithdrawn` and user balances.
38. `claimRewards` should be equivalent to calling `claimReward` multiple times.


### claimBulkTokensOverMultipleEpochs unit test
39. `claimBulkTokensOverMultipleEpochs` can only be called for past epochs.
40. `claimBulkTokensOverMultipleEpochs` correctly update `pointsWithdrawn` and user balances.

### claimBulkTokensOverMultipleEpochsOptimized unit test
41. `claimBulkTokensOverMultipleEpochs` can only be called for past epochs.
42. `claimBulkTokensOverMultipleEpochs` correctly update `pointsWithdrawn`, `points`, `shares` and user balances.




