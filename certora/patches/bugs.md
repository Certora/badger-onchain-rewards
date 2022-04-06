# Bugs in patches (`bug{i}.patch` is the i-th bug in this list):

1. Allow accrue for the future epochs, this will break accounting

2. Do not delete shares in `claimBulkTokensOverMultipleEpochsOptimized` this allows to claim rewards multiple times

3. Remove accrual for the `_handleDeposit` function as that will break internal accounting 

4. Removed [this set of logic](https://github.com/GalloDaSballo/badger-onchain-rewards/blob/c5b5c532cdd941cc395d1c8f71731856b2ac863d/contracts RewardsManager.sol#L545-L547) to allow time in between epochs to be part of accrual math

5. Switched sender and recipient in transferFrom() within addReward.

6. Break the duplicates check, allowing to do multiple claims on same token for `claimBulkTokensOverMultipleEpochsOptimized`

7. Allow starting a next epoch when a new epoch hasn’t ended

8. Allow claiming reward on current epoch, will make users not being able to get all the rewards if more rewards added during the current epoch

9. Allow claim rewards for future epochs

10. Allow calling `claimBulkTokensOverMultipleEpochs` and `claimBulkTokensOverMultipleEpochsOptimized` when `pointsWithdrawn != 0`, will make the user being able to claim rewards twice

11. Transfer tokens before removing data in `claimBulkTokensOverMultipleEpochsOptimized`, will make the function open to a reentrency attack

12. Allow adding rewards to past epochs, will make the part of these rewards that belongs to users who already used all their points get locked.

13. Switched the `to` and `from` arguments that are passed to the `_handleTransfer` function

14. Changed the accrue functions to override the previous points balance, will make the internal accounting go wrong (the number of points won't be correct, and a situation where a user has more points than the totalPoints can happen so attackers can take adventage of this)

15. Changed the claimReward function to override the previous value of `pointsWithdrawn` instead of adding to it, will make users being able to get more rewards than they should

16. used `totalSupply[epochId][vault]` and `shares[epochId][vault][user]` in the accrue function instead the `getTotalSupplyAtEpoch` and `getBalanceAtEpoch` functions, this will make the internal accounting go wrong because the values from the previous epoch won't be saved to next 
epochs

17. Removed [this logic](https://github.com/GalloDaSballo/badger-onchain-rewards/blob/921ffa1edb425684d338b9f52f851b3cf41c9cba/contracts RewardsManager.sol#L551-L553), will make users recieve more points than they should

18. Switched the `token` and `vault` arguments in the call to `claimReward` in the `claimRewards` function