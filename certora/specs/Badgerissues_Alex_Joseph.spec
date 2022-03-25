//  *************************************************************************************************************************************
//  * IMPORTS/SETUP                                                                                                                     *
//  *************************************************************************************************************************************
import "itsLikeAReward.spec"



//  *************************************************************************************************************************************
//  * INVARIANTS AND RULES                                                                                                              *
//  *************************************************************************************************************************************
// The contract should not allow users to send rewards to epoch 0 as it doesn't allow user to claim rewards from epoch 0. Any rewards
// sent to epoch 0 are forever locked in the contract.
// After the contract has been deployed but the startNextEpoch() function is yet to be called, the currentEpoch value is 0. At this point
// the contract allows a user to mistakenly add rewards for epoch 0. This rewards addition leads to reward tokens getting transferred from
// the user's account to the rewardsManager contract. These rewards tokens, once transfered to the contract as rewards for epoch 0, become
// irrecoverable as even the users with shares in the associated vaults can't claim these tokens as points accrued in epoch 0 will always be 0.
// The transferred rewards will remain trapped in the contract. This can be mitigated by adding a require(epochId >= currentEpoch && epochId > 0)
// at the beginning of the addRewards() function.



// FAILING
invariant CurrentEpochZeroAllValuesZero(address vault, address user, address token)
currentEpoch() == 0 => (
    getEpochsStartTimestamp(currentEpoch()) == 0 &&
    getEpochsEndTimestamp(currentEpoch()) == 0 &&
    getPoints(currentEpoch(), vault, user) == 0 &&
    getPointsWithdrawn(currentEpoch(), vault, user, token) == 0 &&
    getTotalPoints(currentEpoch(), vault) == 0 &&
    getRewards(currentEpoch(),vault, token) == 0
)

