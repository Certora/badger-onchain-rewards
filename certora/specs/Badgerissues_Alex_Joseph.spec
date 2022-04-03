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
invariant CurrentEpochZeroThenEpochValuesPointsRewardsZero(address vault, address user, address token)
currentEpoch() == 0 => (
    getEpochsStartTimestamp(currentEpoch()) == 0 &&
    getEpochsEndTimestamp(currentEpoch()) == 0 &&
    getPoints(currentEpoch(), vault, user) == 0 &&
    getPointsWithdrawn(currentEpoch(), vault, user, token) == 0 &&
    getTotalPoints(currentEpoch(), vault) == 0 &&
    getRewards(currentEpoch(),vault, token) == 0
)



// In a vault in an epoch where there are rewards available for user to claim, the contract is supposed to pay rewards to all users who've 
// accumulated points in the vault in the epoch. However due to potential rounding errors during payout calculations, the contract doesn't
// pay some users with low number of points. Even wehn this rounding error leads to non-payment of rewards for a user, the contract proceeds
// to wrongly update the pointswithdrawn mapping to indicate that the user has withdrawn all the rewards.

// This rule checks if there is a way for a user to call claimRewards() function and not get any rewards despite having unwithdrawn points.
// The counter-example shows a case where the payout calculation yields 0 because of rounderdown errors but the pointsWithdrawn are still
// wrongly updated to indicate that the user has withdrawn their rewards.
// https://prover.certora.com/output/64072/4506d3721e81cc95a113/?anonymousKey=8eafee3051de84a35a4a292ffa89d5fab6165544

//FAILING 
rule UserGetRewardsIfTheyHaveUnwithdrawnPoints(uint256 epoch, address vault, address user, address token, method f){
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epoch, vault, user, token);
    uint256 pointsBefore = getPoints(epoch, vault, user);
    uint256 rewards = getRewards(epoch, vault, token);
    uint256 userTokenBalanceBefore = tokenBalanceOf(token, user);
    uint256 contractTokenBalanceBefore = tokenBalanceOf(token, currentContract);
    require pointsWithdrawnBefore < pointsBefore;
    require rewards > 0;
    require user != currentContract;
    env e;
    claimReward(e, epoch, vault, token, user);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epoch, vault, user, token);
    uint256 pointsAfter = getPoints(epoch, vault, user);
    uint256 userTokenBalanceAfter = tokenBalanceOf(token, user);
    uint256 contractTokenBalanceAfter = tokenBalanceOf(token, currentContract);
    assert (userTokenBalanceAfter > userTokenBalanceBefore, "User did not get rewards despite having points");
}