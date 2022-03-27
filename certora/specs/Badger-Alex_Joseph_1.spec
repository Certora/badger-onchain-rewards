//  *************************************************************************************************************************************
//  * IMPORTS/SETUP                                                                                                                     *
//  *************************************************************************************************************************************
import "itsLikeAReward.spec"


//  *************************************************************************************************************************************
//  * USEFUL CONSTRUCTS.                                                                                                                *
//  *************************************************************************************************************************************

definition PRECISION() returns uint256 = 1000000000000000000;

// Ghost for tracking the sum of pointWithdrawn for each epoch, vault and token across all users. This is updated using the pointsWithdrawn hook.
ghost PWSum_EpochVaultToken_Ghost(uint256, address, address) returns uint256{
    init_state axiom forall uint256 e. forall address v. forall address t. PWSum_EpochVaultToken_Ghost(e, v, t) == 0;
}

// Ghost for tracking the sum of points for each epoch and vault across all users. This is updated using the points hook.
ghost Sum_UserPoints_Ghost(uint256, address)returns uint256{
    init_state axiom forall uint256 e. forall address v. Sum_UserPoints_Ghost(e, v) == 0;
}

// Ghost keeping a track of the total rewards tokens that the RewardsManager contract owes, across all epochs, vaults and users, for any 
// given token. How many of a given token, the RewardsManager owes to all the users across all the vaults and epochs. Total rewards owed 
// decrease everytime some user claims rewards and total rewards owed increase everytime new rewards are added to the contract using the
// addReward(s) functions. Therefore, this ghost is updated using two hooks viz., pointsWithdrawn and rewards.
ghost pendingRewards_Token_Ghost(address) returns uint256{
    init_state axiom forall address t. pendingRewards_Token_Ghost(t) == 0;
}

// Ghost tracking the total rewards paid out for a given token by the contract to all users across all epoch and vaults. 
ghost RewardsPayout_EpochVaultToken_Ghost(uint256, address, address) returns uint256{
    init_state axiom forall uint256 e. forall address v. forall address t. RewardsPayout_EpochVaultToken_Ghost(e, v, t) == 0;
}

// Ghost keeping a track of the sum of all user shares in a given epoch and vault. This is updated using the shares hook.
ghost Sum_Shares_Ghost(uint256, address)returns uint256{
    init_state axiom forall uint256 e. forall address v. Sum_Shares_Ghost(e, v) == 0;
}

// Ghost for getting totalPoints for a given epoch and vault. Using this inside the pointsWithdrawn hook for calculating and updating the
// pendingRewards_Token_Ghost since getter function can't be used inside hooks. Updating this ghost using the totalPoints hook.
ghost total_points_vault_epoch_Ghost(uint256,address) returns uint256{
    init_state axiom forall uint256 e. forall address v. total_points_vault_epoch_Ghost(e, v) ==  0;
}

// Ghost for getting rewards in a given epoch and vault. Using this inside the pointsWithdrawn hook for calculating and updating the
// pendingRewards_Token_Ghost since getter function can't be used inside hooks. Updating this ghost using the rewards hook.
ghost Reward_Epoch_Vault_Token_Ghost(uint256, address, address) returns uint256{
    init_state axiom forall uint256 e. forall address v. forall address t. Reward_Epoch_Vault_Token_Ghost(e,v,t) == 0;
}



// pointsWithdrawn hook being used to trigger updates to PWSum_EpochVaultToken_Ghost and pendingRewards_Token_Ghost
hook Sstore pointsWithdrawn [KEY uint256 epoch][KEY address vault][KEY address user][KEY address token] uint256 points_withdrawn(uint256 old_points_withdrawn) STORAGE{
    havoc PWSum_EpochVaultToken_Ghost assuming 
    forall uint256 e. forall address v. forall address t. 
    (e == epoch && v == vault && t == token)? 
    PWSum_EpochVaultToken_Ghost@new(e, v, t) == PWSum_EpochVaultToken_Ghost@old(e, v, t) +  points_withdrawn - old_points_withdrawn:
    PWSum_EpochVaultToken_Ghost@new(e, v, t) == PWSum_EpochVaultToken_Ghost@old(e, v, t);
    
    // Calculatng the reward amount paid out to the user during the reward claim and subtracting the amount from the pendingRewards_Token_Ghost
    havoc pendingRewards_Token_Ghost assuming 
    forall uint256 e. forall address v. forall address t. 
    (e == epoch && v == vault && t == token)? 
    pendingRewards_Token_Ghost@new(t) == pendingRewards_Token_Ghost@old(t) - 
    ((((points_withdrawn - old_points_withdrawn)*PRECISION())*Reward_Epoch_Vault_Token_Ghost(e, v, t))/ total_points_vault_epoch_Ghost(e, v))/PRECISION():
    (pendingRewards_Token_Ghost@new(t) == pendingRewards_Token_Ghost@old(t));
    
    // Sum of all rewards paid out for a give token in a given epoch and vault. Once all users have claimed their rewards in a vault in an epoch,
    // the total payout should be exactly equal to the rewards of that vault and that epoch.
    havoc RewardsPayout_EpochVaultToken_Ghost assuming 
    forall uint256 e. forall address v. forall address t. 
    (e == epoch && v == vault && t == token)? 
    RewardsPayout_EpochVaultToken_Ghost@new(e, v, t) == RewardsPayout_EpochVaultToken_Ghost@old(e, v, t) + 
    ((((points_withdrawn - old_points_withdrawn)*PRECISION())*Reward_Epoch_Vault_Token_Ghost(e, v, t))/ total_points_vault_epoch_Ghost(e, v))/PRECISION()   :
    (RewardsPayout_EpochVaultToken_Ghost@new(e, v, t) == RewardsPayout_EpochVaultToken_Ghost@old(e, v, t));
    }

hook Sstore rewards [KEY uint256 epoch][KEY address vault][KEY address token] uint256 new_rewards(uint256 old_rewards) STORAGE{
    //updating  pendingRewards_Token_Ghost for the given token by to account for the new rewards that are added to the rewardsManager contract.
    havoc pendingRewards_Token_Ghost assuming 
    forall address t. 
    t==token? 
    (pendingRewards_Token_Ghost@new(t) == pendingRewards_Token_Ghost@old(t) - old_rewards + new_rewards):
    pendingRewards_Token_Ghost@new(t) == pendingRewards_Token_Ghost@old(t);
    
    // updating Reward_Epoch_Vault_Token_Ghost which is used for getting the rewards in a given epoch and vault. This ghost is needed for
    // getting rewards inside another hook since getter functions can't be called inside hooks.
    havoc Reward_Epoch_Vault_Token_Ghost assuming 
    forall uint256 e. forall address v. forall address t. 
    (e == epoch && v == vault && t == token)? 
    Reward_Epoch_Vault_Token_Ghost@new(e, v, t) == new_rewards:
    Reward_Epoch_Vault_Token_Ghost@new(e, v, t) == Reward_Epoch_Vault_Token_Ghost@old(e, v, t);
}

hook Sstore points [KEY uint256 epoch][KEY address vault][KEY address user] uint256 new_points(uint256 old_points) STORAGE{
    // updating the Sum_UserPoints_Ghost to keep track of the sum of points across all users in a given epoch and vault.
    havoc Sum_UserPoints_Ghost assuming 
    forall uint256 e. forall address v.
    (e == epoch && v == vault)?
    Sum_UserPoints_Ghost@new(e, v) == Sum_UserPoints_Ghost@old(e, v) - old_points + new_points:
    Sum_UserPoints_Ghost@new(e, v) == Sum_UserPoints_Ghost@old(e, v);
}

hook Sstore totalPoints [KEY uint256 epoch][KEY address vault] uint256 new_total_points STORAGE{
    // updating total_points_vault_epoch_Ghost which is used for getting the totalpoints in a given epoch and vault. This ghost is needed for
    // getting totalPoints inside another hook since getter functions can't be called inside hooks.
    havoc total_points_vault_epoch_Ghost assuming 
    forall uint256 e. forall address v. 
    (e == epoch && v == vault)? 
    total_points_vault_epoch_Ghost@new(e,v) == new_total_points : 
    total_points_vault_epoch_Ghost@new(e,v) == total_points_vault_epoch_Ghost@old(e,v);
}


hook Sstore shares[KEY uint256 epoch][KEY address vault][KEY address user] uint256 shares(uint256 old_shares) STORAGE{
    // updating the Sum_Shares_Ghost to keep track of the sum of shares across all users in a given epoch and vault.
    havoc Sum_Shares_Ghost assuming 
    forall uint256 e. forall address v. 
    (e == epoch && v == vault)? 
    Sum_Shares_Ghost@new(e, v) == Sum_Shares_Ghost@old(e, v) - old_shares + shares:
    Sum_Shares_Ghost@new(e, v) == Sum_Shares_Ghost@old(e, v);
}

//  *************************************************************************************************************************************
//  * INVARIANTS AND RULES                                                                                                              *
//  *************************************************************************************************************************************

// SOLVENCY CHECK: Rule to check that for a given token, the contract holds enough balance to payout all rewards 
// in a given vault and epoch. If this invariant doesn't hold, Rewards Manager will not be able to payout all 
// the rewards owed to the users in a given vault and epoch.
// FAILING
invariant enoughBalanceToPayRewardsForEpochVaultToken (uint256 epoch, address vault, address token)
tokenBalanceOf(token, currentContract) >= (getTotalPoints(epoch, vault) - PWSum_EpochVaultToken_Ghost(epoch, vault, token))*getRewards(epoch, vault, token)/getTotalPoints(epoch,vault)


// SOLVENCY CHECK: Rule to check that for a given token, the contract holds enough balance to payout all rewards 
// across all vaults and epochs. If this invariant doesn't hold, Rewards Manager will not be able to payout all 
// the rewards owed to the users.
// FAILING
invariant enoughBalanceToPayRewardsForToken (address token)
tokenBalanceOf(token, currentContract) >= pendingRewards_Token_Ghost(token)

// rule to verify preserve-state of enoughBalanceToPayRewardsForToken invariant
rule enoughBalanceToPayRewardsForTokenRule(env e, uint256 epoch, address vault, address user, address token, method f) filtered {f -> !f.isView }{
    uint256 tokenBalanceBefore = tokenBalanceOf(token, currentContract);
    uint256 pendingRewardsBefore = pendingRewards_Token_Ghost(token);
    uint256 sharesBefore = getShares(epoch, vault, user);
    uint256 userPointsBefore = getPoints(epoch, vault, user);
    uint256 PW_Before = PWSum_EpochVaultToken_Ghost(epoch, vault, token);
    uint256 PW_User_before = getPointsWithdrawn(epoch, vault, user, token);
    uint256 totalPointsBefore = getTotalPoints(epoch, vault);
    uint256 rewards = getRewards(epoch,vault, token);
    calldataarg args;
    require tokenBalanceBefore >= pendingRewardsBefore;
    // require totalPointsBefore > 0;
    claimReward(e, epoch, vault, token, user);
    uint256 TotalPointsAfter = getTotalPoints(epoch, vault);
    uint256 PW_User_After = getPointsWithdrawn(epoch, vault, user, token);
    uint256 tokenBalanceAfter = tokenBalanceOf(token, currentContract);
    uint256 pendingRewardsAfter = pendingRewards_Token_Ghost(token);
    uint256 sharesAfter = getShares(epoch, vault, user);
    uint256 userPointsAfter = getPoints(epoch, vault, user);
    uint256 PW_After = PWSum_EpochVaultToken_Ghost(epoch, vault, token);
    require TotalPointsAfter > 0;
    uint256 payout = (PW_User_After - PW_User_before)*rewards/TotalPointsAfter;
    assert (tokenBalanceAfter >= pendingRewardsAfter,"token balance less than pending rewards");
}


// Once all the users have claimed rewards for a token in a given epoch and vault, the total reward payout should be equal to the rewards of the 
// vault and epoch 
// FAILING
invariant TotalRewardPayoutEqualsRewardsForVaultEpoch (uint256 ep, address vlt, address token)
(forall address user. getPointsWithdrawn(ep, vlt, user, token) > 0) => 
getRewards(ep, vlt, token) == RewardsPayout_EpochVaultToken_Ghost(ep, vlt, token)
{
    preserved
    {
        require (ep < currentEpoch() && ep > 0);
    }
}
// FAILING
rule TotalRewardPayoutEqualsRewardsForVaultEpochRule(uint256 ep, address vlt, address token, env e, method f){
    uint256 rewardsBefore = getRewards(ep, vlt, token);
    uint256 rewardsPayoutBefore = RewardsPayout_EpochVaultToken_Ghost(ep, vlt, token);
    require (ep < currentEpoch() && ep > 0);
    uint256 currentEpoch = currentEpoch();
    address user;
    calldataarg args;
    f(e, args);
    require forall address users. (getPointsWithdrawn(ep, vlt, user, token) > 0);
    uint256 rewardsAfter = getRewards(ep, vlt, token);
    uint256 rewardsPayoutAfter = RewardsPayout_EpochVaultToken_Ghost(ep, vlt, token);
    assert (rewardsAfter == rewardsPayoutAfter,"Total rewards payout, after all users have claimed, is less than the rewards for the vault and epoch");
}

// FAILING
rule testingRewardsPayoutGhost(uint256 ep, address vlt, address user, address token, env e){
    uint256 rewardPayoutBefore = RewardsPayout_EpochVaultToken_Ghost(ep, vlt, token);
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(ep, vlt, user,token);
    uint256 contractTokenBalanceBefore = tokenBalanceOf(token, currentContract);
    uint256 userTokenBalanceBefore = tokenBalanceOf(token, user);
    uint256 PWSumBefore = PWSum_EpochVaultToken_Ghost(ep, vlt, token);
    require user!= currentContract;
    claimReward(e, ep, vlt, token, user);
    uint256 PWSumAfter = PWSum_EpochVaultToken_Ghost(ep, vlt, token);
    uint256 rewardPayoutAfter = RewardsPayout_EpochVaultToken_Ghost(ep, vlt, token);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(ep, vlt, user,token);
    uint256 contractTokenBalanceAfter = tokenBalanceOf(token, currentContract);
    uint256 userTokenBalanceAfter = tokenBalanceOf(token, user);
    require pointsWithdrawnAfter > pointsWithdrawnBefore;
    assert (rewardPayoutAfter != rewardPayoutBefore,"rewardspayout ghost unchanged");

}


    // invariant for checking that, once the users and the vault have been fully accrued, sum of all user points in a given epoch
//  and vault is less than or equal to the total points
// TAC ERROR
invariant SumOfUserPointsLETotalPointsinEpochVaultAfterFullAccrual (uint256 ep, address vlt)
getTotalPoints(ep, vlt) >= Sum_UserPoints_Ghost(ep, vlt)
{
    preserved
    {
        require forall address user. getLastUserAccrueTimestamp(ep, vlt, user) >= getEpochsEndTimestamp(ep);
        require getLastAccruedTimestamp(ep, vlt) >= getEpochsEndTimestamp(ep);
    }
}
// TAC ERROR
rule SumOfUserPointsLETotalPointsinEpochVaultAfterFullAccrualRule(method f, uint256 epoch, address vault, address token){
    // uint256 totalSupplyBefore = getTotalSupply(epoch, vault);
    // uint256 sumSharesBefore = Sum_Shares_Ghost(epoch, vault);
    env e;
    calldataarg args;
    f(e, args);
    require forall address u. getLastUserAccrueTimestamp(epoch, vault, u) >= getEpochsEndTimestamp(epoch);
    require getLastAccruedTimestamp(epoch, vault) >= getEpochsEndTimestamp(epoch);
    uint256 totalPointsAfter = getTotalPoints(epoch, vault);
    uint256 sumPointsAfter = Sum_UserPoints_Ghost(epoch, vault);
    assert (totalPointsAfter >= sumPointsAfter, "totalPoints is not equal to the sum of user points after complete accrual of all users in the vault in the epoch");
}


// The sum of all points withdrawn should be <= sum of all user points in any given epoch and vault
// If this condition is not met, it would mean that that system has either overpaid some user(s) or hasn't properly accrued some user
// therefore denying them of their fair share of the rewards 
// FAILING
invariant SumOfPointsWithdrawnLESumUserPoints (uint256 ep, address vault, address token)
PWSum_EpochVaultToken_Ghost(ep, vault, token) <= Sum_UserPoints_Ghost(ep, vault)
// FAILING
rule SumOfPointsWithdrawnLESumUserPointsRule (uint256 epoch, address vault, address user, address token, method f, env e) filtered {f -> !f.isView }{
    uint256 SumOfPointsWithdrawnEpochVaultTokenBefore = PWSum_EpochVaultToken_Ghost(epoch, vault, token);
    uint256 SumUserPointsEpochVaultBefore = Sum_UserPoints_Ghost(epoch, vault);
    uint256 pointsWithdrawnUserBefore = getPointsWithdrawn(epoch, vault, user, token);
    uint256 pointUserBefore = getPoints(epoch, vault, user);
    uint256 userSharesBefore = getShares (epoch, vault, user);
    uint256 UserTimeLeftToAccrueBefore = getUserTimeLeftToAccrue(e, epoch, vault, user);
    // uint256 UserBalanceAtEpochBefore, bool updateRequiredbefore = getBalanceAtEpoch(epoch, vault, user);
    calldataarg args;
    require forall address u. getPoints(epoch, vault, u) >= getPointsWithdrawn(epoch, vault, u, token);
    f(e, args);
    uint256 SumOfPointsWithdrawnEpochVaultTokenAfter = PWSum_EpochVaultToken_Ghost(epoch, vault, token);
    uint256 SumUserPointsEpochVaultAfter = Sum_UserPoints_Ghost(epoch, vault);
    uint256 pointsWithdrawnUserAfter = getPointsWithdrawn(epoch, vault, user, token);
    uint256 pointUserAfter = getPoints(epoch, vault, user);
    uint256 userSharesAfter = getShares(epoch, vault, user);
    uint256 UserTimeLeftToAccrueAfter = getUserTimeLeftToAccrue(e, epoch, vault, user);
    // uint256 UserBalanceAtEpochBefore, bool updateRequiredbefore = getBalanceAtEpoch(epoch, vault, user);
    assert (SumOfPointsWithdrawnEpochVaultTokenAfter <= SumUserPointsEpochVaultAfter,"Sum of Points Withdrawn exceeds sum of user points");
}

// Sum of pointsWithdrawn by all users in a vault in an epoch is less than or equal total points of the epoch.
// FAILING
invariant SumOfPointsWithdrawnLETotalPoints (uint256 ep, address vault, address token)
PWSum_EpochVaultToken_Ghost(ep, vault, token) <= getTotalPoints(ep, vault)
{
    preserved with (env e)
    {
        require e.block.timestamp > 0;
    }
}



// transfer the right amount of reward tokens to the user
// updates the pointswithdrawn correctly
// FAILING
rule ClaimRewardsWorksCorrectly(env e, uint256 epoch, address vault, address user, address token){
    env e1;
    accrueUser(e1, epoch, vault, user);
    env e2;
    accrueVault(e2, epoch, vault);
    uint256 Points = getPoints(epoch, vault, user);
    uint256 TotalPoints = getTotalPoints(epoch, vault);
    uint256 rewards =  getRewards(epoch, vault, token);
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epoch, vault, user, token);
    uint256 payoutRatio = (Points - pointsWithdrawnBefore)*PRECISION()/TotalPoints;
    uint256 payouttokens = payoutRatio*rewards/PRECISION();
    uint256 tokenBalanceUserBefore = tokenBalanceOf(token, user);
    require TotalPoints >= Points;
    require pointsWithdrawnBefore < Points;
    claimReward(e, epoch, vault, token, user);
    uint256 tokenBalanceUserAfter = tokenBalanceOf(token, user);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epoch, vault, user, token);
    assert(tokenBalanceUserAfter == tokenBalanceUserBefore + payouttokens,"Token transfer amount not correct");
    assert(pointsWithdrawnAfter == Points,"Points withdrawn not updated correctly");
}



// In a given epoch and vault, once all the users and the vault have been accrued for the entirety of the epoch, the total points should
// be more than the sum of user points.

// A discrepancy here would mean that some users will be paid more that what they’re owed therefore leaving the protocol insolvent 
// to pay other users, or the protocol will end up paying out the users less than they’re owned while keeping the remaining reward \
// token supply locked in the protocol

// invariant for checking that, once the users and the vault have been fully accrued, sum of all user shares in a given epoch
//  and vault is exactly equal to the total supply
// FAILING
invariant TotalPointsGEUserPoints(uint256 epoch, address vault, address user)
(getLastAccruedTimestamp(epoch, vault) >= getLastUserAccrueTimestamp(epoch, vault, user)) => 
(getTotalPoints(epoch, vault) >= getPoints(epoch, vault, user))
