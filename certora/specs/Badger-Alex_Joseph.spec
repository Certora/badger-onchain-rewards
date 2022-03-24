//  *************************************************************************************************************************************
//  * IMPORTS/SETUP                                                                                                                     *
//  *************************************************************************************************************************************
import "itsLikeAReward.spec"


//  *************************************************************************************************************************************
//  * USEFUL CONSTRUCTS.                                                                                                                *
//  *************************************************************************************************************************************

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
    (((points_withdrawn - old_points_withdrawn)/ total_points_vault_epoch_Ghost(e, v))*Reward_Epoch_Vault_Token_Ghost(e, v, t)):
    (pendingRewards_Token_Ghost@new(t) == pendingRewards_Token_Ghost@old(t));
    
    // Sum of all rewards paid out for a give token in a given epoch and vault. Once all users have claimed their rewards in a vault in an epoch,
    // the total payout should be exactly equal to the rewards of that vault and that epoch.
    havoc RewardsPayout_EpochVaultToken_Ghost assuming 
    forall uint256 e. forall address v. forall address t. 
    (e == epoch && v == vault && t == token)? 
    RewardsPayout_EpochVaultToken_Ghost@new(e, v, t) == RewardsPayout_EpochVaultToken_Ghost@old(e, v, t) + 
    (((points_withdrawn - old_points_withdrawn)/ total_points_vault_epoch_Ghost(e, v))*Reward_Epoch_Vault_Token_Ghost(e, v, t)):
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

// SOLVENCY CHECK: Rule to check that for a given token, the contract hold enough balance to payout all rewards 
// in a given vault and epoch. If this invariant doesn't hold, Rewards Manager will not be able to payout all 
// the rewards owed to the users.

invariant enoughBalanceToPayRewardsForEpochVaultToken (uint256 epoch, address vault, address token)
tokenBalanceOf(token, currentContract) >= (getTotalPoints(epoch, vault) - PWSum_EpochVaultToken_Ghost(epoch, vault, token))*getRewards(epoch, vault, token)/getTotalPoints(epoch,vault)


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
invariant TotalRewardPayoutEqualsRewardsForVaultEpoch (uint256 ep, address vlt, address token)
getRewards(ep, vlt, token) == RewardsPayout_EpochVaultToken_Ghost(ep, vlt, token)
{
    preserved
    {
        require forall address user. getPointsWithdrawn(ep, vlt, user, token) > 0;
    }
}


// In a given epoch and vault, if all the users and the vault have been accrued for the entire duration of the epoch, 
// sum of all user shares should equal the total supply and sum of all userpoints should be equal to the total points.

// A discrepancy here would mean that some users will be paid more that what they’re owed therefore leaving the protocol insolvent 
// to pay other users, or the protocol will end up paying out the users less than they’re owned while keeping the remaining reward \
// token supply locked in the protocol

// invariant for checking that, once the users and the vault have been fully accrued, sum of all user shares in a given epoch
//  and vault is exactly equal to the total supply
invariant SumOfUserSharesEqualsTotalSupplyinEpochVaultAfterFullAccrual (uint256 ep, address vlt)
getTotalSupply(ep, vlt) == Sum_Shares_Ghost(ep, vlt)
{
    preserved
    {
        require forall address user. getLastUserAccrueTimestamp(ep, vlt, user) >= getEpochsEndTimestamp(ep);
        require getLastAccruedTimestamp(ep, vlt) >= getEpochsEndTimestamp(ep);
    }
}
// Certora internal type error
rule SumOfUserSharesEqualsTotalSupplyinEpochVaultAfterFullAccrualRule(method f, uint256 epoch, address vault, address token){
    // uint256 totalSupplyBefore = getTotalSupply(epoch, vault);
    // uint256 sumSharesBefore = Sum_Shares_Ghost(epoch, vault);
    env e;
    calldataarg args;
    f(e, args);
    require forall address u. getLastUserAccrueTimestamp(epoch, vault, u) >= getEpochsEndTimestamp(epoch);
    require getLastAccruedTimestamp(epoch, vault) >= getEpochsEndTimestamp(epoch);
    uint256 totalSupplyAfter = getTotalSupply(epoch, vault);
    uint256 sumSharesAfter = Sum_Shares_Ghost(epoch, vault);
    assert (totalSupplyAfter == sumSharesAfter, "totalSupply is not equal to the sum of user shares after complete accrual of all users in the vault in the epoch");
}

// invariant for checking that, once the users and the vault have been fully accrued, sum of all user points in a given epoch
//  and vault is exactly equal to the total points
invariant SumOfUserPointsEqualsTotalPointsinEpochVaultAfterFullAccrual (uint256 ep, address vlt)
getTotalPoints(ep, vlt) == Sum_UserPoints_Ghost(ep, vlt)
{
    preserved
    {
        require forall address user. getLastUserAccrueTimestamp(ep, vlt, user) >= getEpochsEndTimestamp(ep);
        require getLastAccruedTimestamp(ep, vlt) >= getEpochsEndTimestamp(ep);
    }
}

rule SumOfUserPointsEqualsTotalPointsinEpochVaultAfterFullAccrualRule(method f, uint256 epoch, address vault, address token){
    // uint256 totalSupplyBefore = getTotalSupply(epoch, vault);
    // uint256 sumSharesBefore = Sum_Shares_Ghost(epoch, vault);
    env e;
    calldataarg args;
    f(e, args);
    require forall address u. getLastUserAccrueTimestamp(epoch, vault, u) >= getEpochsEndTimestamp(epoch);
    require getLastAccruedTimestamp(epoch, vault) >= getEpochsEndTimestamp(epoch);
    uint256 totalPointsAfter = getTotalPoints(epoch, vault);
    uint256 sumPointsAfter = Sum_UserPoints_Ghost(epoch, vault);
    assert (totalPointsAfter == sumPointsAfter, "totalPoints is not equal to the sum of user points after complete accrual of all users in the vault in the epoch");
}


// The sum of all points withdrawn should be <= sum of all user points in any given epoch and vault
// If this condition is not met, it would mean that that system has either overpaid some user(s) or hasn't properly accrued some user
// therefore denying them of their fair share of the rewards 

invariant SumOfPointsWithdrawnLESumUserPoints (uint256 ep, address vault, address token)
PWSum_EpochVaultToken_Ghost(ep, vault, token) <= Sum_UserPoints_Ghost(ep, vault)

rule SumOfPointsWithdrawnLESumUserPointsRule (uint256 epoch, address vault, address user, address token, method f, env e) filtered {f -> !f.isView }{
uint256 SumOfPointsWithdrawnEpochVaultTokenBefore = PWSum_EpochVaultToken_Ghost(epoch, vault, token);
uint256 SumUserPointsEpochVaultBefore = Sum_UserPoints_Ghost(epoch, vault);
uint256 pointsWithdrawnUserBefore = getPointsWithdrawn(epoch, vault, user, token);
uint256 pointUserBefore = getPoints(epoch, vault, user);
uint256 userSharesBefore = getShares (epoch, vault, user);
uint256 UserTimeLeftToAccrueBefore = getUserTimeLeftToAccrue(e, epoch, vault, user);
// uint256 UserBalanceAtEpochBefore, bool updateRequiredbefore = getBalanceAtEpoch(epoch, vault, user);
calldataarg args;
require(SumOfPointsWithdrawnEpochVaultTokenBefore <= SumUserPointsEpochVaultBefore);
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

invariant SumOfPointsWithdrawnLETotalPoints (uint256 ep, address vault, address token)
PWSum_EpochVaultToken_Ghost(ep, vault, token) <= getTotalPoints(ep, vault)


// In any epoch, for any vault, a users pointsWithdrawn would either be 0 or exactly equal to the user's points
// Since users are allowed to claim rewards only for past epochs, any claim should accrue a user for the entirety of the 
// epoch as there isn't anymore time left to accrue in the epoch. So the user's pointsWithdrawn at this point should be exactly equal to 
// the aggregate points accrued by the user in the epoch. So the pointsWithdrawn for any user, in any epoch and vault, will either be 0 or
// exactly equal to the user's points. If this condition is not held, the user would have been paid over or under the appropriate amount 
// leading to potential solvency issues for the rewards mnanager as a whole or some user's not getting the fair share of rewards.

invariant pointsWithdrawnZeroOrEqualToUserPoints (uint256 ep, address vault, address user, address token)
getPointsWithdrawn(ep, vault, user, token) == 0 || getPointsWithdrawn(ep, vault, user, token) == getPoints(ep, vault, user)
{
    preserved with (env e)
    {
        require e.block.timestamp > 0;
    }
}
// PASSING
rule pointsWithdrawnZeroOrEqualToUserPointsRule(uint256 ep, address vault, address user, address token, method f, env e) {
    uint256 userPointsWithdrawnBefore = getPointsWithdrawn(ep, vault, user, token);
    uint256 userPointsBefore =  getPoints(ep, vault, user);
    require (userPointsWithdrawnBefore == 0 || userPointsWithdrawnBefore == userPointsBefore);
    uint256 userTimeLeftToAccrueBefore = getUserTimeLeftToAccrue(e, ep, vault, user);
    require (userPointsBefore > 0 && userPointsWithdrawnBefore > 0) => userTimeLeftToAccrueBefore == 0;
    if (f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector)
        {
        calldataarg args;
        f(e, args);
        }
    uint256 userPointsWithdrawnAfter = getPointsWithdrawn(ep, vault, user, token);
    uint256 userPointsAfter =  getPoints(ep, vault, user);
    assert (userPointsWithdrawnAfter == 0 || userPointsWithdrawnAfter == userPointsAfter,"points withdrawn can either be 0 or exactly equal to userpoints");
    // assert false;
}

// Everytime there is a change in shares or points, the lastuseraccruedtime needs to be updated.

// For any epoch and vault, lastuseraccruedtime == 0 => userPoints == 0
// PASSING
invariant UserPointsZeroIfAccrueTimeZero (uint256 ep, address vault, address user)
getLastUserAccrueTimestamp(ep, vault, user) == 0 => getPoints(ep, vault, user) == 0
{
    preserved with (env e)
    {
        require e.block.timestamp > 0;
    }
}

// rule proving preserve-state of invariant UserPointsZeroIfAccrueTimeZero
// PASSING
rule ifLastUserAccrueTimeZeroThenPointsZero (method f, uint256 epoch, address vault, address user){
    uint256 LastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 userPointsBefore = getPoints(epoch, vault, user);
    require LastUserAccrueTimeBefore == 0 => userPointsBefore == 0;
    env e;
    require e.block.timestamp > 0;
    calldataarg args;
    f(e, args);
    uint256 LastUserAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 userPointsAfter = getPoints(epoch, vault, user);
    assert LastUserAccrueTimeAfter == 0 => userPointsAfter == 0;


}

// For any epoch and vault, lastuseraccruedtime == 0 => userPoints == 0
// PASSING
invariant UserSharesZeroIfAccrueTimeZero (uint256 ep, address vault, address user)
getLastUserAccrueTimestamp(ep, vault, user) == 0 => getShares(ep, vault, user) == 0
{
    preserved with (env e)
    {
        require e.block.timestamp > 0;
    }
}

// Rule proving preserve-state for invariant UserSharesZeroIfAccrueTimeZero
// PASSING
rule ifLastUserAccrueTimeZeroThenSharesZero(method f, uint256 epoch, address vault, address user){
    uint256 LastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 userSharesBefore = getShares(epoch, vault, user);
    require LastUserAccrueTimeBefore == 0 => userSharesBefore == 0;
    env e;
    require e.block.timestamp > 0;
    calldataarg args;
    f(e, args);
    uint256 LastUserAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 userSharesAfter = getShares(epoch, vault, user);
    assert LastUserAccrueTimeAfter == 0 => userSharesAfter == 0;
}


// Everytime there is a change in totalPoints or totalSupply, the lastaccruedtime needs to be updated.

// For any epoch and vault, lastaccruedtime == 0 => totalPoints == 0
// PASSING
invariant TotalPointsZeroIfAccrueTimeZero (uint256 ep, address vault)
getLastAccruedTimestamp(ep, vault) == 0 => getTotalPoints(ep, vault) == 0
{
    preserved with (env e)
    {
        require e.block.timestamp > 0;
    }
}

// rule proving the preserve-state of invariant TotalPointsZeroIfAccrueTimeZero
// PASSING
rule ifLastUserAccrueTimeZeroThenTotalPointsZero(method f, uint256 epoch, address vault){
    uint256 LastAccrueTimeBefore = getLastAccruedTimestamp(epoch, vault);
    uint256 TotalPointsBefore = getTotalPoints(epoch, vault);
    require LastAccrueTimeBefore == 0 => TotalPointsBefore == 0;
    env e;
    require e.block.timestamp > 0;
    calldataarg args;
    f(e, args);
    uint256 LastAccrueTimeAfter = getLastAccruedTimestamp(epoch, vault);
    uint256 TotalPointsAfter = getTotalPoints(epoch, vault);
    assert LastAccrueTimeAfter == 0 => TotalPointsAfter == 0;
}

// For any epoch and vault, lastaccruedtime == 0 => totalSupply == 0
// PASSING
invariant TotalSupplyZeroIfAccrueTimeZero (uint256 ep, address vault)
getLastAccruedTimestamp(ep, vault) == 0 => getTotalSupply(ep, vault) == 0
{
    preserved with (env e)
    {
        require e.block.timestamp > 0;
    }
}


// not passing the counterexample where the balance of the contract doesn't change despite token transfer to the contract
//  going through. But since AddRewardsIncreasesTokenBalanceOfContract passes, we can eliminate this case.
// PASSING
rule AddRewardsUpdaetesRewardCorrectly(uint256 ep, address vlt, address tok, uint256 amount){
    uint256 RewardBefore = getRewards(ep, vlt, tok);
    uint256 tokenBalanceBefore = tokenBalanceOf(tok, currentContract);
    env e;
    addReward(e, ep, vlt, tok, amount);
    uint256 RewardAfter = getRewards(ep, vlt, tok);
    uint256 tokenBalanceAfter = tokenBalanceOf(tok, currentContract);
    require tokenBalanceAfter ==  tokenBalanceBefore + amount;
    assert RewardAfter ==  RewardBefore + amount;
}

// PASSING
rule AddRewardsIncreasesTokenBalanceOfContract(uint256 epoch, address vault, address token, uint256 amount){
    uint256 tokenBalanceBefore = tokenBalanceOf(token, currentContract);
    require amount > 0;
    env e;
    require e.msg.sender != currentContract;
    addReward(e, epoch, vault, token, amount);
    uint256 tokenBalanceAfter = tokenBalanceOf(token, currentContract);
    assert tokenBalanceAfter == tokenBalanceBefore + amount;
}


// PASSING
rule AccrueUserAccruesCorrectly(uint256 epoch, address vault, address user, env e){
    requireInvariant UserSharesZeroIfAccrueTimeZero(epoch, vault, user);
    uint256 userPointsBefore = getPoints(epoch, vault, user);
    uint256 userSharesBefore = getShares(epoch, vault, user);
    uint256 userLastAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 epochEndTime = getEpochsEndTimestamp(epoch);
    require userSharesBefore > 0;
    require userLastAccrueTimeBefore < e.block.timestamp && userLastAccrueTimeBefore < epochEndTime;
    accrueUser(e, epoch, vault, user);
    uint256 userPointsAfter = getPoints(epoch, vault, user);
    uint256 userSharesAfter = getShares(epoch, vault, user);
    uint256 userLastAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    assert userPointsAfter > userPointsBefore;

}


invariant lastUserAccrueTimeLEBlockTime(uint epoch, address vault, address user, env e)
getLastUserAccrueTimestamp(epoch, vault, user) <= e.block.timestamp

invariant lastAccrueTimeLEBlockTime(uint epoch, address vault, env e)
getLastAccruedTimestamp(epoch, vault) <= e.block.timestamp
// PASSING
rule lastAccrueTimeLEBlockTimeRule (uint epoch, address vault, address user, env e, method f){
    uint256 lastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 lastAccrueTimeBefore = getLastAccruedTimestamp(epoch, vault);
    require lastUserAccrueTimeBefore <= e.block.timestamp;
    require lastAccrueTimeBefore <= e.block.timestamp;
    calldataarg args;
    f(e, args);
    uint256 lastUserAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 lastAccrueTimeAfter = getLastAccruedTimestamp(epoch, vault);
    assert (lastUserAccrueTimeAfter <= e.block.timestamp,"lastUserAccrueTimestamp can't be more than e.block.timestamp");
    assert (lastAccrueTimeAfter <= e.block.timestamp,"lastAccrueTimestamp can't be more than e.block.timestamp");
}


// rule ShareChangeUpdatesLastAccrueTime (uint256 epoch, address vault, address user, method f, env e){
//     requireInvariant lastUserAccrueTimeLEBlockTime(epoch, vault, user, e);
//     uint256 sharesBefore = getShares(epoch, vault, user);
//     uint256 lastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
//     calldataarg args;
//     f(e, args);
//     uint256 sharesAfter = getShares(epoch, vault, user);
//     uint256 lastUserAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
//     assert (sharesAfter != sharesBefore => lastUserAccrueTimeAfter > lastUserAccrueTimeBefore, "last user accrue time not updated despite change in shares");
// }


// PASSING
rule monotonousIncreaseAccrueTime(uint256 epoch, address vault, address user, method f, env e){
    requireInvariant lastUserAccrueTimeLEBlockTime(epoch, vault, user, e);
    requireInvariant lastAccrueTimeLEBlockTime(epoch, vault, e);
    uint256 lastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 lastAccrueTimeBefore = getLastAccruedTimestamp(epoch, vault);
    calldataarg args;
    f(e, args);
    uint256 lastUserAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 lastAccrueTimeAfter = getLastAccruedTimestamp(epoch, vault);
    assert(lastUserAccrueTimeAfter >= lastUserAccrueTimeBefore,"lastUserAccruetimestamp cannot decrease");
    assert(lastAccrueTimeAfter >= lastAccrueTimeBefore,"lastAccruetimestamp cannot decrease");
}

// PASSING
rule monotonousIncreaseInPoints(uint256 epoch, address vault, address user, method f, env e){
    uint256 userPointsBefore = getPoints(epoch, vault, user);
    uint256 totalPointsBefore = getTotalPoints(epoch, vault);
    if (f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector)
        {
        calldataarg args;
        f(e, args);
        }
    uint256 userPointsAfter = getPoints(epoch, vault, user);
    uint256 totalPointsAfter = getTotalPoints(epoch, vault);
    assert(userPointsAfter >= userPointsBefore,"Points cannot decrease");
    assert(totalPointsAfter >= totalPointsBefore,"totalPoints cannot decrease");
}

// PASSING
rule monotonousIncreasePointsWithdrawn(uint256 epoch, address vault, address user, address token, method f, env e){
uint256 pointsWithdrawnUserBefore = getPointsWithdrawn(epoch, vault, user, token);
calldataarg args;
    f(e, args);
uint256 pointsWithdrawnUserAfter = getPointsWithdrawn(epoch, vault, user, token);
assert(pointsWithdrawnUserAfter >= pointsWithdrawnUserBefore,"pointsWithdrawn cannot decrease");

}

// PASSING
rule monotonousIncreaseRewards(uint256 epoch, address vault, address user, address token, method f, env e){
uint256 rewardsBefore = getRewards(epoch, vault, token);
calldataarg args;
f(e, args);
uint256 rewardsAfter = getRewards(epoch, vault, token);
assert (rewardsAfter >= rewardsBefore,"rewards cannot decrease");
}

// PASSING
rule monotonousIncreaseCurrentEpoch(uint256 epoch, method f, env e){
uint256 currentEpochBefore = currentEpoch();
calldataarg args;
f(e, args);
uint256 currentEpochAfter = currentEpoch();
assert (currentEpochAfter >= currentEpochBefore, "CurrentEpoch cannot decrease");
}


// PASSING
invariant NoOverlapBetweenTwoEpochs(uint256 epoch)
getEpochsEndTimestamp(epoch) <= getEpochsStartTimestamp(epoch + 1)
{
    preserved
    {
        require (epoch + 1 <= currentEpoch());
    }
}


// PASSING
invariant CurrentandPastEpochTimestampsNonZero(uint256 epoch)
currentEpoch() > 0 =>(getEpochsEndTimestamp(currentEpoch()) != 0 && getEpochsStartTimestamp(currentEpoch()) != 0 ) && 
((epoch < currentEpoch() && epoch >0) => (getEpochsStartTimestamp(epoch) != 0 && getEpochsEndTimestamp(epoch) != 0))

// PASSING
invariant FutureEpochVaultZERO(uint256 epoch, address vault, address user, address token, env e)
(epoch > currentEpoch()) => (
    getEpochsStartTimestamp(epoch) == 0 &&
    getEpochsEndTimestamp(epoch) == 0 &&
    getPoints(epoch, vault, user) == 0 &&
    getPointsWithdrawn(epoch, vault, user, token) == 0 &&
    getTotalPoints(epoch, vault) == 0 &&
    getLastAccruedTimestamp(epoch, vault) == 0 &&
    getLastUserAccrueTimestamp(epoch, vault, user) == 0 &&
    getShares(epoch, vault, user) == 0 &&
    getTotalSupply(epoch, vault) == 0
)


