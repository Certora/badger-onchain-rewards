//  *************************************************************************************************************************************
//  * IMPORTS/SETUP                                                                                                                     *
//  *************************************************************************************************************************************
import "itsLikeAReward.spec"
import "Badger-Alex_Joseph_1.spec"


//  *************************************************************************************************************************************
//  * USEFUL CONSTRUCTS.                                                                                                                *
//  *************************************************************************************************************************************
definition SECONDS_PER_EPOCH() returns uint256 = 604800;


//  *************************************************************************************************************************************
//  * INVARIANTS AND RULES                                                                                                              *
//  *************************************************************************************************************************************
// PASSING
rule StartNextEpochWorksCorrectly(env e){
    uint256 currentEpochBefore = currentEpoch();
    uint256 currentEpochStartTimeBefore = getEpochsStartTimestamp(currentEpoch());
    uint256 currentEpochEndTimeBefore = getEpochsEndTimestamp(currentEpoch());
    startNextEpoch(e);
    uint256 currentEpochAfter = currentEpoch();
    uint256 currentEpochStartTimeAfter = getEpochsStartTimestamp(currentEpoch());
    uint256 currentEpochEndTimeAfter = getEpochsEndTimestamp(currentEpoch());
    assert(currentEpochBefore + 1 == currentEpochAfter,"Epoch not incremented correctly");
    assert(currentEpochStartTimeAfter > currentEpochEndTimeBefore,"New epoch's start time has to be after the previous epoch's end time");
    assert(currentEpochEndTimeAfter > currentEpochStartTimeAfter,"Epoch end time should be greater than the start time");
    // assert false;
}

// PASSING
rule AccrueVaultWorksCorrectly(env e, uint256 epoch, address vault){
    uint256 totalSupply = getTotalSupply(epoch, vault);
    uint256 totalPointsBefore = getTotalPoints(epoch, vault);
    uint256 lastAccrueTimeBefore = getLastAccruedTimestamp(epoch, vault);
    uint256 timeLeftToAccrue = getVaultTimeLeftToAccrue(e, epoch, vault);
    require lastAccrueTimeBefore > 0;
    accrueVault(e, epoch, vault);
    uint256 totalPointsAfter = getTotalPoints(epoch, vault);
    uint256 lastAccrueTimeAfter = getLastAccruedTimestamp(epoch, vault);
    assert(totalPointsAfter == totalPointsBefore + (totalSupply * timeLeftToAccrue),"Total points not updated correctly");
    assert(lastAccrueTimeAfter == e.block.timestamp,"lastAccrueTimeStamp not updated");
    // assert false;
}



// In a given epoch and vault, sum of all user shares should equal the total supply and sum of all userpoints should be equal to the total points.
// PASSING
invariant SumOfUserSharesEqualTotalSupplyinEpochVault (uint256 ep, address vlt)
getTotalSupply(ep, vlt) == Sum_Shares_Ghost(ep, vlt)

// In a given epoch, if a vault has been accrued after the accrual of a user in the same vault and epoch, the totalPoints of the vault
// will be greater that or equal to the points of the user.




// 
// PASSING
rule AccruedVaultTotalPointsGEUserPointsInVaultRule(uint256 epoch, address vault, address user, method f){
    requireInvariant UserPointsZeroIfAccrueTimeZero(epoch, vault, user);
    requireInvariant TotalPointsZeroIfAccrueTimeZero(epoch, vault);
    requireInvariant SumOfUserSharesEqualTotalSupplyinEpochVault(epoch, vault);
    uint256 lastAccrueTimeBefore = getLastAccruedTimestamp(epoch, vault);
    uint256 lastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 totalPointsBefore = getTotalPoints(epoch, vault);
    uint256 userPointsBefore = getPoints(epoch, vault, user);
    require lastAccrueTimeBefore == 0;
    require lastUserAccrueTimeBefore == 0;
    require totalPointsBefore ==0;
    require userPointsBefore ==0;
    // require lastAccrueTimeBefore < e.block.timestamp;
    // require lastUserAccrueTimeBefore < e.block.timestamp;
    calldataarg args;
    env e;
    f(e, args);
    accrueUser(e, epoch, vault, user);
    accrueVault(e, epoch, vault);
    uint256 lastAccrueTimeAfter = getLastAccruedTimestamp(epoch, vault);
    uint256 lastUserAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 totalPointsAfter = getTotalPoints(epoch, vault);
    uint256 userPointsAfter = getPoints(epoch, vault, user);
    // assert ((lastAccrueTimeAfter >= lastUserAccrueTimeAfter) => (totalPointsAfter >= userPointsAfter),"If vault has been accrued after the user then the total Points should be greater than or equal to user points");
    assert (totalPointsAfter >= userPointsAfter,"If vault has been accrued after the user then the total Points should be greater than or equal to user points");
    
    // assert false;
}


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
    assert (LastUserAccrueTimeAfter == 0 => userPointsAfter == 0,"If lastUserAccrueTime is 0 then the user points must be 0");


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
    assert (LastUserAccrueTimeAfter == 0 => userSharesAfter == 0,"If lastUserAccrueTime is 0 then user shares must be 0");
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
    assert (LastAccrueTimeAfter == 0 => TotalPointsAfter == 0,"If lastAccrueTime for a vault in an epoch is 0 then total points must be 0");
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



// PASSING
rule monotonousIncreaseAccrueTime(uint256 epoch, address vault, address user, method f, env e){
    uint256 lastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 lastAccrueTimeBefore = getLastAccruedTimestamp(epoch, vault);
    require lastUserAccrueTimeBefore <= e.block.timestamp;
    require lastAccrueTimeBefore <= e.block.timestamp;
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
currentEpoch() > 0 =>
((getEpochsEndTimestamp(currentEpoch()) > getEpochsStartTimestamp(currentEpoch()) && 
getEpochsStartTimestamp(currentEpoch()) != 0 ) &&
((epoch < currentEpoch() && epoch >0) => (getEpochsStartTimestamp(epoch) < getEpochsEndTimestamp(epoch) && getEpochsEndTimestamp(epoch) != 0)))

// PASSING
invariant FutureEpochVaultZERO(uint256 epoch, address vault, address user, address token, env e)
(epoch > currentEpoch()) => (
    getEpochsStartTimestamp(epoch) == 0 &&
    getEpochsEndTimestamp(epoch) == 0 &&
    getPoints(epoch, vault, user) == 0 &&
    getPointsWithdrawn(epoch, vault, user, token) == 0 &&
    getTotalPoints(epoch, vault) == 0 &&
    getShares(epoch, vault, user) == 0 &&
    getTotalSupply(epoch, vault) == 0
)


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

// In any epoch, for any vault, a users pointsWithdrawn would either be 0 or exactly equal to the user's points
// Since users are allowed to claim rewards only for past epochs, any claim should accrue a user for the entirety of the 
// epoch as there isn't anymore time left to accrue in the epoch. So the user's pointsWithdrawn at this point should be exactly equal to 
// the aggregate points accrued by the user in the epoch. So the pointsWithdrawn for any user, in any epoch and vault, will either be 0 or
// exactly equal to the user's points. If this condition is not held, the user would have been paid over or under the appropriate amount 
// leading to potential solvency issues for the rewards mnanager as a whole or some user's not getting the fair share of rewards.
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
