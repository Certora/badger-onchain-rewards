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

// PASSING
invariant SumOfUserSharesLETotalSupplyinEpochVault (uint256 ep, address vlt)
getTotalSupply(ep, vlt) >= Sum_Shares_Ghost(ep, vlt)

// In a given epoch, if a vault has been accrued after the accrual of a user in the same vault and epoch, the totalPoints of the vault
// will be greater that or equal to the points of the user.


invariant TotalPointsGEUserPoints(uint256 epoch, address vault, address user)
(getLastAccruedTimestamp(epoch, vault) >= getLastUserAccrueTimestamp(epoch, vault, user)) => 
(getTotalPoints(epoch, vault) >= getPoints(epoch, vault, user))
// {
//     preserved with (env e)
//     {
//         require getLastAccruedTimestamp(epoch, vault) < e.block.timestamp;
//         require getLastUserAccrueTimestamp(epoch, vault, user) < e.block.timestamp;
//     }
// }

invariant AccruedVaultTotalPointsGEUserPointsInVault(env e, uint256 epoch, address vault, address user)
((getLastAccruedTimestamp(epoch, vault) >= getLastUserAccrueTimestamp(epoch, vault, user)) &&
(getLastAccruedTimestamp(epoch, vault) < e.block.timestamp)) => 
(getTotalPoints(epoch, vault) >= getPoints(epoch, vault, user))


rule AccruedVaultTotalPointsGEUserPointsInVaultRule(env e, uint256 epoch, address vault, address user, method f){
    requireInvariant UserPointsZeroIfAccrueTimeZero(epoch, vault, user);
    requireInvariant TotalPointsZeroIfAccrueTimeZero(epoch, vault);
    requireInvariant SumOfUserSharesLETotalSupplyinEpochVault(epoch, vault);
    uint256 lastAccrueTimeBefore = getLastAccruedTimestamp(epoch, vault);
    uint256 lastUserAccrueTimeBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 totalPointsBefore = getTotalPoints(epoch, vault);
    uint256 userPointsBefore = getPoints(epoch, vault, user);
    require (lastAccrueTimeBefore >= lastUserAccrueTimeBefore) => (totalPointsBefore >= userPointsBefore);
    require lastAccrueTimeBefore < e.block.timestamp;
    require lastUserAccrueTimeBefore < e.block.timestamp;
    calldataarg args;
    f(e, args);
    uint256 lastAccrueTimeAfter = getLastAccruedTimestamp(epoch, vault);
    uint256 lastUserAccrueTimeAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    uint256 totalPointsAfter = getTotalPoints(epoch, vault);
    uint256 userPointsAfter = getPoints(epoch, vault, user);
    assert ((lastAccrueTimeAfter >= lastUserAccrueTimeAfter) => (totalPointsAfter >= userPointsAfter),"If vault has been accrued after the user then the total Points should be greater than or equal to user points");
    // assert false;
}

// transfer the right amount of reward tokens to the user
// updates the pointswithdrawn correctly

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

