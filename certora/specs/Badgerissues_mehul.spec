// Rules for badgerDao Care
import "Badger_mehul_1.spec"

// **** Utility functions **** 
function validTimestamp(env e) returns bool{
    return (e.block.timestamp >= getEpochsStartTimestamp(currentEpoch()));
}

//Invariant : New epoch should start after previous epoch is over
invariant sequentialEpoch(env e, uint256 epoch) 
    (epoch <= currentEpoch() && epoch > 0) => (
        (getEpochsEndTimestamp(epoch) < getEpochsStartTimestamp(to_uint256(epoch+1)))
        && (getEpochsEndTimestamp(epoch) - getEpochsStartTimestamp(epoch) == SECONDS_PER_EPOCH())
        && e.block.timestamp >= getEpochsStartTimestamp(epoch)
        )
    {
        preserved startNextEpoch() with (env e2){
            // Only added because currentEpoch is updated before timestamps are set
            require(epoch < currentEpoch());
        }
    }


// Issues in the contract

// Vault accrue
// @note : Fails for epoch = 0
// @note : solution - require (epoch>0)
// or disallow adding tokens and increasing totalSupply before epoch 1
rule unaccruedVaultUpdateValueMatches(uint256 epoch, address vault){
    env e;

    require(timeLastAccrueVault(epoch, vault) <= getEpochsStartTimestamp(epoch));

    uint256 pointsBefore = getTotalPoints(epoch, vault);
    uint256 lastAccrue = getLastAccruedTimestamp(epoch, vault);
    require(lastAccrue <= getEpochsStartTimestamp(epoch));
    accrueVault(e, epoch, vault);
    uint256 pointsAfter = getTotalPoints(epoch, vault);

    // ideally pointsBefore should also be 0
    assert( 
        (epoch < currentEpoch() => pointsAfter - pointsBefore == getTotalSupply(epoch, vault)*SECONDS_PER_EPOCH())
        && (epoch > currentEpoch() => pointsAfter == pointsBefore)
    );
}

// Shares / supply
// Each user's share is less than total sum of all user shares
// @note : Fails during notifyTransfer (0x0, 0x0, amount) - increases vault share without updating total supply
invariant userShareLessThanTotal(uint256 epoch, address vault, address user)
    userShare(epoch, vault, user) <= userShareSum(epoch, vault)


// Sum of user balances should equal total supply - IMPORTANT
// @note : Fails during notifyTransfer (0x0, 0x0, amount) - increases shares without any change to balances
// @note : No function should create a mismatch between supply and sum of user shares
rule sumOfUserSharesShouldMatchTotalSupply(uint256 epoch, address vault, address user, method f){
    env e; calldataarg args;

    require(e.msg.sender != 0);
    require(epoch <= currentEpoch());
    requireInvariant sequentialEpoch(e, epoch);

    require(userShareSum(epoch, vault) == getTotalSupply(epoch, vault));
    f(e, args);
    assert(userShareSum(epoch, vault) == getTotalSupply(epoch, vault));
}

// points
invariant userPointsLessThanTotal(uint256 epoch, address vault, address user)
    userPoints(epoch, vault, user) <= userPointsSum(epoch, vault)
    

rule sumOfUserPointsShouldMatchTotalPoints(uint256 epoch, address vault, address user, method f){
    env e; calldataarg args;

    require(e.msg.sender != 0);
    require(epoch <= currentEpoch());
    requireInvariant sequentialEpoch(e, epoch);
    
    require(e.msg.sender != 0);
    f(e, args);
    assert(userPointsSum(epoch, vault) == getTotalPoints(epoch, vault));
}

// Additionally, userPoints should never decrease since that is handled by pointsWithdrawn
rule userPointsNonDecreasing(uint256 epoch, address vault, address user, method f){
    env e; calldataarg args;
    uint256 pointsBefore = userPoints(epoch, vault, user);
    f(e, args);
    uint256 pointsAfter = userPoints(epoch, vault, user);
    assert(pointsAfter >= pointsBefore, "User points decreased, shouldn't happen");
}



// Accrue time rules : If updated, it should point to current time
rule lastVaultAccrueAfterCurentEpochStart(uint256 epoch, address vault,  method f) filtered {f -> !f.isView}{
    env e; 
    requireInvariant sequentialEpoch(e, epoch);
    require(validTimestamp(e));
    uint256 before = timeLastAccrueVault(epoch, vault);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueVault(epoch, vault);
    assert ((before == after) || getEpochsStartTimestamp(currentEpoch()) < after);
}

rule lastUserAccrueAfterCurentEpochStart(uint256 epoch, address vault, address user,  method f) filtered {f -> !f.isView}{
    env e; 
    requireInvariant sequentialEpoch(e, epoch);
    require(validTimestamp(e));
    uint256 before = timeLastAccrueUser(epoch, vault, user);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueUser(epoch, vault, user);
    assert ((before == after) || getEpochsStartTimestamp(currentEpoch()) < after);
}

// lastAccrueTimestamp non-decreasing
rule nonDecreasingLastAccruedTimestamp(uint256 epoch, address vault, method f) filtered {f -> !f.isView}{
    env e;
    requireInvariant sequentialEpoch(e, epoch);
    require(validTimestamp(e));
    uint256 before = timeLastAccrueVault(epoch, vault);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueVault(epoch, vault);
    assert(before <= after, "lastAccruedTimestamp decreased");
}

rule nonDecreasingLastUserAccrueTimestamp(uint256 epoch, address vault, address user, method f) filtered {f -> !f.isView}{
    env e;
    requireInvariant sequentialEpoch(e, epoch);
    require(validTimestamp(e));
    uint256 before = timeLastAccrueUser(epoch, vault, user);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueUser(epoch, vault, user);
    assert(before <= after, "lastAccrueUserTimestamp decreased");
}




// Is the order of acrue functions important?
// acrueVault is always called after acrueUser
// Does accrual before calling any function produce the same result?
//rule vaultAccrueBeforeCallChangesOutput()


// Rewards to any particular user should match calculation
// Add reward, call claimReward
// Checking for loop functions with two tokens should be sufficient

// definition functionNotAddReward(method f) returns bool =
//        f.selector != addReward(uint256, address, address, uint256).selector
//        && f.selector != addRewards(uint256[], address[], address[], uint256[]).selector
//        ;

// definition functionNotClaimReward(method f) returns bool =
//        f.selector != claimRewards(uint256[], address[], address[], address[]).selector
//        && f.selector != claimReward(uint256, address, address, address).selector
//        ;

// rule rewardsMatchCalculation(
//         address user1, 
//         address user2, 
//         address vault, 
//         uint256 epoch, 
//         address token, 
//         uint256 amount,
//         method f1,
//         method f2)
//    filtered {f1 -> !f1.isView, f2-> !f2.isView } {
//     require(functionNotAddReward(f1));
//     require(functionNotClaimReward(f2));

//     env e1; env e2; env e3;
//     calldataarg args;
//     calldataarg args2;

//     require(e2.msg.sender == user2);
//     require(user1 != user2);

//     addReward(e1, epoch, vault, token, amount);
//     uint256 firstRewards = getRewards(epoch, vault, token);
//     uint256 balanceBefore = tokenBalanceOf(token, user1);
//     f1(e2, args);
//     uint256 userRewards = getEligibleRewards(epoch, vault, token, user1);
//     f2(e3, args2);
//     claimReward(e3, epoch, vault, token, user1);
//     uint256 balanceAfter = tokenBalanceOf(token, user1); 

//     assert(
//         firstRewards == amount // Rewards added correctly
//         && (balanceAfter - balanceBefore == userRewards) // user balance is correct
//     );
// }