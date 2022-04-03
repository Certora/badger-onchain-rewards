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

// points
invariant userPointsLessThanTotal(uint256 epoch, address vault, address user)
    userPoints(epoch, vault, user) <= userPointsSum(epoch, vault)
    
// if user points sum is correct, no function should make it wrong
rule sumOfUserPointsShouldMatchTotalPoints(uint256 epoch, address vault, address user, method f){
    env e; calldataarg args;

    require(e.msg.sender != 0);
    require(epoch <= currentEpoch());
    requireInvariant sequentialEpoch(e, epoch);
    
    require(userPointsSum(epoch, vault) == getTotalPoints(epoch, vault));
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
// Seems like a bug in Certora - check accrueVault answer on prover
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

// lastAccrueUserTimestamp non-decreasing
// // Seems like a bug in Certora - check accrueUser answer on prover
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
