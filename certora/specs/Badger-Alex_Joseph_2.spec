//  *************************************************************************************************************************************
//  * IMPORTS/SETUP                                                                                                                     *
//  *************************************************************************************************************************************
import "itsLikeAReward.spec"


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