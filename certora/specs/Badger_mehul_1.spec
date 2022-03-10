// Rules for badgerDao Care
methods {
    startNextEpoch()
    accrueVault(uint256, address)
    getVaultTimeLeftToAccrue(uint256, address) returns uint256
    getTotalSupplyAtEpoch(uint256, address) returns (uint256, bool) envfree
    claimRewards(uint256[], address[], address[], address[])
    claimReward(uint256, address, address, address)
    claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address)
    claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[])
    addRewards(uint256[], address[], address[], uint256[])
    addReward(uint256, address, address, uint256) //nonreentrant
    notifyTransfer(address, address, uint256)
    accrueUser(uint256, address, address)
    getUserTimeLeftToAccrue(uint256, address, address) returns uint256
    getBalanceAtEpoch(uint256, address, address) returns (uint256, bool) envfree
    //variables
    currentEpoch() returns uint256 envfree
    epochs(uint256) returns uint256, uint256 envfree
    SECONDS_PER_EPOCH() returns uint256 envfree
    lastAccruedTimestamp(uint256, address) returns uint256 envfree
    lastUserAccrueTimestamp(uint256, address, address) returns uint256 envfree
    totalSupply(uint256, address) returns uint256 envfree
}

rule MethodsVacuityCheck(method f) {
	env e; calldataarg args;
	f(e, args);
	assert false, "this method should have a non reverting path";
}

// Epoch Rules
function epochStart(uint256 epoch) returns uint256{
    uint256 start; uint256 end;
    start, end = epochs(epoch);
    return start;
}

function epochEnd(uint256 epoch)returns uint256{
    uint256 start; uint256 end;
    start, end = epochs(epoch);
    return end;
}
// Ghost variable to keep track of starting times of each epoch
ghost epStart(uint256) returns uint256 {
    init_state axiom forall uint256 epoch. epStart(epoch) == 0;
}

hook Sstore epochs[KEY uint256 ep].(offset 0) uint256 value (uint256 old_value) STORAGE {
    // Note that currentEpoch is updated before epochs(currentEpoch has a value)
    // Need to find workaraound to struct maps
    havoc epStart assuming forall uint256 epoch.
    epoch == ep? epStart@new(epoch) == value : epStart@new(epoch) == epStart@old(epoch);
}

function epEnd(uint256 epoch) returns uint256{
    if (epStart(epoch) == 0) return 0;
    else return to_uint256(epStart(epoch) + SECONDS_PER_EPOCH());
}

//Invariant : New epoch should start after previous epoch is over
invariant epochSequential(uint256 epoch)
    epEnd(epoch) < epStart(to_uint256(epoch+1)) || (epStart(epoch) ==0 && epEnd(epoch) == 0)

// currentEpoch should never decrease
rule nonDecreasingCurrentEpoch(method f){
    uint256 before = currentEpoch();
    env e;
    calldataarg args;
    f(e, args);
    uint256 after = currentEpoch();
    assert(before == after || 
        (before < after && f.selector == startNextEpoch().selector),
        "incorrect currentEpoch");
}
