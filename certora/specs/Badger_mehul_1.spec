// Rules for badgerDao Care
import "sanity.spec"

methods {
    // constants
    SECONDS_PER_EPOCH() returns(uint256) envfree // => ALWAYS(604800)
    MAX_BPS() returns(uint256) envfree => ALWAYS(10000)

    // other variables
    currentEpoch() returns(uint256) envfree

    // mapping harness getters
    getEpochsStartTimestamp(uint256) returns(uint256) envfree
    getEpochsEndTimestamp(uint256) returns(uint256) envfree
    getPoints(uint256, address, address) returns(uint256) envfree
    getPointsWithdrawn(uint256, address, address, address) returns(uint256) envfree
    getTotalPoints(uint256, address) returns(uint256) envfree
    getLastAccruedTimestamp(uint256, address) returns(uint256) envfree
    getLastUserAccrueTimestamp(uint256, address, address) returns(uint256) envfree
    getLastVaultDeposit(address) returns(uint256) envfree
    getShares(uint256, address) returns(uint256) envfree
    getTotalSupply(uint256, address) returns(uint256) envfree
    getRewards(uint256 , address, address) returns(uint256) envfree

    // methods
    startNextEpoch()
    accrueVault(uint256, address)
    getVaultTimeLeftToAccrue(uint256, address) returns(uint256)
    claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[])
    addRewards(uint256[], address[], address[], uint256[])
    addReward(uint256, address, address, uint256)
    notifyTransfer(address, address, uint256)
    accrueUser(uint256, address, address)
    getUserTimeLeftToAccrue(uint256, address, address) returns(uint256)
    claimRewards(uint256[], address[], address[], address[])
    claimReward(uint256, address, address, address)
    claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address)
    handleDeposit(address, address, uint256)
    handleWithdrawal(address, address, uint256)

    // envfree methods
    getTotalSupplyAtEpoch(uint256, address) returns(uint256, bool) envfree
    handleTransfer(address, address, address, uint256) envfree
    getBalanceAtEpoch(uint256, address, address) returns(uint256, bool) envfree
    requireNoDuplicates(address[]) envfree
    min(uint256, uint256) returns(uint256) envfree
    tokenBalanceOf(address, address) returns(uint256) envfree
}

// Original Certora rules

rule startNextEpochCheck(method f, env e){
    uint256 epochId = to_uint256(currentEpoch() + 1);

    startNextEpoch(e);

    uint256 epochStartAfter = getEpochsStartTimestamp(epochId);
    uint256 epochEndAfter = getEpochsEndTimestamp(epochId);

    assert epochStartAfter == e.block.timestamp, "wrong start";
    assert epochEndAfter == e.block.timestamp + 604800, "wrong end";
}

// rule whoChangedMyBalance(address token, address user, method f) filtered {f -> !f.isView} {
//     uint256 before = tokenBalanceOf(token,user);
//     env e;
//     calldataarg args;
//     f(e,args);
//     assert tokenBalanceOf(token,user) == before;
// }

rule canAnyFunctionChangeMoreThanOneToken(address token1, address token2, address user, method f) {
    require token1!=token2;
    uint256 before1 = tokenBalanceOf(token1,user);
    uint256 before2 = tokenBalanceOf(token2,user);
    env e;
    calldataarg args;
    f(e,args);
    assert tokenBalanceOf(token1,user) == before1 || tokenBalanceOf(token2,user) == before2;
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


// Reward rules
// rewards mapping should not be reduced under any circumstances
// Otherwise, someone transferred rewards out through addRewards function
// or wrote a value they shouldn't be able to write
rule nonDecreasingRewards (uint256 epochId, address vault, address token, method f) {
    uint256 before = getRewards(epochId, vault, token);
    env e;
    calldataarg args;
    f(e, args);
    uint256 after = getRewards(epochId, vault, token);
    assert(before <= after);
}