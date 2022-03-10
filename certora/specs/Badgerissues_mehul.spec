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

invariant epochSequential(uint256 epoch)
    epochEnd(epoch) < epochStart(to_uint256(epoch+1)) || (epochStart(epoch) ==0 && epochEnd(epoch) == 0)


// last Accrue times
ghost timeLastAccrueUser(uint256, address, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address user. forall address vault.
    timeLastAccrueUser(epoch, vault, user) == 0;
}

ghost timeLastAccrueVault(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault.
    timeLastAccrueVault(epoch, vault) == 0;
}

hook Sstore lastUserAccrueTimestamp[KEY uint256 epoch][KEY address vault][KEY address user] uint256 value (uint256 old_value) STORAGE {
    havoc timeLastAccrueUser assuming timeLastAccrueUser@new(epoch, vault, user) == value;
}

hook Sstore lastAccruedTimestamp[KEY uint256 epoch][KEY address vault] uint256 value (uint256 old_value) STORAGE {
    havoc timeLastAccrueVault assuming timeLastAccrueVault@new(epoch, vault) == value;
}


// Accrue time rules : If updated, it should point to current time
rule lastVaultAccrueAfterCurentEpochStart(uint256 epoch, address vault,  method f){
    uint256 before = timeLastAccrueVault(epoch, vault);
    env e; calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueVault(epoch, vault);
    assert ((before == after) || epochStart(currentEpoch()) < after);
}

rule lastUserAccrueAfterCurentEpochStart(uint256 epoch, address vault, address user,  method f){
    uint256 before = timeLastAccrueUser(epoch, vault, user);
    env e; calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueUser(epoch, vault, user);
    assert ((before == after) || epochStart(currentEpoch()) < after);
}

// lastAccrueTimestamp non-decreasing
rule nonDecreasingLastAccruedTimestamp(uint256 epoch, address vault, method f){
    env e;
    uint256 before = timeLastAccrueVault(epoch, vault);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueVault(epoch, vault);
    assert(before <= after, "lastAccruedTimestamp decreased");
}

rule nonDecreasingLastUserAccrueTimestamp(uint256 epoch, address vault, address user, method f){
    env e;
    uint256 before = timeLastAccrueUser(epoch, vault, user);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueUser(epoch, vault, user);
    assert(before <= after, "lastAccrueUserTimestamp decreased");
}


// Each user's share
ghost userShare(uint256, address, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address user. forall address vault.
    userShare(epoch, vault, user) == 0;
}

// Ghost to calculate sum of user balance at any epoch
ghost userShareSum(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault.
    userShareSum(epoch, vault) == 0;
}

hook Sstore shares[KEY uint256 epoch][KEY address vault][KEY address user] uint256 value (uint256 old_value) STORAGE {
    havoc userShareSum assuming userShareSum@new(epoch, vault) == userShareSum@old(epoch, vault) + value - old_value;
    havoc userShare assuming userShare@new(epoch, vault, user) == userShare@old(epoch, vault, user);
}

// Sum of user balances should equal total supply - IMPORTANT
// Fails during notifyTransfer (0x0, 0x0, amount) - increases shares without any change to balances
rule sumOfUserBalancesShouldMatchTotalSupply(uint256 epoch, address vault, address user, method f){
    require(epoch <= currentEpoch());
    requireInvariant epochSequential(epoch);
    require(userShareSum(epoch, vault) == totalSupply(epoch, vault));
    env e; calldataarg args;
    f(e, args);
    assert(userShareSum(epoch, vault) == totalSupply(epoch, vault));
}