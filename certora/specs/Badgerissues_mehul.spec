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


// Is the order of acrue functions important?
// acrueVault is always called after acrueUser
// Does accrual before calling any function produce the same result?