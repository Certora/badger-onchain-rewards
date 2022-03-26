//  **** Rules for badgerDao Care **** 
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
    getEligibleRewardsForAmount(uint256 , address, address, address, uint256) returns(uint256) envfree
    getEpoch(uint256) returns (uint256, uint256) envfree

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
    handleTransfer(address, address, address, uint256)

    // envfree methods
    getTotalSupplyAtEpoch(uint256, address) returns(uint256, bool) envfree
    getBalanceAtEpoch(uint256, address, address) returns(uint256, bool) envfree
    requireNoDuplicates(address[]) envfree
    min(uint256, uint256) returns(uint256) envfree
    tokenBalanceOf(address, address) returns(uint256) envfree
}

// **** Utility functions **** 
function validTimestamp(env e) returns bool{
    return (e.block.timestamp >= getEpochsStartTimestamp(currentEpoch()));
}


// **** Epoch Rules **** 
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

// Uninitialized epochs should have 0 timestamps
invariant epochNotStarted(uint256 epoch)
    (epoch > currentEpoch() || epoch == 0) => (
        getEpochsStartTimestamp(epoch) == 0 
        && getEpochsEndTimestamp(epoch) == 0 
    )
    {
        preserved startNextEpoch() with (env e2){
            require(epoch > to_uint256(currentEpoch() + 1));
        }
    }

// Epoch state change restrictions
rule epochChange(method f){
    uint256 epochBefore = currentEpoch();
    env e;
    calldataarg args;
    f(e, args);
    uint256 epochAfter = currentEpoch();
    assert(
        epochBefore == epochAfter ||
        (
            (f.selector == startNextEpoch().selector)
            && (epochAfter == epochBefore + 1)
            && (e.block.timestamp > getEpochsEndTimestamp(epochBefore))
            && (e.block.timestamp == getEpochsStartTimestamp(epochAfter))
            && (e.block.timestamp < getEpochsEndTimestamp(epochAfter))
            ),
        "Epoch can only increase by one, no other function can change state"
    );
}

// currentEpoch should never decrease
rule nonDecreasingCurrentEpoch(method f) filtered {f -> !f.isView}{
    uint256 before = currentEpoch();
    env e;
    calldataarg args;
    f(e, args);
    uint256 after = currentEpoch();
    assert(before == after || 
        (before < after && f.selector == startNextEpoch().selector),
        "Epoch can only be changed by startNextEpoch by a single step");
}

// **** Reward rules **** 
// rewards mapping should not be reduced under any circumstances
// Otherwise, someone transferred rewards out through addRewards function
// or wrote a value they shouldn't be able to write
rule nonDecreasingRewards (uint256 epochId, address vault, address token, method f)  filtered {f -> !f.isView}{
    uint256 before = getRewards(epochId, vault, token);
    env e;
    calldataarg args;
    f(e, args);
    uint256 after = getRewards(epochId, vault, token);
    assert(before <= after);
}

// Calculated value of rewards should match balance transferred
rule rewardsMatchCalculation(
        address user, 
        address vault, 
        uint256 epoch, 
        address token, 
        uint256 amount){

    env e1; env e2;

    addReward(e1, epoch, vault, token, amount);
    uint256 firstRewards = getRewards(epoch, vault, token);
    uint256 balanceBefore = tokenBalanceOf(token, user);

    uint256 userRewards = getEligibleRewardsForAmount(epoch, vault, token, user, amount);

    claimReward(e2, epoch, vault, token, user);
    uint256 balanceAfter = tokenBalanceOf(token, user); 

    assert(
        firstRewards == amount // Rewards added correctly
        && (balanceAfter - balanceBefore == userRewards) // user balance is correct
    );
}



// **** Shares / supply rules **** 
// Rules regarding how user balances are updated
// Each user's share in a vault at an epoch
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

// Each user's share is less than total sum of all user shares
invariant userShareLessThanTotal(uint256 epoch, address vault, address user)
    userShare(epoch, vault, user) <= userShareSum(epoch, vault)

// This invariant cannot be used because user shares are updated before total supply
// invariant sumOfUserShareMatchesTotalSupply(uint256 epoch, address vault)
//     userShareSum(epoch, vault) <= getTotalSupply(epoch, vault) // In case users haven't been accrued

// No function should create a mismatch between supply and sum of user shares
rule sumOfUserSharesShouldMatchTotalSupply(uint256 epoch, address vault, address user, method f){
    env e; calldataarg args;

    require(e.msg.sender != 0);
    require(epoch <= currentEpoch());
    requireInvariant sequentialEpoch(e, epoch);

    require(userShareSum(epoch, vault) == getTotalSupply(epoch, vault));
    f(e, args);
    assert(userShareSum(epoch, vault) == getTotalSupply(epoch, vault));
}



// **** Points rules **** 
// Similar to shares, please see the comment above
ghost userPoints(uint256, address, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address user. forall address vault.
    userPoints(epoch, vault, user) == 0;
}

ghost userPointsSum(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault.
    userPointsSum(epoch, vault) == 0;
}

hook Sstore points[KEY uint256 epoch][KEY address vault][KEY address user] uint256 value (uint256 old_value) STORAGE {
    havoc userPointsSum assuming userPointsSum@new(epoch, vault) == userPointsSum@old(epoch, vault) + value - old_value;
    havoc userPoints assuming userPoints@new(epoch, vault, user) == userPoints@old(epoch, vault, user);
}

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



// **** Accrual timestamp rules **** 
// // last Accrue times
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
rule lastVaultAccrueAfterCurentEpochStartTimestamp(uint256 epoch, address vault,  method f) filtered {f -> !f.isView}{
    env e; 
    require(validTimestamp(e));
    uint256 before = timeLastAccrueVault(epoch, vault);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueVault(epoch, vault);
    assert ((before == after) || getEpochsStartTimestamp(currentEpoch()) < after);
}

rule lastUserAccrueAfterCurentgetEpochsStartTimestamp(uint256 epoch, address vault, address user,  method f) filtered {f -> !f.isView}{
    env e; 
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
    require(validTimestamp(e));
    uint256 before = timeLastAccrueVault(epoch, vault);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueVault(epoch, vault);
    assert(before <= after, "lastAccruedTimestamp decreased");
}

rule nonDecreasingLastUserAccrueTimestamp(uint256 epoch, address vault, address user, method f) filtered {f -> !f.isView}{
    env e;
    require(validTimestamp(e));
    uint256 before = timeLastAccrueUser(epoch, vault, user);
    calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueUser(epoch, vault, user);
    assert(before <= after, "lastAccrueUserTimestamp decreased");
}
