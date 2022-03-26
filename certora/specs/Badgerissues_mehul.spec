// Rules for badgerDao Care
import "Badger_mehul_1.spec"

// Accrue time rules : If updated, it should point to current time
rule lastVaultAccrueAfterCurentgetEpochsStartTimestamp(uint256 epoch, address vault,  method f){
    uint256 before = timeLastAccrueVault(epoch, vault);
    env e; calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueVault(epoch, vault);
    assert ((before == after) || getEpochsStartTimestamp(currentEpoch()) < after);
}

rule lastUserAccrueAfterCurentgetEpochsStartTimestamp(uint256 epoch, address vault, address user,  method f){
    uint256 before = timeLastAccrueUser(epoch, vault, user);
    env e; calldataarg args;
    f(e, args);
    uint256 after = timeLastAccrueUser(epoch, vault, user);
    assert ((before == after) || getEpochsStartTimestamp(currentEpoch()) < after);
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

// Vault accrue
rule unaccruedVaultUpdateValueMatches(uint256 epoch, address vault){
    env e;
    //requireInvariant epochOver(epoch, e);
    //requireInvariant epochNotStarted(epoch, e);
    //requireInvariant epochSequential(epoch);
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

// Points
// ghost userPoints(uint256, address, address) returns uint256 {
//     init_state axiom forall uint256 epoch. forall address user. forall address vault.
//     userPoints(epoch, vault, user) == 0;
// }

// hook Sstore totalPoints[KEY uint256 epoch][KEY address vault] uint256 value (uint256 old_value) STORAGE {
//     havoc vaultPoints assuming vaultPoints@new(epoch, vault) = value;
// }

// // Ghost to calculate sum of user balance at any epoch
// ghost vaultPoints(uint256, address) returns uint256 {
//     init_state axiom forall uint256 epoch. forall address vault.
//     tvaultPoints(epoch, vault) == 0;
// }

// hook Sstore totalPoints[KEY uint256 epoch][KEY address vault] uint256 value (uint256 old_value) STORAGE {
//     havoc vaultPoints assuming vaultPoints@new(epoch, vault) = value;
// }

// Sum of user balances should equal total supply - IMPORTANT
// Fails during notifyTransfer (0x0, 0x0, amount) - increases shares without any change to balances
rule sumOfUserBalancesShouldMatchTotalSupply(uint256 epoch, address vault, address user, method f){
    require(epoch <= currentEpoch());
    //requireInvariant epochSequential(epoch);
    require(userShareSum(epoch, vault) == getTotalSupply(epoch, vault));
    env e; calldataarg args;
    require(e.msg.sender != 0);
    f(e, args);
    assert(userShareSum(epoch, vault) == getTotalSupply(epoch, vault));
}


// Is the order of acrue functions important?
// acrueVault is always called after acrueUser
// Does accrual before calling any function produce the same result?
//rule vaultAccrueBeforeCallChangesOutput()


// Rewards to any particular user should match calculation
// Add reward, call claimReward
// Checking for loop functions with two tokens should be sufficient

definition functionNotAddReward(method f) returns bool =
       f.selector != addReward(uint256, address, address, uint256).selector
       && f.selector != addRewards(uint256[], address[], address[], uint256[]).selector
       ;

definition functionNotClaimReward(method f) returns bool =
       f.selector != claimRewards(uint256[], address[], address[], address[]).selector
       && f.selector != claimReward(uint256, address, address, address).selector
       ;

rule rewardsMatchCalculation(
        address user1, 
        address user2, 
        address vault, 
        uint256 epoch, 
        address token, 
        uint256 amount,
        method f1,
        method f2)
   filtered {f1 -> !f1.isView, f2-> !f2.isView } {
    require(functionNotAddReward(f1));
    require(functionNotClaimReward(f2));

    env e1; env e2; env e3;
    calldataarg args;
    calldataarg args2;

    require(e2.msg.sender == user2);
    require(user1 != user2);

    addReward(e1, epoch, vault, token, amount);
    uint256 firstRewards = getRewards(epoch, vault, token);
    uint256 balanceBefore = tokenBalanceOf(token, user1);
    f1(e2, args);
    uint256 userRewards = getEligibleRewards(epoch, vault, token, user1);
    f2(e3, args2);
    claimReward(e3, epoch, vault, token, user1);
    uint256 balanceAfter = tokenBalanceOf(token, user1); 

    assert(
        firstRewards == amount // Rewards added correctly
        && (balanceAfter - balanceBefore == userRewards) // user balance is correct
    );
}