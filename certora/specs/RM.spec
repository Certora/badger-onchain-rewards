import "erc20.spec"

methods {
    // constants
    SECONDS_PER_EPOCH() returns(uint256) envfree

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
    getShares(uint256, address, address) returns(uint256) envfree
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

definition epochStarted(uint epoch) returns bool = (getEpochsEndTimestamp(epoch) == getEpochsStartTimestamp(epoch) + SECONDS_PER_EPOCH()); 
definition epochInTheFutur(uint epoch) returns bool =(epoch > 0 && getEpochsEndTimestamp(epoch) == 0 && getEpochsStartTimestamp(epoch) == 0 );
definition epochStartedBlockTimeStamp(uint epoch, env e) returns bool = (epochStarted( epoch) && getEpochsStartTimestamp(epoch) <= e.block.timestamp) ;
definition vaultCorrectLastAccruedTimestamp(uint epoch,address vault, env e) returns bool = getLastAccruedTimestamp(epoch, vault) <= e.block.timestamp;
definition userCorrectLastAccruedTimestamp(uint epoch,address vault, address user, env e) returns bool = getLastUserAccrueTimestamp(epoch, vault, user) <= e.block.timestamp;

// functions
function epochEndTime(uint256 epoch) returns uint256{
    if (epochStart(epoch) == 0) return 0;
    else return to_uint256(epochStart(epoch) + SECONDS_PER_EPOCH());
}

// STATUS - VERIFIED
// checks that rewards are non-decreasing
rule increasingRewards(uint256 epochs, address vault, address token, method f) {
    env e;
    calldataarg args;
    uint256 rewardsBefore = getRewards(epochs, vault, token);
    f(e, args);
    uint256 rewardsAfter = getRewards(epochs, vault, token);
    assert rewardsAfter >= rewardsBefore, "Rewards decreased";
}


// STATUS - VERIFIED
// checks that rewards are only changed by allowed functions
rule rewardsAllowedFunctions(uint256 epochs, address vault, address token, method f) {
    env e;
    calldataarg args;
    uint256 rewardsBefore = getRewards(epochs, vault, token);
    f(e, args);
    uint256 rewardsAfter = getRewards(epochs, vault, token);
    bool isAddReward = (f.selector == addReward(uint256,address,address,uint256).selector); 
    bool isAddRewards = (f.selector == addRewards(uint256[],address[],address[],uint256[]).selector);
    assert (rewardsAfter != rewardsBefore) =>  (isAddReward || isAddRewards), "Rewards changed by non allowed function";
}


// STATUS: VERIFIED
// If epoch in the futur then lastUserAccrueTimestamp should be zero
invariant futurLastUserAccrueTimestampIsZero(uint256 epoch, address vault, address user)
    epoch > to_uint256(currentEpoch()) => getLastUserAccrueTimestamp(epoch, vault, user) == 0

// STATUS: VERIFIED
// rule to check vacuity of invariant
rule checkFuturLastUserAccrueTimestampIsZeroInvariant(uint256 epoch, address vault, address user){
    assert epoch > currentEpoch() => getLastUserAccrueTimestamp(epoch, vault, user) == 0;
    assert false;
}

// Ghost for initialization of epochs
// Ghost variable to keep track of starting/ending times of each epoch
ghost epochStart(uint256) returns uint256 {
    init_state axiom forall uint256 epoch. epochStart(epoch) == 0;
}

ghost epochEnd(uint256) returns uint256 {
    init_state axiom forall uint256 epoch. epochEnd(epoch) == 0;
}


hook Sstore epochs[KEY uint256 ep].(offset 0) uint256 value (uint256 old_value) STORAGE {
    // Note that currentEpoch is updated before epochs(currentEpoch has a value)
    // Need to find workaraound to struct maps
    havoc epochStart assuming forall uint256 epoch.
    epoch == ep? epochStart@new(epoch) == value : epochStart@new(epoch) == epochStart@old(epoch);
}

hook Sstore epochs[KEY uint256 ep].(offset 32) uint256 value (uint256 old_value) STORAGE {
    // Note that currentEpoch is updated before epochs(currentEpoch has a value)
    // Need to find workaraound to struct maps
    havoc epochEnd assuming forall uint256 epoch.
    epoch == ep? epochEnd@new(epoch) == value : epochEnd@new(epoch) == epochEnd@old(epoch);
}

// STATUS: VERIFIED
// invariant for epochId : futur epochs are non intialized
invariant futurEpochsNonInitialized(uint256 epoch)
    epoch > currentEpoch() => (epochStart(epoch) == 0 && epochEnd(epoch) == 0)

// STATUS: VERIFIED
// invariant for epochId : past epochs are initialized correctly
invariant epochStartAndEndTime(uint256 epoch) 
    (epoch <= currentEpoch() &&  currentEpoch() > 0 && epoch > 0 ) => (epochEnd(epoch) == epochStart(epoch) + SECONDS_PER_EPOCH() )



// STATUS: VERIFIED
// epochs are increasing
// and only startEpoch() can increase epochs
rule monotonicityOfEpochs(method f) {
    env e;
    calldataarg args;
    uint256 epochBefore = currentEpoch();
    f(e, args);
    uint256 epochAfter = currentEpoch();
    assert epochAfter == epochBefore || epochAfter == epochBefore + 1, "epochs math wrong";
    assert epochAfter > epochBefore => f.selector == startNextEpoch().selector, "wrong function changed epochId";
}

// Need to write invariant on timeLeftToAccrueForUser and timeLeftToAccrueVault

// first lastAccruedTimestamp
// Ghost for initialization of lastAccruedTimestamp
ghost vaultLastAccruedTimestamp(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault. vaultLastAccruedTimestamp(epoch, vault) == 0;
}

hook Sstore lastAccruedTimestamp[KEY uint256 ep][KEY address v] uint256 value (uint256 old_value) STORAGE {
    // Note that currentEpoch is updated before epochs(currentEpoch has a value)
    // Need to find workaraound to struct maps
    havoc vaultLastAccruedTimestamp assuming forall uint256 epoch. forall address vault.
    (epoch == ep && vault == v )? vaultLastAccruedTimestamp@new(epoch, vault) == value : vaultLastAccruedTimestamp@new(epoch, vault) == vaultLastAccruedTimestamp@old(epoch, vault);
}

// STATUS: VERIFIED
// check equality of ghost and mapping
invariant lastAccruedTimestampEquality(uint epoch, address vault)
    getLastAccruedTimestamp(epoch, vault) == vaultLastAccruedTimestamp(epoch, vault)

// STATUS: VERIFIED
// check vacuity
rule checkLastAccruedTimestampEquality(uint epoch, address vault) {
    require getLastAccruedTimestamp(epoch, vault) == vaultLastAccruedTimestamp(epoch, vault);
    assert false;
}
    
// write some rules about timestamp

// STATUS: VERIFIED
// check lastAccruedTimestamp is only increasing
rule increasingLastAccruedTimestamp(uint256 epoch, address vault, method f){
    env e;
    calldataarg args;
    //requireInvariant lastAccruedTimestampEquality(epoch, vault);
    //require epoch > 0;
    require vaultCorrectLastAccruedTimestamp(epoch, vault,e);
    uint256 lastUserAccrueTimestampBefore = getLastAccruedTimestamp(epoch, vault);
    //require lastUserAccrueTimestampBefore <= e.block.timestamp;
    f(e, args);
    uint256 lastUserAccrueTimestampAfter = getLastAccruedTimestamp(epoch, vault);
    assert lastUserAccrueTimestampAfter >= lastUserAccrueTimestampBefore, "lastUserAccrueTimestamp decreased";
}


rule increasingLastUserAccrueTimestamp(uint256 epoch, address vault, address user, method f){
    env e;
    calldataarg args;
    require userCorrectLastAccruedTimestamp(epoch, vault, user, e);
    uint256 lastUserAccrueTimestampBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    f(e, args);
    uint256 lastUserAccrueTimestampAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    assert lastUserAccrueTimestampAfter >= lastUserAccrueTimestampBefore, "lastUserAccrueTimestamp decreased";

}

// If timeLeftToAccrue is positif then it is greater than epochId start
invariant lastUserAccrueTimestampLowerBound(uint256 epoch, address vault, address user, env e)
    getLastUserAccrueTimestamp(epoch, vault, user) > 0 => getLastUserAccrueTimestamp(epoch, vault, user) >= getEpochsStartTimestamp(epoch)
    {
        preserved {
            require epochStartedBlockTimeStamp(epoch, e) && epoch > 0;
        }
    }


// ghost sum_of_all_points(uint256,address) returns uint256{
//     // for the constructor - assuming that on the constructor the value of the ghost is 0
//     init_state axiom forall uint256 epoch. forall address vault. sum_of_all_points(epoch, vault) == 0;
// }

// hook Sstore points[KEY uint256 epoch][KEY address vault][KEY address user] uint256 new_points
//     (uint256 old_points) STORAGE {

//   havoc sum_of_all_points assuming sum_of_all_points@new(epoch, vault) == sum_of_all_points@old(epoch, vault) + new_points - old_points &&
// 		(forall uint ep. forall address v. (ep != epoch || v != vault ) => sum_of_all_points@new(ep, v) == sum_of_all_points@old(ep, v));
// }


// // totalPoints >= single user points
// invariant totalPoints_GE_single_user_points(uint256 epoch, address vault)
//     forall address user. getTotalPoints(epoch, vault) >= getPoints(epoch, vault, user)


// // totalPoints >= sum all points
// invariant totalPoints_GE_sum_of_all_points(uint256 epoch, address vault)
//     getTotalPoints(epoch, vault) >= sum_of_all_points(epoch, vault)