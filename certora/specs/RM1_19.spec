import "erc20.spec"
import "RMBase.spec"

// Some Definitions
definition epochStarted(uint epoch) returns bool = (getEpochsEndTimestamp(epoch) == getEpochsStartTimestamp(epoch) + SECONDS_PER_EPOCH()); 
definition epochInTheFutur(uint epoch) returns bool =(epoch > 0 && getEpochsEndTimestamp(epoch) == 0 && getEpochsStartTimestamp(epoch) == 0 );
definition epochStartedBlockTimeStamp(uint epoch, env e) returns bool = (epochStarted( epoch) && getEpochsStartTimestamp(epoch) <= e.block.timestamp) ;
definition vaultCorrectLastAccruedTimestamp(uint epoch,address vault, env e) returns bool = getLastAccruedTimestamp(epoch, vault) <= e.block.timestamp;
definition userCorrectLastAccruedTimestamp(uint epoch,address vault, address user, env e) returns bool = getLastUserAccrueTimestamp(epoch, vault, user) <= e.block.timestamp;
definition epochCorrectStartTime(uint epoch, env e) returns bool = (epoch > 0 && getEpochsStartTimestamp(epoch) >0 ) => getEpochsStartTimestamp(epoch) <= e.block.timestamp;


/********************************
*                               *
*        EPOCH PROPERTIES       *
*                               *
********************************/


// STATUS: VERIFIED
// PROPERTY #2
// rule can only start new epoch after end of current epoch 
rule sanityOfStartingEpoch() {
    env e;
    calldataarg args;
    uint256 epochBefore = currentEpoch();
    uint256 epochEndBefore = getEpochsEndTimestamp(epochBefore);
    startNextEpoch@withrevert(e);
    assert  e.block.timestamp < epochEndBefore => lastReverted, "started next epochs before end";
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
    havoc epochStart assuming forall uint256 epoch.
    epoch == ep? epochStart@new(epoch) == value : epochStart@new(epoch) == epochStart@old(epoch);
}
hook Sstore epochs[KEY uint256 ep].(offset 32) uint256 value (uint256 old_value) STORAGE {
    havoc epochEnd assuming forall uint256 epoch.
    epoch == ep? epochEnd@new(epoch) == value : epochEnd@new(epoch) == epochEnd@old(epoch);
}

// STATUS: VERIFIED
// PROPERTY 1
// invariant for epochId : futur epochs are non intialized
invariant futurEpochsNonInitialized(uint256 epoch)
    epoch > currentEpoch() => (epochStart(epoch) == 0 && epochEnd(epoch) == 0)

// STATUS: VERIFIED
// PROPERTY 3
// invariant for epochId : past epochs are initialized correctly
invariant epochStartAndEndTime(uint256 epoch) 
    (epoch <= currentEpoch() &&  currentEpoch() > 0 && epoch > 0 ) => (epochEnd(epoch) == epochStart(epoch) + SECONDS_PER_EPOCH() )


// STATUS: VERIFIED
// PROPERTY 20
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


// STATUS: VERIFIED
// PROPERTY 3
// Epoch end and start time are correct after starting new epoch
// epoch start time is correct too
rule sanityOfNewEpochMath() {
    env e;
    calldataarg args;
    startNextEpoch(e);
    uint256 epoch = currentEpoch();
    uint256 epochStartTime = getEpochsStartTimestamp(epoch);
    uint256 epochEndTime = getEpochsEndTimestamp(epoch);
    assert  epochEndTime == epochStartTime + SECONDS_PER_EPOCH(), "Epoch math wrong";
    assert epochStartTime == e.block.timestamp, "wrong start time";
}

// STATUS: VERIFIED
// PROPERTY 7
// Epoch end and start time doesnt change illegaly
rule preservationOfEpochData(uint epoch, method f) {
    env e;
    calldataarg args;
    uint256 epochStartTimeBefore = getEpochsStartTimestamp(epoch);
    uint256 epochEndTimeBefore = getEpochsEndTimestamp(epoch);
    f(e, args);
    uint256 currentEp = currentEpoch();
    uint256 epochStartTimeAfter = getEpochsStartTimestamp(epoch);
    uint256 epochEndTimeAfter = getEpochsEndTimestamp(epoch);

    assert epoch != currentEp => (epochStartTimeBefore==epochStartTimeAfter) && (epochEndTimeBefore==epochEndTimeAfter), "wrong epoch data update";
    
}

/********************************
*                               *
* SHARES/TOTALSUPPLY PROPERTIES *
*                               *
********************************/

// proving sum share <= totalSupply
ghost shareSum(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault. shareSum(epoch, vault) == 0;
}

hook Sstore shares[KEY uint256 ep][KEY address v][KEY address u] uint256 value (uint256 old_value) STORAGE {
    havoc shareSum assuming forall uint256 epoch. forall address vault. forall address user.
    (epoch == ep && vault == v && user == u)? shareSum@new(epoch, vault) == shareSum@new(epoch, vault) + value - old_value : shareSum@new(epoch, vault) == shareSum@old(epoch, vault);
}

// proving ghost tracking totalSupply
ghost totalSup(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault. totalSup(epoch, vault) == 0;
}

hook Sstore totalSupply[KEY uint256 ep][KEY address v] uint256 value (uint256 old_value) STORAGE {
    havoc totalSup assuming forall uint256 epoch. forall address vault. 
    (epoch == ep && vault == v )? totalSup@new(epoch, vault) == value : totalSup@new(epoch, vault) == totalSup@old(epoch, vault);
}
// STATUS: VERIFIED
// check equality of ghost and mapping
invariant checkTotalSupEquality(uint256 epoch, address vault)
    getTotalSupply(epoch, vault) == totalSup(epoch, vault)

// STATUS: unVERIFIED
// check sum of shares always less than total supply
// have to check getters of accrueVault !
invariant totalShareInvariant(uint epoch, address vault)
    shareSum(epoch, vault) <= totalSup(epoch, vault)

// STATUS: VERIFIED
// check futur shares non init
invariant futurSharesNonInitialized(uint epoch, address vault)
    epoch > currentEpoch() => getTotalSupply(epoch, vault) == 0



/********************************
*                               *
*       POINTS PROPERTIES       *
*                               *
********************************/



// proving sum points <= totalPoints
ghost pointsSum(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault. pointsSum(epoch, vault) == 0;
}

hook Sstore points[KEY uint256 ep][KEY address v][KEY address u] uint256 value (uint256 old_value) STORAGE {
    havoc pointsSum assuming forall uint256 epoch. forall address vault. forall address user.
    (epoch == ep && vault == v && user == u)? pointsSum@new(epoch, vault) == pointsSum@new(epoch, vault) + value - old_value : pointsSum@new(epoch, vault) == pointsSum@old(epoch, vault);
}

// STATUS: VERIFIED
// PROPERTY 8
// Verified with loop iter 1 have to check for 2 = Have to test claimBulkTokens
// check sum of share always less than total supply
invariant totalPointsInvariant(uint epoch, address vault)
    pointsSum(epoch, vault) <= getTotalPoints(epoch, vault)


// STATUS: VERIFIED
// PROPERTY 11
// check rule that pointsWithdrawn always less than points
// will have to do another check for claimBulkTokensOverMultipleEpochsOptimized
rule pointsWithdrawnUpperBound(uint epoch, address vault, address user, address token, method f) 
filtered {
	f -> f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector
} {
    env e;
    calldataarg args;
    uint256 pointsBefore = getPoints(epoch, vault, user);
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epoch, vault, user, token);
    f(e, args);
    uint256 pointsAfter = getPoints(epoch, vault, user);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epoch, vault, user, token);

    assert pointsWithdrawnBefore <= pointsBefore  => pointsWithdrawnAfter <= pointsAfter, "Wrong math of points withdrawn";
}


// STATUS: unVERIFIED
// PROPERTY 9
// check rule that points are usually non decreasing
rule pointsNonDecreasing(uint epoch, address vault, address user, address token, method f) 
filtered {
	f -> f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector
} {
    env e;
    calldataarg args;
    uint256 pointsBefore = getPoints(epoch, vault, user);
    f(e, args);
    uint256 pointsAfter = getPoints(epoch, vault, user);

    assert pointsAfter >= pointsBefore, "points shouldnt decrease";
}


// STATUS: VERIFIED
// PROPERTY 12/9
// check rule that pointsWithdrawn are non decreasing
rule pointsWithdrawnNonDecreasing(uint epoch, address vault, address user, address token, method f) 
 {
    env e;
    calldataarg args;
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epoch, vault, user, token);
    f(e, args);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epoch, vault, user, token);

    assert pointsWithdrawnAfter >= pointsWithdrawnBefore, "pointsWithdrawn shouldnt decrease";
}


/************************************
*                                   *
*    ACCRUED TIMESTAMP PROPERTIES   *
*                                   *
*************************************/

// Need to write invariant on timeLeftToAccrueForUser and timeLeftToAccrueVault



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
// PROPERY 13
// check lastAccruedTimestamp is only increasing
rule increasingLastAccruedTimestamp(uint256 epoch, address vault, method f){
    env e;
    calldataarg args;
    require vaultCorrectLastAccruedTimestamp(epoch, vault,e);
    uint256 lastUserAccrueTimestampBefore = getLastAccruedTimestamp(epoch, vault);
    f(e, args);
    uint256 lastUserAccrueTimestampAfter = getLastAccruedTimestamp(epoch, vault);
    assert lastUserAccrueTimestampAfter >= lastUserAccrueTimestampBefore, "lastUserAccrueTimestamp decreased";
}

// STATUS: VERIFIED
// check that if lastAccruedTimestamp > 0 then it is > epochId.startTime
invariant lastAccruedTimestampLowerBound(uint256 epoch, address vault)
    (getLastAccruedTimestamp(epoch, vault) > 0 && epoch > 0) => getLastAccruedTimestamp(epoch, vault) >= getEpochsStartTimestamp(epoch)
    {
        preserved with (env e) {
            require vaultCorrectLastAccruedTimestamp(epoch, vault, e) && epochCorrectStartTime(epoch, e);//getEpochsStartTimestamp(epoch) <= e.block.timestamp;
            require epoch > currentEpoch() => getLastAccruedTimestamp(epoch, vault) == 0;
        }
    }

// STATUS: VERIFIED
// PROPERY 14
// checks lastUserAccruedTimestamp is increasing
rule increasingLastUserAccrueTimestamp(uint256 epoch, address vault, address user, method f){
    env e;
    calldataarg args;
    require userCorrectLastAccruedTimestamp(epoch, vault, user, e);
    uint256 lastUserAccrueTimestampBefore = getLastUserAccrueTimestamp(epoch, vault, user);
    f(e, args);
    uint256 lastUserAccrueTimestampAfter = getLastUserAccrueTimestamp(epoch, vault, user);
    assert lastUserAccrueTimestampAfter >= lastUserAccrueTimestampBefore, "lastUserAccrueTimestamp decreased";

}

// STATUS: VERIFIED
// PROPERTY 15
// checks lastUserAccruedTimestamp is block.timestap after call to accrueVault
rule correctLastVaultAccruedTimestamp(uint256 epoch, address vault){
    env e;
    accrueVault(e, epoch, vault);
    assert getLastAccruedTimestamp(epoch, vault) == e.block.timestamp, "wrong update";
   
}

// STATUS: VERIFIED
// checks accrueVault cant be called for futur epochs
rule correctAccrueVaultRevert(uint256 epoch, address vault){
    env e;
    accrueVault@withrevert(e, epoch, vault);
    assert lastReverted <=> epoch > currentEpoch(), "accrueVault should revert";
}

// STATUS: VERIFIED 
// Other one passed we will assume this pass
// check that if lastUserAccruedTimestamp > 0 then it is > epochId.startTimeinvariant 
invariant lastUserAccruedTimestampLowerBound(uint256 epoch, address vault, address user)
    (getLastUserAccrueTimestamp(epoch, vault, user) > 0 && epoch > 0) => getLastUserAccrueTimestamp(epoch, vault, user) >= getEpochsStartTimestamp(epoch)
    {
        preserved with (env e) {
            require userCorrectLastAccruedTimestamp(epoch, vault, user, e) && epochCorrectStartTime(epoch, e);
            require epoch > currentEpoch() => getLastUserAccrueTimestamp(epoch, vault, user) == 0;
        }
    }

// STATUS: VERIFIED
// PROPERTY 16
// checks lastUserAccruedTimestamp is block.timestap after call to accrueVault
rule correctLastUserAccruedTimestamp(uint256 epoch, address vault, address user){
    env e;
    accrueUser(e, epoch, vault, user);
    assert getLastUserAccrueTimestamp(epoch, vault, user) == e.block.timestamp, "wrong update";
   
}

// STATUS:VERIFIED
// checks accrueUser cant be called for futur epochs
rule correctAccrueUserRevert(uint256 epoch, address vault, address user){
    env e;
    uint currentEp = currentEpoch();
    accrueUser@withrevert(e, epoch, vault, user);

    assert epoch > currentEp => lastReverted, "accrueUser should revert";
}


/********************************
*                               *
*       REWARDS PROPERTIES      *
*                               *
********************************/

// STATUS - VERIFIED
// PROPERTY 18
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
// PROPERTY 19
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
// checks addRewards function correctly 
rule sanityOfAddReward(uint256 epoch, address vault, address token, uint256 amount){
    env e;
    uint256 rewardsBefore = getRewards(epoch, vault, token);
    uint256 balanceBefore = tokenBalanceOf(token, currentContract);
    addReward(e, epoch, vault, token, amount);
    uint256 rewardsAfter = getRewards(epoch, vault, token);
    uint256 balanceAfter = tokenBalanceOf(token, currentContract);
    assert rewardsAfter + balanceBefore == rewardsBefore + balanceAfter, "addReward malfunction";
    assert e.msg.sender != currentContract => rewardsAfter == rewardsBefore + amount, "addReward malfunction";

}

// STATUS: VERIFIED
// checks addReward cant be called for past epochs
rule correctAddRewardRevert(uint256 epoch, address vault, address token, address user){
    env e;
    uint currentEp = currentEpoch();
    addReward@withrevert(e, epoch, vault,token, user);
    assert epoch < currentEp => lastReverted, "addReward should revert";
}

// STATUS: FAILS
// token and vault args are swapped in addRewards function !
// STATUS FIX CONTRACT:  VERIFIED
rule sanityOfAddRewards(uint256[] epochs, address[] vaults, address[] tokens, uint256[] amounts){
    env e;

    require epochs.length == vaults.length && epochs.length == tokens.length && epochs.length == amounts.length;
    uint256 epoch = epochs[0];
    address vault = vaults[0];
    address token = tokens[0]; 
    uint256 amount = amounts[0];
    uint256 rewardsBefore = getRewards(epoch, vault, token); 
    uint256 balanceBefore = tokenBalanceOf(token, currentContract); 
    addRewards(e, epochs, vaults, tokens, amounts); 
    uint256 rewardsAfter = getRewards(epoch, vault, token);
    uint256 balanceAfter = tokenBalanceOf(token, currentContract);
    assert rewardsAfter + balanceBefore == rewardsBefore + balanceAfter, "addRewards malfunction";
    assert e.msg.sender != currentContract => rewardsAfter == rewardsBefore + amount, "addRewards malfunction";

}


// STATUS: VERIFIED
// Checks points withdrawn increase
rule sanityOfClaimReward(uint256 epoch, address vault, address token, address user){
    env e;

    uint256 userPointsWithdrawnBefore = getPointsWithdrawn(epoch, vault, user, token);   
    claimReward(e, epoch, vault, token, user);
    uint256 userPointsWithdrawnAfter = getPointsWithdrawn(epoch, vault, user, token);
    assert userPointsWithdrawnAfter >= userPointsWithdrawnBefore , "wrong change in points withdrawn";
   
}

// STATUS: VERIFIED
// checks claimReward cant be called for futur epochs
rule correctClaimRewardRevert(uint256 epoch, address vault, address token, address user){
    env e;
    uint currentEp = currentEpoch();
    claimReward@withrevert(e, epoch, vault, token, user);
    assert epoch >= currentEp => lastReverted, "claimReward should revert";
   
}


// STATUS: VERIFIED
// Checks math after calling claim reward is ok
rule sanityOfClaimRewards(uint256[] epochs, address[] vaults, address[] tokens, address[] users){
    env e;

    uint epoch = epochs[0];
    address vault = vaults[0];
    address token = tokens[0];
    address user = users[0];

    uint256 userPointsWithdrawnBefore = getPointsWithdrawn(epoch, vault, user, token);
    claimRewards(e, epochs, vaults, tokens, users);
    uint256 userPointsWithdrawnAfter = getPointsWithdrawn(epoch, vault, user, token);

    assert userPointsWithdrawnAfter >= userPointsWithdrawnBefore , "wrong change in points withdrawn";
}


// STATUS: VERIFIED
// checks claimBulkTokensOverMultipleEpochs cant be called for futur epochs
rule claimBulkTokensOverMultipleEpochs(uint256 epochS, uint256 epochE, address vault, address[] tokens, address user){
    env e;
    uint currentEp = currentEpoch();
    claimBulkTokensOverMultipleEpochs@withrevert(e, epochS, epochE, vault, tokens, user);
    assert epochE >= currentEp => lastReverted, "claimBulkTokensOverMultipleEpochs should revert";
   
}

// STATUS: VERIFIED
// checks claimBulkTokensOverMultipleEpochsOptimized cant be called for futur epochs
rule correctClaimBulkTokensOptimizedRevert(uint256 epochS, uint256 epochE, address vault, address[] tokens){
    env e;
    uint currentEp = currentEpoch();
    claimBulkTokensOverMultipleEpochsOptimized@withrevert(e, epochS, epochE, vault, tokens);
    assert epochE >= currentEp => lastReverted, "claimRewardOptimized should revert";
   
}
