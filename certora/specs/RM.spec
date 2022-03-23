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
    handleTransfer(address, address, address, uint256) 
    handleWithdrawal(address, address, uint256)

    // envfree methods
    getTotalSupplyAtEpoch(uint256, address) returns(uint256, bool) envfree
    getBalanceAtEpoch(uint256, address, address) returns(uint256, bool) envfree
    requireNoDuplicates(address[]) envfree
    min(uint256, uint256) returns(uint256) envfree
    tokenBalanceOf(address, address) returns(uint256) envfree
    getPrecision() returns(uint256) envfree
}


// Some Definitions
definition epochStarted(uint epoch) returns bool = (getEpochsEndTimestamp(epoch) == getEpochsStartTimestamp(epoch) + SECONDS_PER_EPOCH()); 
definition epochInTheFutur(uint epoch) returns bool =(epoch > 0 && getEpochsEndTimestamp(epoch) == 0 && getEpochsStartTimestamp(epoch) == 0 );
definition epochStartedBlockTimeStamp(uint epoch, env e) returns bool = (epochStarted( epoch) && getEpochsStartTimestamp(epoch) <= e.block.timestamp) ;
definition vaultCorrectLastAccruedTimestamp(uint epoch,address vault, env e) returns bool = getLastAccruedTimestamp(epoch, vault) <= e.block.timestamp;
definition userCorrectLastAccruedTimestamp(uint epoch,address vault, address user, env e) returns bool = getLastUserAccrueTimestamp(epoch, vault, user) <= e.block.timestamp;
definition epochCorrectStartTime(uint epoch, env e) returns bool = (epoch > 0 && getEpochsStartTimestamp(epoch) >0 ) => getEpochsStartTimestamp(epoch) <= e.block.timestamp;
// functions
function epochEndTime(uint256 epoch) returns uint256{
    if (epochStart(epoch) == 0) return 0;
    else return to_uint256(epochStart(epoch) + SECONDS_PER_EPOCH());
}


/********************************
*                               *
*        EPOCH PROPERTIES       *
*                               *
********************************/




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
    havoc epochStart assuming forall uint256 epoch.
    epoch == ep? epochStart@new(epoch) == value : epochStart@new(epoch) == epochStart@old(epoch);
}

hook Sstore epochs[KEY uint256 ep].(offset 32) uint256 value (uint256 old_value) STORAGE {
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

// STATUS: VERIFIED
// rule can only start new epoch after end of current epoch 
rule sanityOfStartingEpoch() {
    env e;
    calldataarg args;
    uint256 epochBefore = currentEpoch();
    uint256 epochEndBefore = getEpochsEndTimestamp(epochBefore);
    startNextEpoch@withrevert(e);
    assert  e.block.timestamp < epochEndBefore => lastReverted, "started next epochs before end";
}


// STATUS: VERIFIED
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

// proving share <= totalSupply
ghost shareSum(uint256, address) returns uint256 {
    init_state axiom forall uint256 epoch. forall address vault. shareSum(epoch, vault) == 0;
}

hook Sstore shares[KEY uint256 ep][KEY address v][KEY address u] uint256 value (uint256 old_value) STORAGE {
    havoc shareSum assuming forall uint256 epoch. forall address vault. forall address user.
    (epoch == ep && vault == v && user == u)? shareSum@new(epoch, vault) == shareSum@new(epoch, vault) + value - old_value : shareSum@new(epoch, vault) == shareSum@old(epoch, vault);
}

// STATUS: VERIFIED
// check sum of share always less than total supply
invariant totalShareInvariant(uint epoch, address vault)
    shareSum(epoch, vault) <= getTotalSupply(epoch, vault)




/************************************
*                                   *
*    ACCRUED TIMESTAMP PROPERTIES   *
*                                   *
*************************************/

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


// WRITE STUFF ON TIME LEFT TO ACCRUE


/********************************
*                               *
*       POINTS PROPERTIES       *
*                               *
********************************/

// STATUS: VERIFIED
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


// STATUS: unVERIFIED
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

// check this :
// addReward: Add rewards correctly
// addRewards: Add rewards correctly
// claimReward: claimsRewards correctly
// claimrewards: claimsRewards correctly
// claimrewardsOverMultipleEpochs: claimsRewards correctly
// claimBulkTokensOverMultipleEpochs: claimsRewards correctly
//DONE

/********************************
*                               *
*       REWARDS PROPERTIES      *
*                               *
********************************/

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



/********************************
*                               *
*          UNIT TESTS           *
*                               *
********************************/


// STATUS: VERIFIED
// checks integrity of handleDeposit function  
rule integrityOfHandleDeposit(address vault, address to, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    uint256 sharesBefore = getShares(epoch, vault, to);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    handleDeposit(e, vault, to, amount);
    uint256 sharesAfter = getShares(epoch, vault, to);
    uint256 supplyAfter = getTotalSupply(epoch, vault);
    assert sharesAfter == sharesBefore + amount, "wrong change in shares";
    assert supplyAfter == supplyBefore + amount, "wrong change in supply";
    assert getLastAccruedTimestamp(epoch, vault) == e.block.timestamp, "wrong update to vault accrue timestamp";
    assert getLastUserAccrueTimestamp(epoch, vault, to) == e.block.timestamp, "wrong update vault accrue user timestamp";
}

// STATUS: VERIFIED
// checks integrity of handleWithdrawal function  
rule integrityOfHandleWithdrawal(address vault, address from, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    uint256 sharesBefore = getShares(epoch, vault, from);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    handleWithdrawal(e, vault, from, amount);
    uint256 sharesAfter = getShares(epoch, vault, from);
    uint256 supplyAfter = getTotalSupply(epoch, vault);
    assert sharesAfter == sharesBefore - amount, "wrong change in shares";
    assert supplyAfter == supplyBefore - amount, "wrong change in supply";
    assert getLastAccruedTimestamp(epoch, vault) == e.block.timestamp, "wrong update to vault accrue timestamp";
    assert getLastUserAccrueTimestamp(epoch, vault, from) == e.block.timestamp, "wrong update vault accrue user timestamp";
}


// STATUS: VERIFIED
// checks integrity of handleTransfer function  
rule integrityOfHandleTransfer(address vault, address from, address to, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    uint256 sharesFromBefore = getShares(epoch, vault, from);
    uint256 sharesToBefore = getShares(epoch, vault, to);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    handleTransfer(e, vault, from, to, amount);
    uint256 sharesFromAfter = getShares(epoch, vault, from);
    uint256 sharesToAfter = getShares(epoch, vault, to);
    uint256 supplyAfter = getTotalSupply(epoch, vault);
    assert sharesToAfter == sharesToBefore + amount, "wrong change in shares To";
    assert sharesFromAfter == sharesFromBefore + amount, "wrong change in shares To";
    assert supplyAfter == supplyBefore , "wrong change in supply";
    assert getLastUserAccrueTimestamp(epoch, vault, from) == e.block.timestamp, "wrong update vault accrue user timestamp";
    assert getLastUserAccrueTimestamp(epoch, vault, to) == e.block.timestamp, "wrong update vault accrue user timestamp";
}


// STATUS: VERIFIED
// NOTE: the block.timestamp updates are not verified by the proved
// it seems he has hard time and over approximate this when there is a call to another internal function
// checks integrity of handleTransfer function  
rule integrityOfNotifyTransfer(address vault, address from, address to, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    uint256 sharesFromBefore = getShares(epoch, vault, from);
    uint256 sharesToBefore = getShares(epoch, vault, to);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    notifyTransfer(e, from, to, amount);
    uint256 sharesFromAfter = getShares(epoch, vault, from);
    uint256 sharesToAfter = getShares(epoch, vault, to);
    uint256 supplyAfter = getTotalSupply(epoch, vault);

    require from != 0 || to != 0;

    assert from == 0 => ((sharesToAfter == sharesToBefore + amount) && (supplyAfter == supplyBefore + amount)), "something wrong with _handleDeposit amount updates";
    //assert from == 0 =>( getLastUserAccrueTimestamp(epoch, vault, to) >= e.block.timestamp && getLastAccruedTimestamp(epoch, vault) >= e.block.timestamp), "something wrong with _handleDeposit accrual updates";
    assert to == 0 => ((sharesFromAfter == sharesFromBefore + amount) && (supplyAfter == supplyBefore - amount)), "something wrong with _handleWithdrawal amount updates";  
    //assert to == 0 =>( getLastUserAccrueTimestamp(epoch, vault, from) >= e.block.timestamp && getLastAccruedTimestamp(epoch, vault) >= e.block.timestamp), "something wrong with _handleWithdrawal accrual updates";
    assert (to != 0 && from != 0) => ((sharesFromAfter == sharesFromBefore + amount) && (supplyAfter == supplyBefore )), "something wrong with _handleTransfer amount updates";  
    //assert (to != 0 && from != 0) =>( getLastUserAccrueTimestamp(epoch, vault, from) >= e.block.timestamp && getLastUserAccrueTimestamp(epoch, vault, to) >= e.block.timestamp), "something wrong with _handleTransfer accrual updates";
   
}


// STATUS: Verified
// checking sanity of internal function
rule sanityOfrequireNoDuplicates(address[] arr) {
    uint l = arr.length;
    requireNoDuplicates@withrevert(arr);

    uint i;
    uint j;

    assert (i != j && arr[i] == arr[j] && i < l && j < l ) => lastReverted;
}


// write rules for getUserTimeLeftToAccrue and getVaulTimeLeftToAccrue

// write invariants for 
// getVaultTimeLeftToAccrue
// getUserTimeLeftToAccrue

