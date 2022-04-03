import "erc20.spec"

methods {
    // constants
    SECONDS_PER_EPOCH() returns(uint256) envfree
    MAX_BPS() returns(uint256) envfree

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
    handleTransfer(address, address, address, uint256)

    // envfree methods
    getTotalSupplyAtEpoch(uint256, address) returns(uint256, bool) envfree
    getBalanceAtEpoch(uint256, address, address) returns(uint256, bool) envfree
    requireNoDuplicates(address[]) envfree
    min(uint256, uint256) returns(uint256) envfree
    tokenBalanceOf(address, address) returns(uint256) envfree
}

/*
STATUS - VERIFIED

The `currentEpoch` should be the latest epoch with populated startTimestamp and endTimestamp.
*/
invariant emptyEpoch(uint256 epochId)
    epochId > currentEpoch() => getEpochsStartTimestamp(epochId) == 0 && getEpochsEndTimestamp(epochId) == 0

/*
STATUS - VERIFIED

Epochs should be sequential - the startTimestamp of the next epoch should be later than the timestamp of the current epoch.
*/
invariant sequentialEpoch(uint256 epochId)
    epochId + 1 <= currentEpoch() => getEpochsEndTimestamp(epochId) < getEpochsStartTimestamp(epochId + 1)

/*
STATUS - VERIFIED

The time difference between startTimestamp and endTimestamp of any epoch should be equal to SECONDS_PER_EPOCH (one week in current implementation)
*/
invariant epochStartEndEpoch(uint256 epochId)
    epochId > 0 && epochId <= currentEpoch() =>
        getEpochsStartTimestamp(epochId) + SECONDS_PER_EPOCH() == getEpochsEndTimestamp(epochId)

/*
STATUS - VERIFIED

`currentEpoch`:
- can only increase, there should be no way of decreasing its value 
- increases by 1 via `startNextEpoch` function => currentEpochAfter == currentEpochBefore + 1
- cannot change (is constant) via any other function than `startNextEpoch` => currentEpochAfter == currentEpochBefore
*/
rule currentEpochChange(method f) {
    env e;
    calldataarg args;

    uint256 currentEpochBefore = currentEpoch();
    f(e, args);
    uint256 currentEpochAfter = currentEpoch();

    assert currentEpochAfter >= currentEpochBefore, "currentEpoch should only increase";
    assert f.selector == startNextEpoch().selector => currentEpochAfter == currentEpochBefore + 1, "epoch didnt increase";
    assert f.selector != startNextEpoch().selector => currentEpochAfter == currentEpochBefore, "current epoch changed";
}

/*
STATUS - VERIFIED

`currentEpoch` can only be lower or equal to block timestamp.
*/
rule epochStartAndEndTimestampsCannotBeBiggerThanBlockTimestamp(method f, uint256 epochId) {
    env e;
    calldataarg args;

    require epochId <= currentEpoch();
    require getEpochsStartTimestamp(epochId) <= e.block.timestamp;
    require getEpochsEndTimestamp(epochId) <= e.block.timestamp;

    f(e, args);

    assert getEpochsStartTimestamp(epochId) <= e.block.timestamp, "epochStartTimestamp bigger than block timestamp";
    assert getEpochsEndTimestamp(epochId) <= e.block.timestamp, "epochEndTimestamp bigger than block timestamp";
}

/*
STATUS - VERIFIED

`rewards[epochId][vault][token]`:
- should only increase, there should be no way of its value to decrease
- can change only via addReward or addRewards functions
*/
rule rewardsChange(method f, uint256 epochId, address vault, address token) {
    env e;
    calldataarg args;

    uint256 rewardsBefore = getRewards(epochId, vault, token);
    f(e, args);
    uint256 rewardsAfter = getRewards(epochId, vault, token);

    assert rewardsAfter >= rewardsBefore, "rewards should only increase";
    assert f.selector != addReward(uint256,address,address,uint256).selector &&
            f.selector != addRewards(uint256[],address[],address[],uint256[]).selector =>
                rewardsAfter == rewardsBefore, "rewards changed not via addReward nor addRewards functions";
}

/*
STATUS VERIFIED

`totalPoints[epochId][vault]`:
- should only increase, there should be no way of its value to decrease
*/
rule totalPointsCanOnlyIncrease(method f, uint256 epochId, address vault) {
    env e;
    calldataarg args;

    uint256 totalPointsBefore = getTotalPoints(epochId, vault);
    f(e, args);
    uint256 totalPointsAfter = getTotalPoints(epochId, vault);

    assert totalPointsAfter >= totalPointsBefore, "totalPoints should only increase";
}

/*
STATUS - VERIFIED

`points[epochId][vault][user]`:
- can only increase, there should be no way of its value to decrease (exception claimBulkTokensOverMultipleEpochsOptimized)
*/
rule userPointsCanOnlyIncrease(method f, uint256 epochId, address vault, address user) {
    env e;
    calldataarg args;

    require f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256,uint256,address,address[]).selector;

    uint256 pointsBefore = getPoints(epochId, vault, user);
    f(e, args);
    uint256 pointsAfter = getPoints(epochId, vault, user);

    assert pointsAfter >= pointsBefore, "points should only increase";
}

/*
STATUS - VERIFIED

`lastAccruedTimestamp[epochId][vault]`:
- should only increase, there should be no way of its value to decrease
*/
rule lastAccruedTimestampCanOnlyIncrease(method f, uint256 epochId, address vault) {
    env e;
    calldataarg args;

    uint256 lastAccruedTimestampBefore = getLastAccruedTimestamp(epochId, vault);
    require lastAccruedTimestampBefore <= e.block.timestamp;

    f(e, args);
    uint256 lastAccruedTimestampAfter = getLastAccruedTimestamp(epochId, vault);

    assert lastAccruedTimestampAfter >= lastAccruedTimestampBefore, "lastAccruedTimestamp should only increase";
}

/*
STATUS - VERIFIED

`lastAccruedTimestmap[epochId][vault]`:
- value should always be lower or equal to block.timestamp
*/
rule lastAccruedTimestampCannotBeBiggerThanBlockTimestamp(method f, uint256 epochId, address vault) {
    env e;
    calldataarg args;

    require getLastAccruedTimestamp(epochId, vault) <= e.block.timestamp;
    f(e, args);
    assert getLastAccruedTimestamp(epochId, vault) <= e.block.timestamp, "lastAccruedTimestamp bigger than block timestamp";
}

/*
STATUS - VERIFIED

`lastUserAccrueTimestamp[epochId][vault][user]`:
- can only increase, there should be no way of its value to decrease
*/
rule lastUserAccruedTimestampCanOnlyIncrease(method f, uint256 epochId, address vault, address user) {
    env e;
    calldataarg args;

    uint256 lastUserAccrueTimestampBefore = getLastUserAccrueTimestamp(epochId, vault, user);
    require lastUserAccrueTimestampBefore <= e.block.timestamp;

    f(e, args);
    uint256 lastUserAccrueTimestampAfter = getLastUserAccrueTimestamp(epochId, vault, user);

    assert lastUserAccrueTimestampAfter >= lastUserAccrueTimestampBefore, "lastUserAccrueTimestamp should only increase";
}

/*
STATUS - VERIFIED

`lastUserAccrueTimestamp[epochId][vault][user]`:
- value sould always be lower or equal to block.timestamp
*/
rule lastUserAccruedTimestampCannotBeBiggerThanBlockTimestamp(method f, uint256 epochId, address vault, address user) {
    env e;
    calldataarg args;

    require getLastUserAccrueTimestamp(epochId, vault, user) <= e.block.timestamp;
    f(e, args);
    assert getLastUserAccrueTimestamp(epochId, vault, user) <= e.block.timestamp, "lastUserAccruedTimestamp bigger than block timestamp";
}

/*
STATUS - VERIFIED

`pointsWithdrawn[epochId][vault][user][token]`:
- should only increase, there should be no way of its value to decrease
- it can be changed only via claimReward, claimRewards and claimBulkTokensOverMultipleEpochs functions
- it cannot changed via any other function (its value does not change)
*/
rule pointsWithdrawnCanOnlyIncrease(method f, uint256 epochId, address vault, address user, address token) {
    env e;
    calldataarg args;

    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epochId, vault, user, token);
    f(e, args);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epochId, vault, user, token);

    assert pointsWithdrawnAfter >= pointsWithdrawnBefore, "pointsWithdrawn should only increase";
    assert f.selector != claimReward(uint256,address,address,address).selector &&
           f.selector != claimRewards(uint256[],address[],address[],address[]).selector && 
           f.selector != claimBulkTokensOverMultipleEpochs(uint256,uint256,address,address[],address).selector =>
            pointsWithdrawnBefore == pointsWithdrawnAfter, "pointsWithdrawn changed not via claimReward nor claimRewards";
}

/*
STATUS - VERIFIED

`shares[epochId][vault][user]`:
- can only change via notifyTransfer (we ban harness functions)
*/
rule sharesCanOnlyChangeViaNotifyTransfer(method f, uint256 epochId, address vault, address user) {
    env e;
    calldataarg args;

    uint256 sharesBefore = getShares(epochId, vault, user);
    f(e, args);
    uint256 sharesAfter = getShares(epochId, vault, user);

    assert 
        f.selector != notifyTransfer(address,address,uint256).selector &&
        f.selector != handleDeposit(address,address,uint256).selector &&
        f.selector != handleWithdrawal(address,address,uint256).selector &&
        f.selector != handleTransfer(address,address,address,uint256).selector =>
            sharesBefore == sharesAfter, "shares changed not via notifyTransfer";
}
