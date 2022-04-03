import "erc20.spec"

methods {
    // constants
    SECONDS_PER_EPOCH() returns(uint256) envfree
    PRECISION() returns(uint256) envfree

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
    getRewardsManagerAddress() returns (address) envfree

    // methods
    startNextEpoch()
    accrueVault(uint256, address)
    getVaultTimeLeftToAccrue(uint256, address) returns(uint256)
    getUserTimeLeftToAccrue(uint256, address, address) returns(uint256)
    claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[])
    addRewards(uint256[], address[], address[], uint256[])
    addReward(uint256, address, address, uint256)
    notifyTransfer(address, address, uint256)
    accrueUser(uint256, address, address)
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
    max(uint256, uint256) returns(uint256) envfree
    tokenBalanceOf(address, address) returns(uint256) envfree
    tokenAllowance(address, address, address) returns(uint256) envfree
}

// @note - This spec file tests rules with 2 iterations unrolled optimisitcally.
//         run it with `bash certora/scripts/verifyThrottle2.sh`

// @note - VERIFIED(k) - k means that ist verified for k iterations unrolled

function isClaimFunction(method f) returns bool {
    return f.selector == claimReward(uint256,address,address,address).selector ||
        f.selector == claimRewards(uint256[],address[],address[],address[]).selector ||
        f.selector == claimBulkTokensOverMultipleEpochs(uint256,uint256,address,address[],address).selector ||
        f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256,uint256,address,address[]).selector;
}

function isAddRewardFunction(method f) returns bool {
    return f.selector == addRewards(uint256[],address[],address[],uint256[]).selector ||
        f.selector == addReward(uint256,address,address,uint256).selector;
}

function isVaultAccruingFunction(method f) returns bool {
    return isClaimFunction(f) ||
        f.selector == accrueVault(uint256,address).selector ||
        f.selector == notifyTransfer(address,address,uint256).selector ||
        f.selector == handleDeposit(address,address,uint256).selector ||
        f.selector == handleWithdrawal(address,address,uint256).selector ||
        f.selector == handleTransfer(address,address,address,uint256).selector;
}

function isUserAccruingFunction(method f) returns bool {
    return isClaimFunction(f) ||
        f.selector == accrueUser(uint256,address,address).selector ||
        f.selector == notifyTransfer(address,address,uint256).selector ||
        f.selector == handleDeposit(address,address,uint256).selector ||
        f.selector == handleWithdrawal(address,address,uint256).selector ||
        f.selector == handleTransfer(address,address,address,uint256).selector;
}

// -----------------------
// VALID STATES
// -----------------------

// STATUS - VERIFIED(1, 2)
invariant futureEpoch(uint256 epochId, address vault, address user, address rewardToken)
    currentEpoch() < epochId => (
        getEpochsStartTimestamp(epochId) == 0 &&
        getEpochsEndTimestamp(epochId) == 0 &&
        getPoints(epochId, vault, user) == 0 &&
        getPointsWithdrawn(epochId, vault, user, rewardToken) == 0 &&
        getTotalPoints(epochId, vault) == 0 &&
        getLastAccruedTimestamp(epochId, vault) == 0 &&
        getLastUserAccrueTimestamp(epochId, vault, user) == 0 &&
        getShares(epochId, vault, user) == 0 &&
        getTotalSupply(epochId, vault) == 0
    )
//
// STATUS - VERIFIED(1, 2)
// Accrue TS either uninitialized or accrued after epoch start
rule validLastAccrueTimestampInvariant(method f, env e, uint256 epochId, address vault) filtered {f -> !f.isView} {
    require 0 == getLastAccruedTimestamp(epochId, vault) || getEpochsStartTimestamp(epochId) <= getLastAccruedTimestamp(epochId, vault);
    require getLastAccruedTimestamp(epochId, vault) <= e.block.timestamp;
    require getEpochsStartTimestamp(epochId) <= e.block.timestamp;
    require epochId <= currentEpoch();

    calldataarg args;
    f(e, args);

    assert 0 == getLastAccruedTimestamp(epochId, vault) || getEpochsStartTimestamp(epochId) <= getLastAccruedTimestamp(epochId, vault);
}

// STATUS - VERIFIED(1, 2)
// Accrue TS either uninitialized or accrued after epoch start
rule validLastUserAccrueTimestampInvariant(method f, env e, uint256 epochId, address vault, address user) filtered {f -> !f.isView} {
    require 0 == getLastUserAccrueTimestamp(epochId, vault, user) || getEpochsStartTimestamp(epochId) <= getLastUserAccrueTimestamp(epochId, vault, user);
    require getLastUserAccrueTimestamp(epochId, vault, user) <= e.block.timestamp;
    require getEpochsStartTimestamp(epochId) <= e.block.timestamp;
    require epochId <= currentEpoch();

    calldataarg args;
    f(e, args);

    assert 0 == getLastUserAccrueTimestamp(epochId, vault, user) || getEpochsStartTimestamp(epochId) <= getLastUserAccrueTimestamp(epochId, vault, user);
}

// -----------------------
// STATE TRANSITIONS
// -----------------------

// STATUS - VERIFIED(1, 2)
rule epochTimestamps(method f) filtered {f -> !f.isView} {
    address vault;
    uint256 oldEpoch = currentEpoch();
    uint256 startOldEpoch = getEpochsStartTimestamp(oldEpoch);
    uint256 endOldEpoch = getEpochsEndTimestamp(oldEpoch);

    env e;
    calldataarg args;
    f(e, args);

    uint256 newEpoch = currentEpoch();
    uint256 startNewEpoch = getEpochsStartTimestamp(newEpoch);
    uint256 endNewEpoch = getEpochsEndTimestamp(newEpoch);

    assert oldEpoch + 1 == newEpoch => startNewEpoch + SECONDS_PER_EPOCH() == endNewEpoch, "epoch should be valid for 1 week";
    assert oldEpoch + 1 == newEpoch => endOldEpoch < startNewEpoch && startNewEpoch == e.block.timestamp, "invalid timestamps";
}

// -----------------------
// VARIABLES TRANSITIONS
// -----------------------

// STATUS - VERIFIED(1, 2)
rule lastAccrueTimestampNotDecreasing(method f) filtered {f -> !f.isView} {
    env e;
    calldataarg args;

    uint256 epochId;
    address vault;
    uint256 lastAccruedTimestampBefore = getLastAccruedTimestamp(epochId, vault);
    require lastAccruedTimestampBefore <= e.block.timestamp;

    f(e);

    uint256 lastAccruedTimestampAfter = getLastAccruedTimestamp(epochId, vault);

    assert lastAccruedTimestampBefore <= lastAccruedTimestampAfter, "lastAccruedTimestamp decreased";
    assert lastAccruedTimestampBefore < lastAccruedTimestampAfter => isVaultAccruingFunction(f), "lastAccruedTimestamp updated by wrong function";
}

// STATUS - VERIFIED(1, 2)
rule lastUserAccrueTimestampNotDecreasing(method f) filtered {f -> !f.isView} {
    env e;
    calldataarg args;

    uint256 epochId;
    address vault;
    address user;
    uint256 lastUserAccruedTimestampBefore = getLastUserAccrueTimestamp(epochId, vault, user);
    require lastUserAccruedTimestampBefore <= e.block.timestamp;

    f(e);

    uint256 lastUserAccruedTimestampAfter = getLastUserAccrueTimestamp(epochId, vault, user);

    assert lastUserAccruedTimestampBefore <= lastUserAccruedTimestampAfter, "lastUserAccruedTimestamp decreased";
    assert lastUserAccruedTimestampBefore < lastUserAccruedTimestampAfter => isUserAccruingFunction(f), "lastUserAccruedTimestamp updated by wrong function";
}

// STATUS - VERIFIED(1, 2)
rule totalPointsNotDecreasing(method f) filtered {f -> !f.isView} {
    uint256 epochId;
    address vault;
    uint256 totalPointsBefore = getTotalPoints(epochId, vault);

    env e;
    calldataarg args;
    f(e);

    uint256 totalPointsAfter = getTotalPoints(epochId, vault);

    assert totalPointsBefore <= totalPointsAfter, "totalPoints decreased";
    assert totalPointsBefore < totalPointsAfter => isVaultAccruingFunction(f), "totalPoints updated by wrong function";
}

// STATUS - VERIFIED(1, 2)
rule pointsWithdrawnNotDecreasing(method f) filtered {f -> !f.isView} {
    uint256 epochId;
    address vault;
    address user;
    address token;
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epochId, vault, user, token);

    env e;
    calldataarg args;
    f(e);

    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epochId, vault, user, token);

    assert pointsWithdrawnBefore <= pointsWithdrawnAfter, "pointsWithdrawn decreased";
    assert pointsWithdrawnBefore < pointsWithdrawnAfter => isClaimFunction(f), "pointsWithdrawn should increase only when claiming";
}

// STATUS - VERIFIED(1, 2)
rule pointsNotDecreasing(method f) filtered {f -> !f.isView && f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256,uint256,address,address[]).selector} {
    uint256 epochId;
    address vault;
    address user;
    uint256 pointsBefore = getPoints(epochId, vault, user);

    env e;
    calldataarg args;
    f(e);

    uint256 pointsAfter = getPoints(epochId, vault, user);

    assert pointsBefore <= pointsAfter, "points decreased";
    assert pointsBefore < pointsAfter => isUserAccruingFunction(f), "points updated by wrong function";
}

// STATUS - VERIFIED(1, 2)
rule rewardsNotDecreasing(method f) filtered {f -> !f.isView} {
    uint256 epochId;
    address vault;
    address user;
    uint256 rewardsBefore = getRewards(epochId, vault, user);

    env e;
    calldataarg args;
    f(e);

    uint256 rewardsAfter = getRewards(epochId, vault, user);

    assert rewardsBefore <= rewardsAfter, "rewards decreased";
    assert rewardsBefore < rewardsAfter => isAddRewardFunction(f) , "change triggered by wrong function";
}

// STATUS - VERIFIED(1, 2)
rule lastVaultDepositNotDecreasing(method f) filtered {f -> !f.isView} {
    address vault;
    uint256 lastVaultDepositBefore = getLastVaultDeposit(vault);

    env e;
    calldataarg args;
    f(e);

    uint256 lastVaultDepositAfter = getLastVaultDeposit(vault);

    assert lastVaultDepositBefore <= lastVaultDepositAfter, "lastVaultDeposit decreased";
    assert lastVaultDepositBefore < lastVaultDepositAfter => isVaultAccruingFunction(f), "lastVaultDeposit updated by wrong function";
}

// STATUS - VERIFIED(1, 2)
rule currentEpochCanOnlyIncreaseByOne(method f) filtered {f -> !f.isView} {
    address vault;
    uint256 currentEpochBefore = currentEpoch();

    env e;
    calldataarg args;
    f(e);

    uint256 currentEpochAfter = currentEpoch();

    assert currentEpochBefore == currentEpochAfter || currentEpochBefore + 1 == currentEpochAfter, "currentEpoch can increase only by 1";
    assert currentEpochBefore + 1 == currentEpochAfter => f.selector == startNextEpoch().selector, "startNextEpoch() should be called";
}

// -----------------------
// HIGH LEVEL
// -----------------------

// STATUS - VERIFIED(1, 2)
// rewards can be added only for the future epoch
rule rewardsCantBeAddedToPastEpochs(method f) filtered {f -> !f.isView} {
    uint256 epochId;
    address vault;
    address token;
    uint256 rewardsBefore = getRewards(epochId, vault, token);
    uint256 currentEpochId = currentEpoch();

    env e;
    calldataarg args;
    f(e);

    uint256 rewardsAfter = getRewards(epochId, vault, token);

    assert rewardsBefore < rewardsAfter => epochId >= currentEpochId, "rewards added to past epoch";
}

// STATUS - VERIFIED(1, 2)
// rewards can be claimed only for past epoch
rule rewardsCanBeClaimedFromPastEpochs(address token1, method f) filtered {f -> !f.isView} {
    uint256 epochId;
    address vault;
    address token;
    address user;
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epochId, vault, token, user);
    uint256 currentEpochId = currentEpoch();

    env e;
    calldataarg args;
    f(e);

    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epochId, vault, token, user);

    assert pointsWithdrawnBefore < pointsWithdrawnAfter => epochId < currentEpochId, "rewards claimed too early 1";
}

// STATUS - VERIFIED(1, 2)
// PointsWithdrawn should be always <= points
rule pointsWithdrawnLessOrEqualToUserPointsInvariant(method f) filtered {f -> !f.isView && f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256,uint256,address,address[]).selector} {
    uint256 epochId;
    address vault;
    address user;
    address rewardToken;
    require getPointsWithdrawn(epochId, vault, user, rewardToken) <= getPoints(epochId, vault, user);

    env e;
    calldataarg args;
    f(e, args);

    assert getPointsWithdrawn(epochId, vault, user, rewardToken) <= getPoints(epochId, vault, user);
}

// STATUS - VERIFIED(1, 2)
rule secondAccrueVaultIsIdentity(env e, uint256 epochId, address vault) {
    require e.block.timestamp > 0;

    accrueVault(e, epochId, vault);

    uint256 totalSupply = getTotalSupply(epochId, vault);
    uint256 totalPoints = getTotalPoints(epochId, vault);
    uint256 lastAccruedTs = getLastAccruedTimestamp(epochId, vault);

    accrueVault(e, epochId, vault);

    assert totalSupply == getTotalSupply(epochId, vault);
    assert totalPoints == getTotalPoints(epochId, vault);
    assert lastAccruedTs == getLastAccruedTimestamp(epochId, vault);
}

// STATUS - VERIFIED(1, 2)
rule secondAccrueUserIsIdentity(env e, uint256 epochId, address vault, address user) {
    require e.block.timestamp > 0;

    accrueUser(e, epochId, vault, user);

    uint256 shares = getShares(epochId, vault, user);
    uint256 points = getPoints(epochId, vault, user);
    uint256 lastAccrueTs = getLastUserAccrueTimestamp(epochId, vault, user);

    accrueUser(e, epochId, vault, user);

    assert shares == getShares(epochId, vault, user);
    assert points == getPoints(epochId, vault, user);
    assert lastAccrueTs == getLastUserAccrueTimestamp(epochId, vault, user);
}

// STATUS - VERIFIED(1, 2)
rule claimAndClaimBulkAreEqual(env e, uint256[] epochIds, address[] tokens, address[] vaults, address[] users) {
    require epochIds.length == 1 && epochIds.length == tokens.length && epochIds.length == vaults.length && epochIds.length == users.length;
    storage initialStorage = lastStorage;
    claimReward(e, epochIds[0], vaults[0], tokens[0], users[0]);

    uint256 points = getPoints(epochIds[0], vaults[0], users[0]);
    uint256 pointsWithdrawn = getPointsWithdrawn(epochIds[0], vaults[0], users[0], tokens[0]);
    uint256 totalPoints = getTotalPoints(epochIds[0], vaults[0]);
    uint256 lastAccruedTs = getLastAccruedTimestamp(epochIds[0], vaults[0]);
    uint256 lastUserAccruedTs = getLastUserAccrueTimestamp(epochIds[0], vaults[0], users[0]);
    uint256 shares = getShares(epochIds[0], vaults[0], users[0]);
    uint256 totalSupply = getTotalSupply(epochIds[0], vaults[0]);
    uint256 balanceAfter = tokenBalanceOf(tokens[0], users[0]);

    claimRewards(e, epochIds, vaults, tokens, users) at initialStorage;

    assert points == getPoints(epochIds[0], vaults[0], users[0]);
    assert pointsWithdrawn == getPointsWithdrawn(epochIds[0], vaults[0], users[0], tokens[0]);
    assert totalPoints == getTotalPoints(epochIds[0], vaults[0]);
    assert lastAccruedTs == getLastAccruedTimestamp(epochIds[0], vaults[0]);
    assert lastUserAccruedTs == getLastUserAccrueTimestamp(epochIds[0], vaults[0], users[0]);
    assert shares == getShares(epochIds[0], vaults[0], users[0]);
    assert totalSupply == getTotalSupply(epochIds[0], vaults[0]);
    assert balanceAfter == tokenBalanceOf(tokens[0], users[0]);
}

// -----------------------
//     UNIT TESTS
// -----------------------

// STATUS - VERIFIED(2)
// If epochId was accrued then return last supply and dont update
// If epochId was not accrued then look back 1 epoch
// If epochId and epochId - 1 were not accrued then look back 2 epochs
// 2 is enough because we unroll loop exactly 2 iterations
rule getTotalSupplyAtEpochUnitTest(env e, uint256 epochId, address vault, address user, address rewardToken) {
    requireInvariant futureEpoch(epochId, vault, user, rewardToken);

    uint256 lastSupply;
    bool update;
    lastSupply, update = getTotalSupplyAtEpoch(epochId, vault);

    assert (epochId > 0 &&
            getLastAccruedTimestamp(epochId, vault) > 0)
        => (lastSupply == getTotalSupply(epochId, vault) && update == false);
    assert (epochId > 1 &&
            getLastAccruedTimestamp(epochId, vault) == 0 &&
            getLastAccruedTimestamp(epochId - 1, vault) > 0)
        => (lastSupply == getTotalSupply(epochId - 1, vault) && ((lastSupply > 0 && update == true) || update == false));
    assert (epochId > 2 &&
            getLastAccruedTimestamp(epochId, vault) == 0 &&
            getLastAccruedTimestamp(epochId - 1, vault) == 0 &&
            getLastAccruedTimestamp(epochId - 2, vault) > 0)
        => (lastSupply == getTotalSupply(epochId - 2, vault) && ((lastSupply > 0 && update == true) || update == false));
}

// STATUS - VERIFIED(2)
rule getBalanceAtEpochUnitTest(env e, uint256 epochId, address vault, address user, address rewardToken) {
    requireInvariant futureEpoch(epochId, vault, user, rewardToken);

    uint256 lastBalance;
    bool update;
    lastBalance, update = getBalanceAtEpoch(epochId, vault, user);

    assert (epochId > 0 &&
            getLastUserAccrueTimestamp(epochId, vault, user) > 0)
        => (lastBalance == getShares(epochId, vault, user) && update == false);
    assert (epochId > 1 &&
            getLastUserAccrueTimestamp(epochId, vault, user) == 0 &&
            getLastUserAccrueTimestamp(epochId - 1, vault, user) > 0)
        => (lastBalance == getShares(epochId - 1, vault, user) && update == true);
    assert (epochId > 2 &&
            getLastUserAccrueTimestamp(epochId, vault, user) == 0 &&
            getLastUserAccrueTimestamp(epochId - 1, vault, user) == 0 &&
            getLastUserAccrueTimestamp(epochId - 2, vault, user) > 0)
        => (lastBalance == getShares(epochId - 2, vault, user) && update == true);
}

// STATUS - VERIFIED(1, 2)
rule claimRewardUnitTest(env e, uint256 epochId, address vault, address token, address user) {
    require user != getRewardsManagerAddress();

    accrueUser(e, epochId, vault, user);
    accrueVault(e, epochId, vault);

    uint256 totalPoints = getTotalPoints(epochId, vault);
    uint256 pointsWithdrawn = getPointsWithdrawn(epochId, vault, user, token);
    uint256 userPoints = getPoints(epochId, vault, user);
    uint256 rewards = getRewards(epochId, vault, token);

    require pointsWithdrawn <= userPoints && userPoints <= totalPoints;
    require rewards <= 10^30; // sane value
    require 0 < totalPoints && totalPoints <= 10^30; // sane value

    uint256 share = PRECISION() * (userPoints - pointsWithdrawn) / totalPoints;
    uint256 delta = rewards * share / PRECISION();

    uint256 balanceBefore = tokenBalanceOf(token, user);
    require balanceBefore <= 10^30; // sane value

    claimReward(e, epochId, vault, token, user);

    uint256 balanceAfter = tokenBalanceOf(token, user);

    assert getLastAccruedTimestamp(epochId, vault) == e.block.timestamp;
    assert getLastUserAccrueTimestamp(epochId, vault, user) == e.block.timestamp;
    assert balanceAfter - balanceBefore == delta;
    assert userPoints == getPointsWithdrawn(epochId, vault, user, token), "not withdrawn all points";
}

// STATUS - VERIFIED(2)
// Test if points withdrawn are maxed out and both epochs are accrued
rule claimBulkTokensOverMultipleEpochsUnitTest(env e, uint256 epochStart, uint256 epochEnd, address vault, address[] tokens, address user) {
    require epochStart + 1 == epochEnd;
    require tokens.length >= 1;
    require getPoints(epochStart, vault, user) > 0;
    require getPoints(epochEnd, vault, user) > 0;

    claimBulkTokensOverMultipleEpochs(e, epochStart, epochEnd, vault, tokens, user);

    assert getLastUserAccrueTimestamp(epochStart, vault, user) == e.block.timestamp;
    assert getLastUserAccrueTimestamp(epochEnd, vault, user) == e.block.timestamp;

    assert getPointsWithdrawn(epochStart, vault, user, tokens[0]) == getPoints(epochStart, vault, user);
    assert getPointsWithdrawn(epochEnd, vault, user, tokens[0]) == getPoints(epochEnd, vault, user);
}

// STATUS - VERIFIED(2)
// Test if data structures are deleted and both epochs are accrued
rule claimBulkTokensOverMultipleEpochsOptimizedUnitTest(env e, uint256 epochStart, uint256 epochEnd, address vault, address[] tokens) {
    require epochStart + 1 == epochEnd;
    address user = e.msg.sender;

    claimBulkTokensOverMultipleEpochsOptimized(e, epochStart, epochEnd, vault, tokens);

    assert getLastUserAccrueTimestamp(epochStart, vault, user) == e.block.timestamp;
    assert getLastUserAccrueTimestamp(epochEnd, vault, user) == e.block.timestamp;

    assert getShares(epochStart, vault, user) == 0;
    assert getPoints(epochStart, vault, user) == 0;
    assert getPoints(epochEnd, vault, user) == 0;
}
