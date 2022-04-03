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

// @note - This spec file tests rules with 1 iterations unrolled optimisitcally.
//         run it with `bash certora/scripts/verifyThrottle1.sh`

// @note - VERIFIED(k) - k means that ist verified for k iterations unrolled

// -----------------------
// HIGH LEVEL
// -----------------------

// STATUS - VERIFIED(1)
rule claimAndClaimBulk2AreEqual(env e, uint256 epochId, address[] tokens, address vault, address user) {
    storage initialStorage = lastStorage;
    claimReward(e, epochId, vault, tokens[0], user);

    uint256 points = getPoints(epochId, vault, user);
    uint256 pointsWithdrawn = getPointsWithdrawn(epochId, vault, user, tokens[0]);
    uint256 totalPoints = getTotalPoints(epochId, vault);
    uint256 lastAccruedTs = getLastAccruedTimestamp(epochId, vault);
    uint256 lastUserAccruedTs = getLastUserAccrueTimestamp(epochId, vault, user);
    uint256 shares = getShares(epochId, vault, user);
    uint256 totalSupply = getTotalSupply(epochId, vault);
    uint256 balanceAfter = tokenBalanceOf(tokens[0], user);

    uint256 epochStart = epochId;
    uint256 epochEnd = epochId;
    claimBulkTokensOverMultipleEpochs(e, epochStart, epochEnd, vault, tokens, user) at initialStorage;

    assert points == getPoints(epochId, vault, user);
    assert pointsWithdrawn == getPointsWithdrawn(epochId, vault, user, tokens[0]);
    assert totalPoints == getTotalPoints(epochId, vault);
    assert lastAccruedTs == getLastAccruedTimestamp(epochId, vault);
    assert lastUserAccruedTs == getLastUserAccrueTimestamp(epochId, vault, user);
    assert shares == getShares(epochId, vault, user);
    assert totalSupply == getTotalSupply(epochId, vault);
    assert balanceAfter == tokenBalanceOf(tokens[0], user);
}

// STATUS - VERIFIED(1)
rule claimAndClaimBulkOptimizedAreEqual(env e, uint256 epochId, address[] tokens, address vault, address user) {
    storage initialStorage = lastStorage;
    claimReward(e, epochId, vault, tokens[0], user);

    uint256 pointsWithdrawn = getPointsWithdrawn(epochId, vault, user, tokens[0]);
    uint256 totalPoints = getTotalPoints(epochId, vault);
    uint256 lastAccruedTs = getLastAccruedTimestamp(epochId, vault);
    uint256 lastUserAccruedTs = getLastUserAccrueTimestamp(epochId, vault, user);
    uint256 totalSupply = getTotalSupply(epochId, vault);
    uint256 balanceAfter = tokenBalanceOf(tokens[0], user);

    uint256 epochStart = epochId;
    uint256 epochEnd = epochId;
    claimBulkTokensOverMultipleEpochs(e, epochStart, epochEnd, vault, tokens, user) at initialStorage;

    assert pointsWithdrawn == getPointsWithdrawn(epochId, vault, user, tokens[0]);
    assert totalPoints == getTotalPoints(epochId, vault);
    assert lastAccruedTs == getLastAccruedTimestamp(epochId, vault);
    assert lastUserAccruedTs == getLastUserAccrueTimestamp(epochId, vault, user);
    assert totalSupply == getTotalSupply(epochId, vault);
    assert balanceAfter == tokenBalanceOf(tokens[0], user);
}

// -----------------------
//     UNIT TESTS
// -----------------------

// STATUS - VERIFIED(1, 2)
rule minUnitTest(uint256 a, uint256 b) {
    uint256 min = min(a, b);

    assert (a < b && a == min) || b == min;
}

// STATUS - VERIFIED(1)
rule accrueShouldUpdateTotalSupply() {
    uint256 currentEpochId = currentEpoch();
    require currentEpochId > 1; // Require at least 2 initialized epoch

    address vault;
    uint256 totalSupplyAtPreviousEpoch = getTotalSupply(currentEpochId - 1, vault);
    require getLastAccruedTimestamp(currentEpochId, vault) == 0;

    env e;
    accrueVault(e, currentEpochId, vault);

    uint256 totalSupplyAtCurrentEpoch = getTotalSupply(currentEpochId, vault);

    assert totalSupplyAtPreviousEpoch > 0 => totalSupplyAtPreviousEpoch == totalSupplyAtCurrentEpoch, "totalSupply not accrued";
    assert getLastAccruedTimestamp(currentEpochId, vault) == e.block.timestamp;
    assert getVaultTimeLeftToAccrue(e, currentEpochId, vault) == 0;
}

// STATUS - VERIFIED(1)
rule accrueUserShouldUpdateUserShares() {
    uint256 currentEpochId = currentEpoch();
    require currentEpochId > 1; // Require at least 2 initialized epoch

    address vault;
    address user;
    uint256 sharesAtPreviousEpoch = getShares(currentEpochId - 1, vault, user);
    require getLastUserAccrueTimestamp(currentEpochId, vault, user) == 0;

    env e;
    accrueUser(e, currentEpochId, vault, user);

    uint256 sharesAtCurrentEpoch = getShares(currentEpochId, vault, user);

    assert sharesAtPreviousEpoch > 0 => sharesAtPreviousEpoch == sharesAtCurrentEpoch, "shares not accrued";
    assert getLastUserAccrueTimestamp(currentEpochId, vault, user) == e.block.timestamp;
    assert getUserTimeLeftToAccrue(e, currentEpochId, vault, user) == 0;
}

// STATUS - VERIFIED(1, 2)
rule getVaultTimeLeftToAccrueUnitTest(env e, uint256 epochId, address vault) {
    uint256 start = getEpochsStartTimestamp(epochId);
    uint256 end = getEpochsEndTimestamp(epochId);
    require start + SECONDS_PER_EPOCH() == end;
    require start <= e.block.timestamp;

    uint256 lastAccruedTimestamp = getLastAccruedTimestamp(epochId, vault);
    require lastAccruedTimestamp == 0 || start <= lastAccruedTimestamp;

    uint256 upperBound = min(end, e.block.timestamp);
    uint256 lowerBound = max(start, lastAccruedTimestamp);

    uint256 result = getVaultTimeLeftToAccrue(e, epochId, vault);

    if lowerBound < upperBound {
        assert result == upperBound - lowerBound;
    } else {
        assert result ==  0;
    }
}

// STATUS - VERIFIED(1, 2)
rule getUserTimeLeftToAccrueUnitTest(env e, uint256 epochId, address vault, address user) {
    uint256 start = getEpochsStartTimestamp(epochId);
    uint256 end = getEpochsEndTimestamp(epochId);
    require start + SECONDS_PER_EPOCH() == end;
    require start <= e.block.timestamp;

    uint256 lastAccruedTimestamp = getLastUserAccrueTimestamp(epochId, vault, user);
    require lastAccruedTimestamp == 0 || start <= lastAccruedTimestamp;

    uint256 upperBound = min(end, e.block.timestamp);
    uint256 lowerBound = max(start, lastAccruedTimestamp);

    uint256 result = getUserTimeLeftToAccrue(e, epochId, vault, user);

    if lowerBound < upperBound {
        assert result == upperBound - lowerBound;
    } else {
        assert result ==  0;
    }
}

// STATUS - VERIFIED(1)
rule handleDepositUnitTest(env e, address from, address to, uint256 amount) {
    require from == 0 && to != 0; // trigger handleDeposit()
    address vault = e.msg.sender;
    uint256 currentEpochId = currentEpoch();

    uint256 totalSupplyBefore = getTotalSupply(currentEpochId, vault);
    uint256 sharesBefore = getShares(currentEpochId, vault, to);

    notifyTransfer(e, from, to, amount);

    uint256 totalSupplyAfter = getTotalSupply(currentEpochId, vault);
    uint256 sharesAfter = getShares(currentEpochId, vault, to);

    assert totalSupplyBefore + amount == totalSupplyAfter;
    assert sharesBefore + amount == sharesAfter;
}

// STATUS - VERIFIED(1)
rule handleWithdrawalUnitTest(env e, address from, address to, uint256 amount) {
    require from != 0 && to == 0; // trigger handleWithdrawal()
    address vault = e.msg.sender;

    uint256 currentEpochId = currentEpoch();
    uint256 totalSupplyBefore = getTotalSupply(currentEpochId, vault);
    uint256 sharesBefore = getShares(currentEpochId, vault, from);

    notifyTransfer(e, from, to, amount);

    uint256 totalSupplyAfter = getTotalSupply(currentEpochId, vault);
    uint256 sharesAfter = getShares(currentEpochId, vault, from);

    assert totalSupplyBefore - amount == totalSupplyAfter;
    assert sharesBefore - amount == sharesAfter;
}

// STATUS - VERIFIED(1)
rule handleTransferUnitTest(env e, address from, address to, uint256 amount) {
    require from != 0 && to != 0; // trigger handleTransfer()
    address vault = e.msg.sender;

    uint256 currentEpochId = currentEpoch();
    uint256 totalSupplyBefore = getTotalSupply(currentEpochId, vault);
    uint256 sharesFromBefore = getShares(currentEpochId, vault, from);
    uint256 sharesToBefore = getShares(currentEpochId, vault, to);

    notifyTransfer(e, from, to, amount);

    uint256 totalSupplyAfter = getTotalSupply(currentEpochId, vault);
    uint256 sharesFromAfter = getShares(currentEpochId, vault, from);
    uint256 sharesToAfter = getShares(currentEpochId, vault, to);

    assert totalSupplyBefore == totalSupplyAfter;
    assert from != to => sharesFromBefore - amount == sharesFromAfter;
    assert from != to => sharesToBefore + amount == sharesToAfter;
    assert from == to => sharesToBefore == sharesToAfter;
}

// STATUS - VERIFIED(1)
rule addRewardUnitTest(env e, uint256 epochId, address vault, address token, uint256 amount) {
    address contractAddress = getRewardsManagerAddress();
    require e.msg.sender != contractAddress;

    uint256 rewardsBefore = getRewards(epochId, vault, token);
    uint256 balanceBefore = tokenBalanceOf(token, contractAddress);

    addReward(e, epochId, vault, token, amount);

    uint256 rewardsAfter = getRewards(epochId, vault, token);
    uint256 balanceAfter = tokenBalanceOf(token, contractAddress);

    assert rewardsBefore + amount == rewardsAfter;
    assert balanceBefore + amount == balanceAfter;
}

// STATUS - VERIFIED(1)
rule claimBulkTokensOverMultipleEpochsUnitTest(env e, uint256 epochStart, uint256 epochEnd, address vault, address[] tokens, address user) {
    require user != getRewardsManagerAddress();
    require epochStart == epochEnd; // If it works for 1 epoch it should work for
    require tokens.length == 1; // In other spec files increase token array
    address token = tokens[0];
    // require tokens[0] != tokens[1]; // this would be unhealthy under-approximation ...

    accrueUser(e, epochStart, vault, user);
    accrueVault(e, epochStart, vault);

    uint256 totalPoints = getTotalPoints(epochStart, vault);
    uint256 pointsWithdrawn = getPointsWithdrawn(epochStart, vault, user, token);
    uint256 userPoints = getPoints(epochStart, vault, user);
    uint256 rewards = getRewards(epochStart, vault, token);

    require pointsWithdrawn <= userPoints && userPoints <= totalPoints;
    require rewards <= 10^30; // sane value
    require 0 < totalPoints && totalPoints <= 10^30; // sane value

    uint256 share = PRECISION() * (userPoints - pointsWithdrawn) / totalPoints;
    uint256 delta = rewards * share / PRECISION();

    uint256 balanceBefore = tokenBalanceOf(token, user);
    require balanceBefore <= 10^30; // sane value

    claimBulkTokensOverMultipleEpochs(e, epochStart, epochEnd, vault, tokens, user);

    uint256 balanceAfter = tokenBalanceOf(token, user);

    assert getLastAccruedTimestamp(epochStart, vault) == e.block.timestamp;
    assert getLastUserAccrueTimestamp(epochStart, vault, user) == e.block.timestamp;
    assert balanceAfter - balanceBefore == delta;
    assert userPoints == getPointsWithdrawn(epochStart, vault, user, token), "not withdrawn all points";
}

// STATUS - in progress(1)
rule claimBulkTokensOverMultipleEpochsOptimizedUnitTest(env e, uint256 epochStart, uint256 epochEnd, address vault, address[] tokens) {
    address user = e.msg.sender;
    require user != getRewardsManagerAddress();
    require epochStart == epochEnd;
    require tokens.length == 1;
    address token = tokens[0];

    accrueUser(e, epochStart, vault, user);
    accrueVault(e, epochStart, vault);

    uint256 totalPoints = getTotalPoints(epochStart, vault);
    uint256 pointsWithdrawn = getPointsWithdrawn(epochStart, vault, user, token);
    uint256 userPoints = getPoints(epochStart, vault, user);
    uint256 rewards = getRewards(epochStart, vault, token);

    require pointsWithdrawn <= userPoints && userPoints <= totalPoints;
    require rewards <= 10^30; // sane value
    require 0 < totalPoints && totalPoints <= 10^30; // sane value

    uint256 share = PRECISION() * (userPoints - pointsWithdrawn) / totalPoints;
    uint256 delta = rewards * share / PRECISION();

    uint256 balanceBefore = tokenBalanceOf(token, user);
    require balanceBefore <= 10^30; // sane value

    claimBulkTokensOverMultipleEpochsOptimized(e, epochStart, epochEnd, vault, tokens);

    uint256 balanceAfter = tokenBalanceOf(token, user);

    assert getLastAccruedTimestamp(epochStart, vault) == e.block.timestamp;
    assert getLastUserAccrueTimestamp(epochStart, vault, user) == e.block.timestamp;
    assert balanceAfter - balanceBefore == delta;
    assert getPoints(epochStart, vault, user) == 0;
}
