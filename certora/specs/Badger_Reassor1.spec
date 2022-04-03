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
    getAddress() returns(address) envfree;

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

// ================ UNIT TESTS ===============

/*
STATUS - VERIFIED

Unit Test - startNextEpoch()
Checking the correctness of starting next epoch
- increase currentEpoch
- add new epoch to epochs with valid startTimestamp and epochEndTimestamp
*/
rule unitTestStartNextEpoch() {
    env e;
    
    uint256 currentEpochBefore = currentEpoch();
    
    startNextEpoch(e);
    
    uint256 currentEpochAfter = currentEpoch();
    assert currentEpochAfter == currentEpochBefore + 1, "failed to increase epoch";
    
    uint256 epochStartTimestamp = getEpochsStartTimestamp(currentEpochAfter);
    uint256 epochEndTimestamp = getEpochsEndTimestamp(currentEpochAfter); 

    assert epochStartTimestamp == e.block.timestamp, "invalid epochStartTimestamp";
    assert epochEndTimestamp == e.block.timestamp + SECONDS_PER_EPOCH(), "invalid epochEndTimestamp";
}

/*
STATUS - VERIFIED

Unit Test - accrueVault(uint256 epochId, address vault)
Checking correctness of accruing vault
*/
rule unitTestAccrueVault(uint256 epochId, address vault) {
    env e;

    uint256 totalPointsBefore = getTotalPoints(epochId, vault);
    uint256 lastAccruedTimestampBefore = getLastAccruedTimestamp(epochId, vault);
    uint256 totalSupplyBefore = getTotalSupply(epochId, vault);

    uint256 supply; bool shouldUpdate;
    supply, shouldUpdate = getTotalSupplyAtEpoch(epochId, vault);
    uint256 timeLeftToAccrue = getVaultTimeLeftToAccrue(e, epochId, vault);

    accrueVault(e, epochId, vault);

    uint256 totalPointsAfter = getTotalPoints(epochId, vault);
    uint256 lastAccruedTimestampAfter = getLastAccruedTimestamp(epochId, vault);
    uint256 totalSupplyAfter = getTotalSupply(epochId, vault);

    assert shouldUpdate => totalSupplyAfter == supply, "failed to update totalSupply";
    assert !shouldUpdate => totalSupplyAfter == totalSupplyBefore, "failed should not change totalSupply";
    assert lastAccruedTimestampAfter == e.block.timestamp, "failed to update lastAccruedTimestampAfter";

    assert timeLeftToAccrue == 0 => totalPointsAfter == totalPointsBefore, "failed should not change total points";
    assert timeLeftToAccrue > 0 => totalPointsAfter == totalPointsBefore + timeLeftToAccrue * supply, "failed to correctly increase totalPoints";
}

/*
STATUS - VERIFIED

Unit Test - accrueUser(uint256 epochId, address vault, address user)
Checking correctness of accruing user
*/
rule unitTestAccrueUser(uint256 epochId, address vault, address user) {
    env e; 

    uint256 currentBalance; bool shouldUpdate;
    currentBalance, shouldUpdate = getBalanceAtEpoch(epochId, vault, user);

    uint256 sharesBefore = getShares(epochId, vault, user);
    uint256 timeInEpochSinceLastAccrue = getUserTimeLeftToAccrue(e, epochId, vault, user);
    uint256 pointsBefore = getPoints(epochId, vault, user);

    accrueUser(e, epochId, vault, user);

    uint256 sharesAfter = getShares(epochId, vault, user);
    uint256 lastUserAccrueTimestampAfter = getLastUserAccrueTimestamp(epochId, vault, user);
    uint256 pointsAfter = getPoints(epochId, vault, user);

    assert shouldUpdate => sharesAfter == currentBalance, "failed to update shares";
    assert !shouldUpdate => sharesAfter == sharesBefore, "failed should not change shares";

    assert lastUserAccrueTimestampAfter == e.block.timestamp, "failed to update lastUserAccrueTimestamp";
    assert timeInEpochSinceLastAccrue == 0 => pointsAfter == pointsBefore, "failed should not change points";
    assert currentBalance > 0 && timeInEpochSinceLastAccrue > 0 =>
        pointsAfter == pointsBefore + currentBalance * timeInEpochSinceLastAccrue, "failed to increase points";
}

/*
STATUS - VERIFIED

Unit Test - claimReward(uint256 epochId, address vault, address token, address user)
Checking the correctness of claiming reward:
- increase pointsWithdrawn
- user points should be equal to withdrawn points
*/
rule unitTestClaimReward(uint256 epochId, address vault, address token, address user) {
    env e;

    claimReward(e, epochId, vault, token, user);

    uint256 userPointsAfter = getPoints(epochId, vault, user);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epochId, vault, user, token);

    assert userPointsAfter == pointsWithdrawnAfter, "failed to update points withdraw";
}

/*
STATUS - VERIFIED

Unit Test - addReward(int256 epochId, address vault, address token, uint256 amount)
Checking the correctness of adding reward:
- transfering amount of tokens to the contract
- adding rewards
*/
rule unitTestAddReward(uint256 epochId, address vault, address token, uint256 amount) {
    env e;

    require e.msg.sender != currentContract;

    uint256 rewardsBefore = getRewards(epochId, vault, token);
    addReward(e, epochId, vault, token, amount);
    uint256 rewardsAfter = getRewards(epochId, vault, token);

    assert rewardsAfter == rewardsBefore + amount, "failed to add rewards";
}

/*
STATUS - VERIFIED

Unit Test - addReward(int256 epochId, address vault, address token, uint256 amount)
*/
rule unitTestAddRewardIncreaseTokenBalance(uint256 epochId, address vault, address token, uint256 amount) {
    env e;

    require e.msg.sender != currentContract;

    uint256 tokenBalanceBefore = tokenBalanceOf(token, currentContract);
    addReward(e, epochId, vault, token, amount);
    uint256 tokenBalanceAfter = tokenBalanceOf(token, currentContract);

    assert tokenBalanceAfter == tokenBalanceBefore + amount, "failed to add tokens as reward";
}


/*
STATUS - VERIFIED

Unit Test - claimRewards(uint256[] calldata epochsToClaim, address[] calldata vaults, address[] calldata tokens, address[] calldata users)
Checking the correctness of claming multiple rewards
- increase pointsWithdrawn
- user points should be equal to withdrawn points for every user
*/
rule unitTestClaimRewards(uint256[] epochsToClaim, address[] vaults, address[] tokens, address[] users) {
    env e;

    require epochsToClaim.length == 3;

    claimRewards(e, epochsToClaim, vaults, tokens, users);

    uint256 first_userPointsAfter = getPoints(epochsToClaim[0], vaults[0], users[0]);
    uint256 first_pointsWithdrawnAfter = getPointsWithdrawn(epochsToClaim[0], vaults[0], users[0], tokens[0]);

    assert first_userPointsAfter == first_pointsWithdrawnAfter, "failed to update points withdraw first user";

    uint256 second_userPointsAfter = getPoints(epochsToClaim[1], vaults[1], users[1]);
    uint256 second_pointsWithdrawnAfter = getPointsWithdrawn(epochsToClaim[1], vaults[1], users[1], tokens[1]);

    assert second_userPointsAfter == second_pointsWithdrawnAfter, "failed to update points withdraw second user";

    uint256 third_userPointsAfter = getPoints(epochsToClaim[2], vaults[2], users[2]);
    uint256 third_pointsWithdrawnAfter = getPointsWithdrawn(epochsToClaim[2], vaults[2], users[2], tokens[2]);

    assert third_userPointsAfter == third_pointsWithdrawnAfter, "failed to update points withdraw third user";
}

/*
STATUS - VERIFIED

Unit Test notifyTransfer(address from, address to, uint256 amount) - deposit path
Checking the correctness of depositing:
- increasing shares of the user
- increasing totalSupply
*/
rule unitTestNotifyTransferDepositPath(address vault, address from, address to, uint256 amount) {
    env e;

    require from == 0;
    require vault == e.msg.sender;

    uint256 currentEpoch = currentEpoch();

    uint256 sharesBefore = getShares(currentEpoch, vault, to);
    uint256 totalSupplyBefore = getTotalSupply(currentEpoch, vault);

    notifyTransfer(e, from, to, amount);

    uint256 sharesAfter = getShares(currentEpoch, vault, to);
    uint256 totalSupplyAfter = getTotalSupply(currentEpoch, vault);

    assert sharesAfter == sharesBefore + amount, "failed to correctly increase shares";
    assert totalSupplyAfter == totalSupplyBefore + amount, "failed to correctly increase total supply";
}

/*
STATUS - VERIFIED

Unit Test notifyTransfer(address from, address to, uint256 amount) - withdrawal path
Checking the correctness of notifying withdrawal:
- decreasing shares of the user
- decreasing totalSupply
*/
rule unitTestNotifyTransferWithdrawalPath(address vault, address from, address to, uint256 amount) {
    env e;

    require from != 0 && to == 0;
    require vault == e.msg.sender;

    uint256 currentEpoch = currentEpoch();

    uint256 sharesBefore = getShares(currentEpoch, vault, from);
    uint256 totalSupplyBefore = getTotalSupply(currentEpoch, vault);

    notifyTransfer(e, from, to, amount);

    uint256 sharesAfter = getShares(currentEpoch,vault, from);
    uint256 totalSupplyAfter = getTotalSupply(currentEpoch, vault);

    assert sharesAfter == sharesBefore - amount, "failed to correctly decrease shares";
    assert totalSupplyAfter == totalSupplyBefore - amount, "failed to correctly decrease total supply";
}
