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


// @note - This file contains failing rules

// STATUS - ISSUE. RULE FAILS
// @note - This rule fails because accruing stops at epoch 0 (excluded)
//         but it is possible to make deposit at epoch 0.
//         Users who deposit at epoch 0 will not be accoutned for rewards...
//         However, the developer comment says that first epoch will be launched right after deployment...
//         But there is no reason to trust dev comments. There are ways that developer could assure that:
//         1. starting first epoch in constructor
//         2. not allow deposits in epoch 0
//         Thus, I consider it a bug/issue
rule accrueShouldUpdateTotalSupply(env e, address vault) {
    uint256 currentEpochId = currentEpoch();
    require currentEpochId > 0; // Require at least 1 defined epoch

    uint256 totalSupplyAtPreviousEpoch = getTotalSupply(currentEpochId - 1, vault);
    require totalSupplyAtPreviousEpoch > 0;
    require getTotalSupply(currentEpochId, vault) == 0;
    require getLastAccruedTimestamp(currentEpochId, vault) == 0;

    accrueVault(e, currentEpochId, vault);

    uint256 totalSupplyAtCurrentEpoch = getTotalSupply(currentEpochId, vault);

    assert totalSupplyAtPreviousEpoch > 0 => totalSupplyAtPreviousEpoch == totalSupplyAtCurrentEpoch, "totalSupply not accrued";
}

// STATUS - ISSUE. RULE FAILS
// @note - Similar as issue 1
rule accrueUserShouldUpdateUserShares(env e, address vault, address user) {
    uint256 currentEpochId = currentEpoch();
    require currentEpochId > 0; // Require at least 1 defined epoch

    uint256 sharesAtPreviousEpoch = getShares(currentEpochId - 1, vault, user);
    require sharesAtPreviousEpoch > 0;
    require getShares(currentEpochId, vault, user) == 0;
    require getLastUserAccrueTimestamp(currentEpochId, vault, user) == 0;

    accrueUser(e, currentEpochId, vault, user);

    uint256 sharesAtCurrentEpoch = getShares(currentEpochId, vault, user);

    assert sharesAtPreviousEpoch > 0 => sharesAtPreviousEpoch == sharesAtCurrentEpoch, "shares not accrued";
}

// STATUS - ISSUE. RULE FAILS
// @note - No `require(to != address(0))` input validation.
rule handleDepositUnitTest(env e, address from, address to, uint256 amount) {
    require from == 0; // trigger handleDeposit()
    address vault = e.msg.sender;
    uint256 currentEpochId = currentEpoch();

    uint256 totalSupplyBefore = getTotalSupply(currentEpochId, vault);
    uint256 sharesBefore = getShares(currentEpochId, vault, to);

    notifyTransfer(e, from, to, amount);

    uint256 totalSupplyAfter = getTotalSupply(currentEpochId, vault);
    uint256 sharesAfter = getShares(currentEpochId, vault, to);

    assert totalSupplyBefore + amount == totalSupplyAfter;
    assert sharesBefore + amount == sharesAfter;
    assert to != 0, "Input validation should cut off path wtih `to == address(0)` ";
}

// STATUS - ISSUE. RULE FAILS
// @note - This rule fails because addRewards() function has wrong argument order
rule addRewardsUnitTest(env e, uint256[] epochIds, address[] tokens, address[] vaults, uint256[] amounts) {
    storage initialStorage = lastStorage;
    addReward(e, epochIds[0], vaults[0], tokens[0], amounts[0]); // this should fail because arguments are switched
    uint256 firstAddRewardResult = getRewards(epochIds[0], vaults[0], tokens[0]);

    addRewards(e, epochIds, tokens, vaults, amounts) at initialStorage;
    uint256 secondAddRewardResult = getRewards(epochIds[0], vaults[0], tokens[0]);

    assert firstAddRewardResult == secondAddRewardResult;
}
