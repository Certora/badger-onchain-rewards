import "erc20.spec"

methods {
    // constants
    SECONDS_PER_EPOCH() returns(uint256) envfree
    MAX_BPS() returns(uint256) envfree
    PRECISION() returns (uint256) envfree;

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

pointsWithdrawn[epochId][vault][user][token] <= points[epochId][vault][user]
*/
rule pointsWithdrawnCanBeOnlyLowerOrEqualThanPoints(method f, uint256 epochId, address vault, address user, address token)
filtered {
    f -> f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256,uint256,address,address[]).selector
}
{
    env e;
    calldataarg args;

    require getPointsWithdrawn(epochId, vault, user, token) <= getPoints(epochId, vault, user);
    f(e, args);
    assert getPointsWithdrawn(epochId, vault, user, token) <= getPoints(epochId, vault, user), "more pointsWithdrawn than points";
}

/*
STATUS - VERIFIED

totalSupply[epochId][vault] == sum(shares[epochId][vault][user])
*/
ghost getSharesSum(uint256, address) returns uint256 {
    init_state axiom forall uint256 epochId. forall address vault. getSharesSum(epochId, vault) == 0;
}
hook Sstore shares[KEY uint256 epochId][KEY address vaultAddress][KEY address userAddress] uint256 value(uint256 old_value) STORAGE {
    havoc getSharesSum assuming forall uint256 epoch. forall address vault.
        (epoch == epochId && vault == vaultAddress) ? 
            getSharesSum@new(epoch, vault) == getSharesSum@old(epoch, vault) + value - old_value :
            getSharesSum@new(epoch, vault) == getSharesSum@old(epoch, vault);
}

invariant totalSupplyEqualToSumOfShares(uint256 epochId, address vault)
    getTotalSupply(epochId, vault) == getSharesSum(epochId, vault)

