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

/*
STATUS - VERIFIED

Unit Test - addRewards(uint256[] calldata epochIds, address[] calldata tokens, address[] calldata vaults, uint256[] calldata amounts)
Checking the correctness of adding rewards

DISCOVERED ISSUE:
- addRewards incorrectly passes arguments to addReward function. Vault address and token address are swapped which leads to rewards being added to wrong address.
*/
rule unitTestAddRewards(uint256[] epochIds, address[] tokens, address[] vaults, uint256[] amounts) {
    env e;

    require epochIds.length == 1;
    require tokens.length == 1;
    require vaults.length == 1;

    require e.msg.sender != currentContract;
    require vaults[0] != tokens[0];

    uint256 rewardsBefore = getRewards(epochIds[0], vaults[0], tokens[0]);

    addRewards(e, epochIds, tokens, vaults, amounts);

    uint256 rewardsAfter = getRewards(epochIds[0], vaults[0], tokens[0]);

    assert rewardsAfter == rewardsBefore + amounts[0], "failed to add rewards first element";
}

/*
STATUS - VERIFIED

Unit Test - addReward(int256 epochId, address vault, address token, uint256 amount)
Checking the correctness of adding reward:
- transfering amount of tokens to the contract
- adding rewards
- rejecting attempt to add 0 tokens

DISCOVERED ISSUE:
- no check that amount > 0 - it is possible to addReward with amount equal to 0, which basically ends up with wasting gas on transaction that does not change the state of the contract
*/
rule unitTestAddRewardRejectZeroAmount(uint256 epochId, address vault, address token, uint256 amount) {
    env e;

    require e.msg.sender != currentContract;

    addReward(e, epochId, vault, token, amount);

    assert amount > 0, "failed to reject amount 0";
}

/*
STATUS - VERIFIED
Unit Test notifyTransfer(address from, address to, uint256 amount) - transfer path

Checking the correctness of notifying transfer:
- user `from` shares are decreased by `amount`
- user `to` shares are increased by `amount`

DISCOVERED ISSUE:
- no check that from != to - it is possible to notify that tokens were transferred from address A to address A which basically ends up with wasting gas on transaction that does not change the state of the contract
*/
rule unitTestNotifyTransferTransferPath(address vault, address from, address to, uint256 amount) {
    env e;

    require from != 0 && to != 0;
    require vault == e.msg.sender;

    uint256 currentEpoch = currentEpoch();

    uint256 sharesFromBefore = getShares(currentEpoch, vault, from); 
    uint256 sharesToBefore = getShares(currentEpoch, vault, to); 
    uint256 totalSupplyBefore = getTotalSupply(currentEpoch, vault);

    notifyTransfer(e, from, to, amount);

    uint256 sharesFromAfter = getShares(currentEpoch,vault, from); 
    uint256 sharesToAfter = getShares(currentEpoch,vault, to); 
    uint256 totalSupplyAfter = getTotalSupply(currentEpoch, vault);

    assert sharesFromAfter == sharesFromBefore - amount, "failed to decrease from shares by amount";
    assert sharesToAfter == sharesToBefore + amount, "failed to increase to shares by amount";
    assert totalSupplyAfter == totalSupplyBefore, "failed should not change total supply";
}

/*
STATUS - VERIFIED
Unit Test notifyTransfer(address from, address to, uint256 amount) - transfer path

Checking the correctness of notifying transfer:
- rejecting attempt to notify transfer of 0 tokens 

DISCOVERED ISSUE:
- no check that amount > 0 - it is possible to notify that 0 tokens were transferred which basically ends up with wasting gas on transaction that does not change the state of the contract
*/
rule unitTestNotifyTransferTransferPathRejectZeroAmount(address vault, address from, address to, uint256 amount) {
    env e;

    require from != 0 && to != 0;

    notifyTransfer(e, from, to, amount);

    assert amount > 0, "failed should reject amount 0";
}

/*
STATUS - VERIFIED

Unit Test notifyTransfer(address from, address to, uint256 amount) - deposit path
Checking the correctness of depositing:
- rejecting attempt to notify deposit of 0 tokens

DISCOVERED ISSUE:
- no check that amount > 0 - it is possible to notify that 0 tokens were deposited which basically ends up with wasting gas on transaction that does not change the state of the contract
*/
rule unitTestNotifyTransferDepositPathRejectZeroAmount(address vault, address from, address to, uint256 amount) {
    env e;

    require from == 0;

    notifyTransfer(e, from, to, amount);

    assert amount > 0, "should reject amount 0";
}

/*
STATUS - VERIFIED

Unit Test notifyTransfer(address from, address to, uint256 amount) - withdrawal path
Checking the correctness of notifying withdrawal:
- rejecting attempt to notify withdrawal of 0 tokens 

ISSUES:
- no check that amount > 0 - it is possible to notify that 0 tokens were withdrawn which basically ends up with wasting gas on transaction that does not change the state of the contract
*/
rule unitTestNotifyTransferWithdrawalPathRejectZeroAmount(address vault, address from, address to, uint256 amount) {
    env e;

    require from != 0 && to == 0;

    notifyTransfer(e, from, to, amount);

    assert amount > 0, "should reject amount 0";
}
