import "base.spec"

// rule accrue_vault_can_not_after_epoch_end() {
//     env e;
//     uint256 epochId;
//     require epochId < currentEpoch();
//     address vault;

//     require e.block.timestamp 
// }

// unit test
// verified
rule accrue_vault_work_as_expected() {
    env e;
    uint256 epochId;
    address vault;

    require epochId <= currentEpoch();

    uint256 totalPointBeforeAccrue = getTotalPoints(epochId, vault);
    uint256 lastTimeAccruedBeforeAccrue = getLastAccruedTimestamp(epochId, vault);

    uint256 timeLeftToAccue = getVaultTimeLeftToAccrue(e, epochId,vault);
    uint256 supply;
    bool shouldUpdate;

    supply,shouldUpdate  = getTotalSupplyAtEpoch(epochId, vault);

    accrueVault(e,epochId,vault);

    uint256 totalPointAfterAccrue = getTotalPoints(epochId, vault);
    uint256 lastTimeAccruedAfterAccrue = getLastAccruedTimestamp(epochId, vault);

    assert (lastTimeAccruedAfterAccrue > lastTimeAccruedBeforeAccrue)
        || (lastTimeAccruedAfterAccrue == lastTimeAccruedBeforeAccrue => timeLeftToAccue == 0);
    assert lastTimeAccruedAfterAccrue == e.block.timestamp;
    assert (totalPointAfterAccrue > totalPointBeforeAccrue)
     || (totalPointAfterAccrue == totalPointBeforeAccrue => (timeLeftToAccue == 0 || supply == 0));

}


// unit test
// verified
rule accrue_user_work_as_expected() {
    env e;
    uint256 epochId;
    address vault;
    address user;

    require epochId <= currentEpoch();

    uint256 userPointBeforeAccrue = getPoints(epochId, vault, user);
    uint256 lastTimeUserAccruedBeforeAccrue = getLastUserAccrueTimestamp(epochId, vault, user);

    uint256 timeInEpochSinceLastAccrue = getUserTimeLeftToAccrue(e, epochId,vault, user);
    uint256 currentBalance;
    bool shouldUpdate;

    currentBalance,shouldUpdate  = getBalanceAtEpoch(epochId, vault, user);

    accrueUser(e,epochId,vault, user);

    uint256 userPointAfterAccrue = getPoints(epochId, vault, user);
    uint256 lastTimeUserAccruedAfterAccrue = getLastUserAccrueTimestamp(epochId, vault, user);

    assert (lastTimeUserAccruedAfterAccrue > lastTimeUserAccruedBeforeAccrue)
        || (lastTimeUserAccruedAfterAccrue == lastTimeUserAccruedBeforeAccrue => timeInEpochSinceLastAccrue == 0);
    assert lastTimeUserAccruedAfterAccrue == e.block.timestamp;
    assert  (userPointAfterAccrue > userPointBeforeAccrue)
     || (userPointAfterAccrue == userPointBeforeAccrue => (timeInEpochSinceLastAccrue == 0 || currentBalance == 0));

}

// variable transition
// verified
rule reward_token_balance_decrease_only_from_claiming(method f) {
    env e;
    calldataarg args;
    address token;
    
    uint256 tokenBalanceBefore = tokenBalanceOf(token, currentContract);

    f(e,args);

    uint256 tokenBalanceAfter = tokenBalanceOf(token, currentContract);

    assert (tokenBalanceAfter < tokenBalanceBefore) => 
        f.selector == claimRewards(
        uint256[],
        address[],
        address[],
        address[]
    ).selector ||
        f.selector == claimReward(
        uint256,
        address,
        address,
        address
    ).selector ||
        f.selector == claimBulkTokensOverMultipleEpochs(
        uint256,
        uint256,
        address,
        address[],
        address
    ).selector ||
        f.selector == claimBulkTokensOverMultipleEpochsOptimized(
        uint256,
        uint256,
        address,
        address[]
    ).selector;
}

