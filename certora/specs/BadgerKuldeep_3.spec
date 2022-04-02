import "base.spec"

// acrrue vault, accrue vault, claim related properties here

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
        || (lastTimeAccruedAfterAccrue == lastTimeAccruedBeforeAccrue => timeLeftToAccue == 0), "last timestamp for vault accrue not updated properly";
    assert lastTimeAccruedAfterAccrue == e.block.timestamp, "last timestamp for vault accrue is incorrect";
    assert (totalPointAfterAccrue > totalPointBeforeAccrue)
     || (totalPointAfterAccrue == totalPointBeforeAccrue => (timeLeftToAccue == 0 || supply == 0)), "total points after vault accrue not updated properly";

}

// verified
rule accrue_vault_can_not_after_epoch_end() {
    env e;
    uint256 epochId = currentEpoch();
    address vault;

    require epochId <= currentEpoch();

    // require getEpochsEndTimestamp(epochId) < e.block.timestamp;
    require getLastAccruedTimestamp(epochId,vault) >=  getEpochsEndTimestamp(epochId);

    uint256 totalPointBeforeAccrue = getTotalPoints(epochId, vault);
    accrueVault(e,epochId,vault);

    uint256 totalPointAfterAccrue = getTotalPoints(epochId, vault);

    assert totalPointAfterAccrue == totalPointBeforeAccrue, "accrue vault after epoch end";
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
        || (lastTimeUserAccruedAfterAccrue == lastTimeUserAccruedBeforeAccrue => timeInEpochSinceLastAccrue == 0), "last timestamp for user accrue not updated properly";
    assert lastTimeUserAccruedAfterAccrue == e.block.timestamp, "last timestamp for user accrue value incorrect";
    assert  (userPointAfterAccrue > userPointBeforeAccrue)
     || (userPointAfterAccrue == userPointBeforeAccrue => (timeInEpochSinceLastAccrue == 0 || currentBalance == 0)), "user points not updated properly after accrue";

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
    ).selector, "contract balance got reduced without claim";
}

// unit test
// verified
rule user_claiming_reward() {
    env e;
    uint256 epochId;
    address vault;
    address token;
    address user;

    require user != currentContract;
    require epochId > 0 && epochId <= currentEpoch();
    
    uint256 userPointsBefore = getPoints(epochId,vault, user);
    uint256 userPointsWithdrawmBeforeClaim = getPointsWithdrawn(epochId, vault, user, token);
    uint256 userTokenBalanceBefore = tokenBalanceOf(token, user);

    claimReward(e,epochId,vault,token,user);

    uint256 userPointsAfter = getPoints(epochId,vault, user);
    uint256 userPointsWithdrawmAfterClaim = getPointsWithdrawn(epochId, vault, user, token);
    uint256 userTokenBalanceAfter = tokenBalanceOf(token, user);

    assert userPointsWithdrawmAfterClaim > userPointsWithdrawmBeforeClaim 
     || (userPointsWithdrawmAfterClaim == userPointsWithdrawmBeforeClaim => (userPointsAfter == userPointsWithdrawmAfterClaim )) , "user points withdrawn should increase";
    assert userTokenBalanceAfter > userTokenBalanceBefore
     || (userTokenBalanceAfter == userTokenBalanceBefore => (userPointsAfter == userPointsWithdrawmAfterClaim)) , "user token balance should increase"; 
}

