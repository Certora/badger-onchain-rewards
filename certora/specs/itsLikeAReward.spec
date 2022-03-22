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

// STATUS - verified
// check correctness of startNextEpoch() method
rule startNextEpochCheck(method f, env e){
    uint256 epochId = to_uint256(currentEpoch() + 1);

    startNextEpoch(e);

    uint256 epochStartAfter = getEpochsStartTimestamp(epochId);
    uint256 epochEndAfter = getEpochsEndTimestamp(epochId);

    assert epochStartAfter == e.block.timestamp, "wrong start";
    assert epochEndAfter == e.block.timestamp + SECONDS_PER_EPOCH(), "wrong end";
}


// get the list of functions which can change user's balance (It's not a rule that we usually use in real verification, more as a code example)
rule whoChangedMyBalance(address token, address user, method f) filtered {f -> !f.isView && f.selector != accrueVault(uint256, address).selector} {
    uint256 before = tokenBalanceOf(token,user);

    env e;
    calldataarg args;
    f(e,args);

    assert tokenBalanceOf(token,user) == before;
}


// check if any function can change balances in different tokens (hint: there will be different results with --loop_iter 1 and 2. Try to undesrtand the reason), due to claimRewards which allows changing multiple tokens with a loop
rule canAnyFunctionChangeMoreThanOneToken(address token1, address token2, address user, method f) {
    require token1!=token2;

    uint256 before1 = tokenBalanceOf(token1,user);
    uint256 before2 = tokenBalanceOf(token2,user);
    
    env e;
    calldataarg args;
    f(e,args);

    assert tokenBalanceOf(token1,user) == before1 || tokenBalanceOf(token2,user) == before2;
}


// total shares greater than sum of all shares 
// STATUS - verfied
ghost sum_all_shares(uint256, address) returns uint {
    init_state axiom forall uint256 epoch. forall address vault. sum_all_shares(epoch, vault) == 0;
}

hook Sstore shares[KEY uint256 epoch][KEY address vault][KEY address user]
    uint256 shares
    (uint256 old_shares) STORAGE {
        // sum_all_points can be any state as long as 
        havoc sum_all_shares assuming forall uint256 e. forall address v. ((epoch == e && vault == v) => sum_all_shares@new(e, v) == sum_all_shares@old(e, v) - old_shares + shares) && ((epoch != e || vault != v) => sum_all_shares@new(e, v) == sum_all_shares@old(e, v));
    }

// Total shares should be greater than sum of all users' shares.
// STATUS - valid
invariant total_shares_gte_sum_all_shares(uint256 epoch, address vault)
    getTotalSupply(epoch, vault) >= sum_all_shares(epoch, vault)
