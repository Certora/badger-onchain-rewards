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
	getRewards(uint256, address, address) returns(uint256) envfree
	
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
	requireNoDuplicates(address) envfree
	min(uint256, uint256) returns(uint256) envfree
	tokenBalanceOf(address, address) returns(uint256) envfree
    contractTokenBalance(address) returns(uint256) envfree
    contractAddress() returns(address) envfree
}

invariant epochZero_NotExists()
    getEpochsEndTimestamp(0) == 0 && getEpochsStartTimestamp(0) == 0

// check correctness of startNextEpoch() method
rule startNextEpochCheck() {
	uint256 currentEpochBefore = currentEpoch();
	
	env e;
	startNextEpoch(e);
	
	uint256 currentEpochAfter = currentEpoch();
	assert currentEpochAfter == currentEpochBefore + 1;
	
	uint256 epochStartAfter = getEpochsStartTimestamp(currentEpochAfter);
	uint256 epochEndAfter = getEpochsEndTimestamp(currentEpochAfter);
	
	assert epochStartAfter == e.block.timestamp, "wrong start";
	assert epochEndAfter == e.block.timestamp + SECONDS_PER_EPOCH(), "wrong end";
}

rule noOverlappingEpochs() {
	env e;
	startNextEpoch(e);
	uint256 firstEpochEnd = getEpochsEndTimestamp(currentEpoch());
	startNextEpoch(e);
	uint256 secondEpochStart = getEpochsStartTimestamp(currentEpoch());
	assert secondEpochStart > firstEpochEnd;
}

invariant shares_LE_totalSupply(uint256 epochId, address vault, address user)
	getShares(epochId, vault, user) <= getTotalSupply(epochId, vault)
	{
		preserved notifyTransfer(address from, address to, uint256 amount) with(env e) {
			// @note preventing false negative caused by havocing
			require e.msg.sender == vault &&(from == user || to == user)
				&&
				getShares(epochId, vault, from) + getShares(epochId, vault, to) <= getTotalSupply(epochId, vault);
		}
		
		preserved handleTransfer(address v, address from, address to, uint256 amount) with(env e) {
			// @note preventing false negative caused by havocing
			require v == vault => getTotalSupply(epochId, v) >= getShares(epochId, v, from) + getShares(epochId, v, to);
		}
		
		preserved handleWithdrawal(address v, address to, uint256 amount) with(env e) {
			// @note preventing false negative caused by havocing
			require(v == vault && to != user) => getTotalSupply(epochId, v) >= getShares(epochId, v, user) + getShares(epochId, v, to);
		}
	}

rule pointsWithdrawn_LE_points(method f, uint256 epochId, address vault, address user, address token)
filtered {
	f -> f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector
}
{
	require getPointsWithdrawn(epochId, vault, user, token) <= getPoints(epochId, vault, user);
	env e;
	calldataarg args;
	f(e, args);
	assert getPointsWithdrawn(epochId, vault, user, token) <= getPoints(epochId, vault, user);
}

rule lastAccruedTimestamp_updated(uint256 epochId, address vault) {
	env e;
	accrueVault(e, epochId, vault);
	assert getLastAccruedTimestamp(epochId, vault) == e.block.timestamp;
}

rule accreuVault_idempotent(uint256 epochId, address vault) {
	env e;
	accrueVault(e, epochId, vault);
	uint256 totalPointsAfterFirstAccruement = getTotalPoints(epochId, vault);
	accrueVault(e, epochId, vault);
	uint256 totalPointsAfterSecondAccruement = getTotalPoints(epochId, vault);
	assert totalPointsAfterFirstAccruement == totalPointsAfterSecondAccruement;
}

invariant epochTimestamps_BothZero_or_SECONDS_PER_EPOCH_apart(uint256 epochId)
    getEpochsStartTimestamp(epochId) == 0 && getEpochsEndTimestamp(epochId) == 0 || getEpochsStartTimestamp(epochId) + SECONDS_PER_EPOCH() == getEpochsEndTimestamp(epochId)

invariant timeLeftToAccrure_is_Zero_at_NonExistingEpoch(env e, uint256 epochId, address vault)
	epochId > currentEpoch() => getVaultTimeLeftToAccrue(e, epochId, vault) == 0

rule timeLeftToAccure_Zero_After_Accruement(uint256 epochId, address vault) {
    env e;
    accrueVault(e, epochId, vault);
    assert getVaultTimeLeftToAccrue(e, epochId, vault) == 0;
}

rule userTimeLeftToAccrue_Zero_After_Accruement(uint256 epochId, address vault, address user) {
    env e;
    accrueUser(e, epochId, vault, user);
    assert getUserTimeLeftToAccrue(e, epochId, vault, user) == 0;
}

rule shares_totalSupply_Increase_After_Deposit(address vault, address user, uint256 amount) {
    uint256 epochId = currentEpoch();
    uint256 sharesBefore = getShares(epochId, vault, user);
    uint256 totalSupplyBefore = getTotalSupply(epochId, vault);

    env e;
    handleDeposit(e, vault, user, amount);

    uint256 sharesAfter = getShares(epochId, vault, user);
    uint256 totalSupplyAfter = getTotalSupply(epochId, vault);

    assert sharesAfter == sharesBefore + amount;
    assert totalSupplyAfter == totalSupplyBefore + amount;
}

rule shares_totalSupply_Decrease_After_Withdrawal(address vault, address user, uint256 amount) {
    uint256 epochId = currentEpoch();
    uint256 sharesBefore = getShares(epochId, vault, user);
    uint256 totalSupplyBefore = getTotalSupply(epochId, vault);

    env e;
    handleWithdrawal(e, vault, user, amount);

    uint256 sharesAfter = getShares(epochId, vault, user);
    uint256 totalSupplyAfter = getTotalSupply(epochId, vault);

    assert sharesAfter == sharesBefore - amount;
    assert totalSupplyAfter == totalSupplyBefore - amount;
}

rule shares_totalSupply_Check_After_Transfer(address vault, address from, address to, uint256 amount) {
    uint256 epochId = currentEpoch();
    uint256 fromSharesBefore = getShares(epochId, vault, from);
    uint256 toSharesBefore = getShares(epochId, vault, to);
    uint256 totalSupplyBefore = getTotalSupply(epochId, vault);

    env e;
    handleTransfer(e, vault, from, to, amount);

    uint256 fromSharesAfter = getShares(epochId, vault, from);
    uint256 toSharesAfter = getShares(epochId, vault, to);
    uint256 totalSupplyAfter = getTotalSupply(epochId, vault);

    assert from != to => (fromSharesAfter == fromSharesBefore - amount && toSharesAfter == toSharesBefore + amount);
    assert from == to => fromSharesAfter == fromSharesBefore && toSharesAfter == toSharesBefore;
    assert totalSupplyAfter == totalSupplyBefore;
}

rule addRewardCheck(uint256 epochId, address vault, address token, uint256 amount) {
    uint256 rewardsBefore = getRewards(epochId, vault, token);
    uint256 tokenBalanceBefore = contractTokenBalance(token);

    env e;
    require e.msg.sender != contractAddress();
    addReward(e, epochId, vault, token, amount);

    uint256 rewardsAfter = getRewards(epochId, vault, token);
    uint256 tokenBalanceAfter = contractTokenBalance(token);

    assert rewardsAfter == rewardsBefore + amount;
    assert tokenBalanceAfter == tokenBalanceBefore + amount;
}

rule addRewardRevert_at_EpochZero(uint epochId, address vault, address token, uint256 amount) {
    env e;
    addReward@withrevert(e, epochId, vault, token, amount);
    assert epochId == 0 => lastReverted;
}