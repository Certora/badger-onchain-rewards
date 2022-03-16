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
	addRewards(uint256, address, address, uint256)
	addReward(uint256, address, address, uint256)
	notifyTransfer(address, address, uint256)
	accrueUser(uint256, address, address)
	getUserTimeLeftToAccrue(uint256, address, address) returns(uint256)
	claimRewards(uint256, address, address, address)
	claimReward(uint256, address, address, address)
	claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address, address)
	handleDeposit(address, address, uint256)
	handleWithdrawal(address, address, uint256)
	handleTransfer(address, address, address, uint256)
	
	// envfree methods
	getTotalSupplyAtEpoch(uint256, address) returns(uint256, bool) envfree
	getBalanceAtEpoch(uint256, address, address) returns(uint256, bool) envfree
	requireNoDuplicates(address) envfree
	min(uint256, uint256) returns(uint256) envfree
	tokenBalanceOf(address, address) returns(uint256) envfree
}

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
