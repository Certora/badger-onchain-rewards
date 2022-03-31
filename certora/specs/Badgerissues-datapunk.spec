// Issues discovered

import "erc20.spec"
import "rewardsManagerMethods.spec"

using DummyERC20A as tokenA
using DummyERC20B as tokenB

/*
  Rule: addReward function should be additive 
  Property: High level 
  Explanation: All things being equal, the same total amount of tokens added into a vault through addReward should result in the same amount of rewards, whether it is done in one call or multiple calls
  Priority: High
  Justification: if this rule fails, it means that addReward() and addRewards() are inconsistent
*/
// ******** IMPORTANT: This rule discovers a bug *********
// addRewards has token and vault variables reversed compared to addReward. When addRewards relays to addReward, the order is not corrected either
// Fix: addReward(epochIds[i], vaults[i], tokens[i], amounts[i]) and/or change addRewards parameter order as well
rule test_addRewards(uint256 epochId, address vault, address token, uint256 amt1, uint256 amt2) {
  env e1;
  env e2;
  require e1.msg.sender != currentContract && e2.msg.sender != currentContract;  
  // require vault != token;
  uint256[] epochIds; require epochIds.length==2; require epochIds[0]==epochId; require epochIds[1]==epochId;
  address[] vaults; require vaults.length==2; require vaults[0]==vault; require vaults[1]==vault; 
  address[] tokens; require tokens.length==2; require tokens[0]==token; require tokens[1]==token; 
  uint256[] amounts; require amounts.length==2; require amounts[0]==amt1; require amounts[1]==amt2;

  storage init = lastStorage;
  addReward(e1, epochId, vault, token, amt1);
  addReward(e2, epochId, vault, token, amt2);
  uint256 reward_1_2 = getRewards(epochId, vault, token);
  uint256 balance_1_2 = tokenBalanceOf(token, currentContract);

  addRewards(e1, epochIds, tokens, vaults, amounts) at init;
  uint256 reward_sum = getRewards(epochId, vault, token);
  uint256 balance_sum = tokenBalanceOf(token, currentContract);
  assert reward_1_2 == reward_sum;  
  assert balance_1_2 == balance_sum;  
}

/*
  Rule: check notifyTransfer and its related functions
  Property: Unit test 
  Explanation: All things being equal, the same total amount of tokens added into a vault through addReward should result in the same amount of rewards, whether it is done in one call or multiple calls
  Priority: High
  Justification: if this rule fails, it means that one can arbitrage the rewards in a vault
*/
// ******** IMPORTANT: This rule discovers a bug *********
// When both "from" and "to" equal to 0, the code flows to the _handleDeposit branch, which would inflate totalSupply.
// Fix: add require (from!=to); at the top, which has the side benefit of saving gas

rule test_notifyTransfer(uint256 epochId, address vault, address token, address from, address to, uint256 amount) {
    env e;
    require vault == e.msg.sender; 
    require epochId == currentEpoch();
    uint256 _sharesFrom = getShares(epochId, vault, from);
    uint256 _sharesTo = getShares(epochId, vault, to);
    uint256 _totalSupply = getTotalSupply(epochId, vault);
    require _sharesFrom <= _totalSupply && _sharesTo <= _totalSupply;    
    uint256 _lastUserAccrueTimestampFrom = getLastUserAccrueTimestamp(epochId, vault, from);
    uint256 _lastUserAccrueTimestampTo = getLastUserAccrueTimestamp(epochId, vault, to);
    require _lastUserAccrueTimestampFrom == 0 => _sharesFrom == 0;
    require _lastUserAccrueTimestampTo == 0 => _sharesTo == 0;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId, vault);
    require _lastAccruedTimestamp == 0 => _totalSupply==0;
    require e.block.timestamp >= _lastUserAccrueTimestampFrom && e.block.timestamp >= _lastUserAccrueTimestampTo && e.block.timestamp >= _lastAccruedTimestamp;

    notifyTransfer(e, from, to, amount);
    uint256 sharesFrom_ = getShares(epochId, vault, from);
    uint256 sharesTo_ = getShares(epochId, vault, to);
    uint256 totalSupply_ = getTotalSupply(epochId, vault);

    if (from==0) { // this should NOT be for (from==0 && to==0) 
      assert getLastAccruedTimestamp(epochId, vault) == getLastUserAccrueTimestamp(epochId, vault, to);            
      assert _lastUserAccrueTimestampTo != 0 ? _sharesTo + amount == sharesTo_ : to_uint256(_sharesTo + amount) <= sharesTo_ ;
      assert _lastAccruedTimestamp != 0 ? _totalSupply + amount == totalSupply_ : to_uint256(_totalSupply + amount) <= totalSupply_;
    } else if (to == 0) {
      assert getLastAccruedTimestamp(epochId, vault) == getLastUserAccrueTimestamp(epochId, vault, from);
      assert _lastUserAccrueTimestampFrom != 0 ? _sharesFrom == sharesFrom_  + amount: _sharesFrom <= sharesFrom_ + amount;
      assert _lastAccruedTimestamp != 0 ? _totalSupply == totalSupply_ + amount: _totalSupply <= totalSupply_ + amount;
    } else { // this should be for ((from==0 && to==0) || (from!=0 && to!=0))
      assert getLastUserAccrueTimestamp(epochId, vault, from) == getLastUserAccrueTimestamp(epochId, vault, to);
      assert _lastUserAccrueTimestampTo != 0 ? _sharesTo + amount == sharesTo_ : _sharesTo + amount <= sharesTo_ ;
      assert _lastUserAccrueTimestampFrom != 0 ? _sharesFrom == sharesFrom_ + amount : _sharesFrom <= sharesFrom_ + amount;
      assert _lastAccruedTimestamp == getLastAccruedTimestamp(epochId, vault) && _totalSupply == totalSupply_;
    } 
}

// This Badger contract is missing zero address in many places. This is one example where it should be checked and reverted
rule test_accrueVault_require_vault(uint256 epochId, address vault) {
  env e;
  require e.msg.value != 0;
  require epochId <= currentEpoch();
  accrueVault@withrevert(e, epochId, vault);
  assert vault==0 => lastReverted, "can accrue only before or current epoch";
  assert false;
}

/*
  Rule: addReward at epoch 0 should fail
  Property: High level 
  Explanation: When addReward() is called before the first startNextEpoch() call, reward will be locked. The endTimestamp of epoch 0 is 0, which makes it impossible to accrue points, thus not claimReward can be done. Also there is no sweeping function in this contract
  Priority: High
  Justification: No fund should ever be locked in contract.
*/
rule test_addReward_at_EpochZero(uint epochId, address vault, address token, uint256 amount) {
    env e;
    addReward@withrevert(e, epochId, vault, token, amount);
    assert epochId == 0 => lastReverted, "adding reward to epoch 0 will result in locked reward";
}

/*
  Rule: Test the sensitivity of claimReward to PRECISION.
  Property: High level 
  Explanation: Since the contract expects any ERC20 token, the decimals is undetermined a priori. While 18 is the standard, we could see different values. This is to test the impact of change in PRECISION
  Priority: Low
  Justification: it turns out even if PRECISION is changed by a factor 10, this rule will fail. This leads one to think if the PRECISION should be defined directly by token.decimal()
*/
rule test_precision(uint256 epochId, address vault, address token, address user) { 
  env e;
  require getLastAccruedTimestamp(epochId, vault) == getLastUserAccrueTimestamp(epochId, vault, user);
  require getLastAccruedTimestamp(epochId, vault) == e.block.timestamp;
  require getPoints(epochId, vault, user) <= getTotalPoints(epochId, vault);
  require getPointsWithdrawn(epochId, vault, user, token) <= getPoints(epochId, vault, user);
  require user != currentContract;
  require getRewards(epochId, vault, token) != 0;
  require getPoints(epochId, vault, user) != 0;

  uint256 _actual = tokenBalanceOf(token, user);
  uint256 PRECISION = 10000000000000000000; //1e19 instead of 1e18

  uint256 pointsLeft = getPoints(epochId, vault, user) - getPointsWithdrawn(epochId, vault, user, token);
  uint256 ratioForPointsLeft = PRECISION * pointsLeft / getTotalPoints(epochId, vault);
  uint256 expectedReward = getRewards(epochId, vault, token) * ratioForPointsLeft / PRECISION;

  claimReward(e, epochId, vault, token, user);

  uint256 actual_ = tokenBalanceOf(token, user);
  assert (actual_-_actual == expectedReward);
}
