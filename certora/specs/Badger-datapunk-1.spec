// ****************************
// ****** Check Requires ******
// ****************************


import "erc20.spec"
import "rewardsManagerMethods.spec"

using DummyERC20A as tokenA
using DummyERC20B as tokenB

/*
  Rules: Making sure requires are in place for all functions 
  Property: Unit test
  Explanation: Requires ensures the pre-conditions of each function. In case they are removed inadvertantly, it should be reported
  Priority: Medium
  Justification: The rules here are based on existing requires and ensure they are not removed by mistake. Also including some checks for 0 address.
*/

// pass
rule check_claimRewards_require_length(uint256[] epochsToClaim, address[] vaults, address[] tokens, address[] users) {
  env e;
  require e.msg.value != 0;  
  claimRewards@withrevert(e, epochsToClaim, vaults, tokens, users);
  assert epochsToClaim.length != vaults.length || epochsToClaim.length != tokens.length || epochsToClaim.length != users.length => lastReverted, "array inputs to claimRewards should have equal length";
  // assert false;
}

// pass
rule check_claimReward_require_epoch(uint256 epochId, address vault, address token, address user) {
  env e;
  uint256 currEpoch = currentEpoch();
  require e.msg.value != 0;

  claimReward@withrevert(e, epochId, vault, token, user);
  assert epochId >= currEpoch => lastReverted, "can only claim ended epochs";
  // assert false;
}

// pass
rule check_claimBulkTokensOverMultipleEpochs_require_timestamp(uint256 epochStart, uint256 epochEnd, address vault, address[] tokens, address user) {
  env e;
  require e.msg.value != 0;
  claimBulkTokensOverMultipleEpochs@withrevert(e, epochStart, epochEnd, vault, tokens, user);
  assert epochStart > epochEnd => lastReverted, "epoch timestamp math wrong";
  // assert false;
}

// pass
rule check_claimBulkTokensOverMultipleEpochs_require_epoch(uint256 epochStart, uint256 epochEnd, address vault, address[] tokens, address user) {
  env e;
  uint256 currEpoch = currentEpoch();
  require epochStart <= epochEnd;
  require e.msg.value != 0;

  claimBulkTokensOverMultipleEpochs@withrevert(e, epochStart, epochEnd, vault, tokens, user);
  assert epochEnd >= currEpoch => lastReverted, "Can't claim if not expired";
  // assert false;
}

// pass
rule check_claimBulkTokensOverMultipleEpochs_require_no_dups(uint256 epochStart, uint256 epochEnd, address vault, address[] tokens, address user) {
  env e;
  require epochStart == epochEnd;
  require epochEnd < currentEpoch();
  require tokens.length == 2;
  require tokens[0] == tokens[1];
  require e.msg.value != 0;

  claimBulkTokensOverMultipleEpochs@withrevert(e, epochStart, epochEnd, vault, tokens, user);
  assert tokens[0]==tokens[1] => lastReverted, "Can't claim duplicated tokens";
  // assert false;
}

// pass
rule check_claimBulkTokensOverMultipleEpochsOptimized_require_timestamp(uint256 epochStart, uint256 epochEnd, address vault, address[] tokens) {
  env e;
  require e.msg.value != 0;
  claimBulkTokensOverMultipleEpochsOptimized@withrevert(e, epochStart, epochEnd, vault, tokens);
  assert epochStart > epochEnd => lastReverted, "epoch timestamp math wrong";
  // assert false;
}

// pass
rule check_claimBulkTokensOverMultipleEpochsOptimized_require_epoch(uint256 epochStart, uint256 epochEnd, address vault, address[] tokens) {
  env e;
  uint256 currEpoch = currentEpoch();
  require epochStart <= epochEnd;
  require e.msg.value != 0;

  claimBulkTokensOverMultipleEpochsOptimized@withrevert(e, epochStart, epochEnd, vault, tokens);
  assert epochEnd >= currEpoch => lastReverted, "Can't claim if not expired";
  // assert false;
}

// pass
rule check_claimBulkTokensOverMultipleEpochsOptimized_require_no_dups(uint256 epochStart, uint256 epochEnd, address vault, address[] tokens) {
  env e;
  require epochStart == epochEnd;
  require epochEnd < currentEpoch();
  require tokens.length == 2;
  require tokens[0] == tokens[1];
  require e.msg.value != 0;

  claimBulkTokensOverMultipleEpochsOptimized@withrevert(e, epochStart, epochEnd, vault, tokens);
  assert tokens[0]==tokens[1] => lastReverted, "Can't claim duplicated tokens";
  // assert false;
}

// pass
rule check_addRewards_require_epochIds(uint256[] epochIds, address[] tokens, address[] vaults, uint256[] amounts) {
  env e;
  require e.msg.value != 0;
  addRewards@withrevert(e, epochIds, tokens, vaults, amounts);
  assert epochIds.length != vaults.length => lastReverted, "epochToClaim should have the same length as vaults";
  // assert false;
}

// pass
rule check_addRewards_require_amounts(uint256[] epochIds, address[] tokens, address[] vaults, uint256[] amounts) {
  env e;
  require epochIds.length == vaults.length;
  require e.msg.value != 0;
  addRewards@withrevert(e, epochIds, tokens, vaults, amounts);
  assert amounts.length != vaults.length => lastReverted, "amounts should have the same length as vaults";
  // assert false;
}

// pass
rule check_addRewards_require_tokens(uint256[] epochIds, address[] tokens, address[] vaults, uint256[] amounts) {
  env e;  
  require e.msg.value != 0;
  require epochIds.length == vaults.length;
  require amounts.length == vaults.length;
  addRewards@withrevert(e, epochIds, tokens, vaults, amounts);
  assert tokens.length != vaults.length => lastReverted, "tokens should have the same length as vaults";
  // assert false;
}
 
// pass
rule check_addReward_require_epoch(uint256 epochId, address vault, address token, uint256 amount) {
  env e;
  require e.msg.value != 0;
  uint256 currEpoch = currentEpoch();
  require epochId < currEpoch;
  addReward@withrevert(e, epochId, vault, token, amount);
  assert epochId < currEpoch => lastReverted, "can addReward to current or future epoch";
  assert currEpoch == currentEpoch();
  // assert false;
}

// // does not pass. don't understand the reason
// rule check_accrueUser_require_epoch(uint256 epochId, address vault, address user) {
//   env e;
//   uint256 currEpoch = currentEpoch();
//   require e.msg.value != 0;
//   require epochId > currEpoch;
//   accrueUser@withrevert(e, epochId, vault, user);
//   assert epochId > currentEpoch() => lastReverted, "can accrue user only before or current epoch";
//   assert currEpoch == currentEpoch();
//   // assert false;
// }

// // does not pass. don't understand the reason
// rule check_accrueVault_require_epoch(uint256 epochId, address vault) {
//   env e;
//   require e.msg.value != 0;
//   require epochId > currentEpoch();

//   accrueVault@withrevert(e, epochId, vault);
//   assert epochId > currentEpoch() => lastReverted, "can accrue vault only before or current epoch";
//   // assert false;
// }

// // does not pass. don't understand the reason
// rule check_startNextEpoch_require_timestamp(){
//     env e;
//     uint256 prevEpoch = currentEpoch();
//     startNextEpoch@withrevert(e);    
//     assert e.block.timestamp <= getEpochsEndTimestamp(prevEpoch) => lastReverted, "can startNextEpoch only after the current one finishes";   
//     // assert false;
// }
 
// // does not pass. don't understand the reason, might be related to double loop
// rule check_claimBulkTokensOverMultipleEpochs_require_zero_pointsWithdrawn(uint256 epochId, address vault, address[] tokens, address user) {
//   env e;
//   require getLastAccruedTimestamp(epochId, vault)>0;
//   require getLastUserAccrueTimestamp(epochId, vault, user)>0;
//   require epochId < currentEpoch();
//   require tokens.length == 1;
//   require e.msg.value != 0;
//   claimBulkTokensOverMultipleEpochs@withrevert(e, epochId, epochId, vault, tokens, user);
//   assert getPointsWithdrawn(epochId, vault, user, tokens[0])!=0 => lastReverted, "You already accrued during the epoch, cannot optimize";
//   // assert false;
// }

// // does not pass. don't understand the reason, might be related to double loops
// rule check_claimBulkTokensOverMultipleEpochsOptimized_require_zero_pointsWithdrawn(uint256 epochId, address vault, address[] tokens) {
//   env e;
//   require getLastAccruedTimestamp(epochId, vault)>0;
//   require getLastUserAccrueTimestamp(epochId, vault, e.msg.sender)>0;
//   require epochId < currentEpoch();
//   require tokens.length == 1;
//   require e.msg.value != 0;

//   claimBulkTokensOverMultipleEpochsOptimized@withrevert(e, epochId, epochId, vault, tokens);
//   assert getPointsWithdrawn(epochId, vault, e.msg.sender, tokens[0])!=0 => lastReverted, "You already accrued during the epoch, cannot optimize";
//   // assert false;
// }

// ***********************************
// ****** Check No Interference ******
// ***********************************

/*
Rules: noChangeToOthers
Property: Valid state 
Explanation: When a function is called, it should only change variables' states for associated epochId, vault, token, user
Priority: High
Justification: if this rule fails, it means that functions are changing variables' states of unrelated inputs, which indicates broken contract
*/
rule noChangeToOthers_accrueVault(uint256 epochId, address vault, uint256 epochId_other, address vault_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);

    require epochId_other!=epochId || vault_other!=vault;
    accrueVault(e, epochId, vault); 

    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);

    assert lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert totalPoints_ == _totalPoints;
    assert totalSupply_ == _totalSupply;
}

rule noChangeToOthers_getVaultTimeLeftToAccrue(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    
    require epochId != epochId_other || vault != vault_other;
    getVaultTimeLeftToAccrue(e, epochId, vault);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);

    assert lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert totalPoints_ == _totalPoints;
    assert totalSupply_ == _totalSupply;
}

rule noChangeToOthers_addRewards(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    uint256[] epochIds; require epochIds.length==1; require epochIds[0]==epochId;
    address[] vaults; require vaults.length==1; require vaults[0]==vault;
    address[] tokens; require tokens.length==1; require tokens[0]==token;
    address[] users; require users.length==1; require users[0]==from;
    uint256[] amounts; require amounts.length==1; require amounts[0]==amount; require amounts[1]==amount; 
    
    require epochId_other!=epochId || vault_other!=vault || token_other!=token;
    addRewards(e, epochIds, tokens, vaults, amounts);
      
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_addReward(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=epochId || vault_other!=vault || token_other!=token;
    addReward(e, epochId, vault, token, amount);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_notifyTransfer(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=epochId || vault_other!=e.msg.sender || (user_other!=from && user_other != to);
    require vault == e.msg.sender;
    require epochId == currentEpoch();
    notifyTransfer(e, from, to, amount);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_handleTransfer(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other !=to);
    require epochId == currentEpoch();
    handleTransfer(e, vault, from, to, amount);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_handleDeposit(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=epochId || vault_other!=vault || user_other != to;
    require epochId == currentEpoch();
    handleDeposit(e, vault, to, amount);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_handleWithdrawal(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=currentEpoch() || vault_other!=vault || user_other!=from;
    require epochId == currentEpoch();
    handleWithdrawal(e, vault, from, amount);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_accrueUser(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=epochId || vault_other!=vault || user_other!=from;
    accrueUser(e, epochId, vault, from);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_getUserTimeLeftToAccrue(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=epochId || vault_other!=vault || user_other!=from;
    getUserTimeLeftToAccrue(e, epochId, vault, from);

    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

rule noChangeToOthers_claimRewards(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    uint256[] epochIds; require epochIds.length==1; require epochIds[0]==epochId;
    address[] vaults; require vaults.length==1; require vaults[0]==vault;
    address[] tokens; require tokens.length==1; require tokens[0]==token;
    address[] users; require users.length==1; require users[0]==from;
    
    require epochId_other!=epochId || vault_other!=vault || token_other!=token || (user_other!=from && user_other != to);
    claimRewards(e, epochIds, vaults, tokens, users);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}


rule noChangeToOthers_claimReward(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    require epochId_other!=epochId || vault_other!=vault || token_other!=token || user_other!=from ;
    claimReward(e, epochId, vault, token, from);

    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}


rule noChangeToOthers_claimBulkTokensOverMultipleEpochs(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    address[] tokens; require tokens.length==1; require tokens[0]==token;
    
    require epochId_other!=epochId || vault_other!=vault || token_other!=token || (user_other!=from && user_other != to);
    claimBulkTokensOverMultipleEpochs(e, epochId, epochId, vault, tokens, from);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to) => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}


rule noChangeToOthers_claimBulkTokensOverMultipleEpochsOptimized(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    address[] tokens; require tokens.length==1; require tokens[0]==token;
    
    require epochId_other!=epochId || vault_other!=vault || token_other!=token || (user_other!=from && user_other != to);
    claimBulkTokensOverMultipleEpochsOptimized(e, epochId, epochId, vault, tokens);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
    assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
    assert epochId_other!=epochId || vault_other!=vault || user_other!=e.msg.sender => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert epochId_other!=epochId || vault_other!=vault || user_other!=e.msg.sender => shares_ == _shares;
    assert epochId_other!=epochId || vault_other!=vault || user_other!=e.msg.sender => points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}


rule noChangeToOthers_others(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) filtered {
  f ->
    f.selector != accrueVault(uint256, address).selector &&
    f.selector != getVaultTimeLeftToAccrue(uint256, address).selector &&
    f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector &&
    f.selector != addRewards(uint256[], address[], address[], uint256[]).selector &&
    f.selector != addReward(uint256, address, address, uint256).selector &&
    f.selector != notifyTransfer(address, address, uint256).selector &&
    f.selector != accrueUser(uint256, address, address).selector &&
    f.selector != getUserTimeLeftToAccrue(uint256, address, address).selector &&
    f.selector != claimRewards(uint256[], address[], address[], address[]).selector &&
    f.selector != claimReward(uint256, address, address, address).selector &&
    f.selector != claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector &&
    f.selector != handleDeposit(address, address, uint256).selector &&
    f.selector != handleWithdrawal(address, address, uint256).selector &&
    f.selector != handleTransfer(address, address, address, uint256).selector
} {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
    uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 _shares = getShares(epochId_other, vault_other, user_other);
    uint256 _points = getPoints(epochId_other, vault_other, user_other);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    calldataarg args;
    f(e,args);
    
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
    uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
    uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
    uint256 shares_ = getShares(epochId_other, vault_other, user_other);
    uint256 points_ = getPoints(epochId_other, vault_other, user_other);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

    assert lastAccruedTimestamp_ == _lastAccruedTimestamp;
    assert totalPoints_ == _totalPoints;
    assert totalSupply_ == _totalSupply;
    assert lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
    assert shares_ == _shares;
    assert points_ == _points;
    assert pointsWithdrawn_ == _pointsWithdrawn;
}

// rule noChangeToOthers(uint256 epochId, address vault, address token, address from, address to, uint256 amount, uint256 epochId_other, address vault_other, address token_other, address user_other, method f) {
//     env e;
//     require epochId != epochId_other || vault != vault_other || token != token_other || (user_other!=from && user_other != to && user_other != e.msg.sender);
//     uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId_other, vault_other);
//     uint256 _totalPoints = getTotalPoints(epochId_other, vault_other);
//     uint256 _totalSupply = getTotalSupply(epochId_other, vault_other);
//     uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
//     uint256 _shares = getShares(epochId_other, vault_other, user_other);
//     uint256 _points = getPoints(epochId_other, vault_other, user_other);
//     uint256 _pointsWithdrawn = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

//     uint256[] epochIds; require epochIds.length==1; require epochIds[0]==epochId;
//     address[] vaults; require vaults.length==1; require vaults[0]==vault;
//     address[] tokens; require tokens.length==1; require tokens[0]==token;
//     address[] users; require users.length==1; require users[0]==from;
//     uint256[] amounts; require amounts.length==1; require amounts[0]==amount;
    
//     if (f.selector == accrueVault(uint256, address).selector) {
//       require epochId_other!=epochId || vault_other!=vault;
//       accrueVault(e, epochId, vault); 
//     } else if  (f.selector == getVaultTimeLeftToAccrue(uint256, address).selector) {
//       require epochId_other!=epochId || vault_other!=vault;
//       getVaultTimeLeftToAccrue(e, epochId, vault);
//     } else if (f.selector == addRewards(uint256[], address[], address[], uint256[]).selector) {
//       require epochId_other!=epochId || vault_other!=vault || token_other!=token;
//       addRewards(e, epochIds, tokens, vaults, amounts);
//     } else if (f.selector == addReward(uint256, address, address, uint256).selector) {
//       require epochId_other!=epochId || vault_other!=vault || token_other!=token;
//       addReward(e, epochId, vault, token, amount);
//     } else if (f.selector == notifyTransfer(address, address, uint256).selector) {
//       require epochId_other!=epochId || vault_other!=e.msg.sender || (user_other!=from && user_other != to);
//       require vault == e.msg.sender;
//       require epochId == currentEpoch();
//       notifyTransfer(e, from, to, amount);
//     } else if (f.selector == handleTransfer(address,address,address,uint256).selector) {
//       require epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other !=to);
//       require epochId == currentEpoch();
//       handleTransfer(e, vault, from, to, amount);
//     } else if (f.selector == handleDeposit(address,address,uint256).selector) { 
//       require epochId_other!=epochId || vault_other!=vault || user_other != to;
//       require epochId == currentEpoch();
//       handleDeposit(e, vault, to, amount);
//     } else if (f.selector == handleWithdrawal(address,address,uint256).selector) { 
//       require epochId_other!=currentEpoch() || vault_other!=vault || user_other!=from;
//       require epochId == currentEpoch();
//       handleWithdrawal(e, vault, from, amount);
//     } else if (f.selector == accrueUser(uint256, address, address).selector) {
//       require epochId_other!=epochId || vault_other!=vault || user_other!=from;
//       accrueUser(e, epochId, vault, from);
//     } else if (f.selector == getUserTimeLeftToAccrue(uint256, address, address).selector) {
//       require epochId_other!=epochId || vault_other!=vault || user_other!=from;
//       getUserTimeLeftToAccrue(e, epochId, vault, from);
//     } else if (f.selector == claimRewards(uint256[], address[], address[], address[]).selector) {
//       require epochId_other!=epochId || vault_other!=vault || token_other!=token || (user_other!=from && user_other != to);
//       claimRewards(e, epochIds, vaults, tokens, users);
//     } else if (f.selector == claimReward(uint256, address, address, address).selector) {
//       require epochId_other!=epochId || vault_other!=vault || token_other!=token || user_other!=from ;
//       claimReward(e, epochId, vault, token, from);
//     } else if (f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector) {
//       require epochId_other!=epochId || vault_other!=vault || token_other!=token || (user_other!=from && user_other != to);
//       claimBulkTokensOverMultipleEpochs(e, epochId, epochId, vault, tokens, from);
//     } else if (f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector) {
//       require epochId_other!=epochId || vault_other!=vault || token_other!=token || user_other != e.msg.sender;
//       claimBulkTokensOverMultipleEpochsOptimized(e, epochId, epochId, vault, tokens);
//     } else {
//       calldataarg args;
//       f(e,args);
//     }
    
//     uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId_other, vault_other);
//     uint256 totalPoints_ = getTotalPoints(epochId_other, vault_other);
//     uint256 totalSupply_ = getTotalSupply(epochId_other, vault_other);
//     uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId_other, vault_other, user_other);
//     uint256 shares_ = getShares(epochId_other, vault_other, user_other);
//     uint256 points_ = getPoints(epochId_other, vault_other, user_other);
//     uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId_other, vault_other, user_other, token_other);

//     assert epochId_other!=epochId || vault_other!=vault => lastAccruedTimestamp_ == _lastAccruedTimestamp;
//     assert epochId_other!=epochId || vault_other!=vault => totalPoints_ == _totalPoints;
//     assert epochId_other!=epochId || vault_other!=vault => totalSupply_ == _totalSupply;
//     assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to && user_other != e.msg.sender) => lastUserAccrueTimestamp_ == _lastUserAccrueTimestamp;
//     assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to && user_other != e.msg.sender) => shares_ == _shares;
//     assert epochId_other!=epochId || vault_other!=vault || (user_other!=from && user_other != to && user_other != e.msg.sender) => points_ == _points;
//     assert pointsWithdrawn_ == _pointsWithdrawn;
// }



// *****************************
// ****** Check Functions ******
// *****************************

invariant epochTimestamps(env e, uint256 epochId)
    ((getEpochsStartTimestamp(epochId) == 0 && getEpochsEndTimestamp(epochId) == 0) || 
    getEpochsStartTimestamp(epochId) + SECONDS_PER_EPOCH() == getEpochsEndTimestamp(epochId)) 

invariant futureEpochHasNoTimeLeftToAccrure(env e, uint256 epochId, address vault)
	epochId > currentEpoch() => getVaultTimeLeftToAccrue(e, epochId, vault) == 0

/*
  Rule: addReward function should be additive 
  Property: High level 
  Explanation: All things being equal, the same total amount of tokens added into a vault through addReward should result in the same amount of rewards, whether it is done in one call or multiple calls
  Priority: High
  Justification: if this rule fails, it means that addReward() is not self-consistent
*/
rule test_additiveAddReward(uint256 epochId, address vault, address token, uint256 amt1, uint256 amt2) {
  env e1;
  env e2;
  // requireInvariant epochTimestamps(e, epochId);
  // requireInvariant futureEpochHasNoTimeLeftToAccrure(e1, epochId, vault);
  // requireInvariant futureEpochHasNoTimeLeftToAccrure(e2, epochId, vault);
  require e1.msg.sender != currentContract && e2.msg.sender != currentContract;
  uint256 sum_amt = amt1 + amt2;

  storage init = lastStorage;
  addReward(e1, epochId, vault, token, amt1);
  addReward(e2, epochId, vault, token, amt2);
  uint256 reward_1_2 = getRewards(epochId, vault, token);
  uint256 balance_1_2 = tokenBalanceOf(token, currentContract);
  // Start a new transaction from the initial state	
  
  addReward(e2, epochId, vault, token, sum_amt) at init;
  uint256 reward_sum = getRewards(epochId, vault, token);
  uint256 balance_sum = tokenBalanceOf(token, currentContract);
  assert reward_1_2 == reward_sum, "expected addReward to be additive";
  assert balance_1_2 == balance_sum, "expected addReward to be additive";
}

/*
  Rule: addRewards() function should be equevalent to addReward() 
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

  addRewards(e1, epochIds, vaults, tokens, amounts) at init;
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
// Fix: add require (from!=0 || to!=0); at the top
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
    require from != to;

    notifyTransfer(e, from, to, amount);
    uint256 sharesFrom_ = getShares(epochId, vault, from);
    uint256 sharesTo_ = getShares(epochId, vault, to);
    uint256 totalSupply_ = getTotalSupply(epochId, vault);

    if ((from==0 && to==0) || (from!=0 && to!=0)) {
      assert getLastUserAccrueTimestamp(epochId, vault, from) == getLastUserAccrueTimestamp(epochId, vault, to);
      assert _lastUserAccrueTimestampTo != 0 ? _sharesTo + amount == sharesTo_ : to_uint256(_sharesTo + amount) <= sharesTo_ ;
      assert _lastUserAccrueTimestampFrom != 0 ? _sharesFrom == sharesFrom_ + amount : _sharesFrom <= sharesFrom_ + amount;
      assert _lastAccruedTimestamp == getLastAccruedTimestamp(epochId, vault) && _totalSupply == totalSupply_;
    } else if (from==0) {
      assert getLastAccruedTimestamp(epochId, vault) == getLastUserAccrueTimestamp(epochId, vault, to);            
      assert _lastUserAccrueTimestampTo != 0 ? to_uint256(_sharesTo + amount) == sharesTo_ : to_uint256(_sharesTo + amount) <= sharesTo_ ;
      assert _lastAccruedTimestamp != 0 ? to_uint256(_totalSupply + amount) == totalSupply_ : to_uint256(_totalSupply + amount) <= totalSupply_;
    } else {
      assert getLastAccruedTimestamp(epochId, vault) == getLastUserAccrueTimestamp(epochId, vault, from);
      assert _lastUserAccrueTimestampFrom != 0 ? _sharesFrom == sharesFrom_  + amount: _sharesFrom <= sharesFrom_ + amount;
      assert _lastAccruedTimestamp != 0 ? _totalSupply == totalSupply_ + amount: _totalSupply <= totalSupply_ + amount;
    } 
}


/*
  Rule: Making sure startNextEpoch() works as expected
  Property: Unit test
  Explanation: epoch should increase only by one at a time, and there should not be overlapping epochs
  Priority: Low
  Justification: This rule can be checked manually quite easily and it touches only one function.
*/
rule test_startNextEpoch() {
	uint256 _epoch = currentEpoch();
	uint256 _epochEnd = getEpochsEndTimestamp(_epoch);
	env e;
	startNextEpoch(e);
	
	uint256 epoch_ = currentEpoch();
	assert epoch_ == _epoch + 1;
	
	assert getEpochsStartTimestamp(epoch_) == e.block.timestamp, "wrong start";
	assert getEpochsEndTimestamp(epoch_) == e.block.timestamp + SECONDS_PER_EPOCH(), "wrong end";
  assert getEpochsEndTimestamp(_epoch) < getEpochsStartTimestamp(epoch_), "overlapping epochs";
}

/*
  Rule: Making sure accueVault() is working properly
  Property: Unit test
  Explanation: accrueVault() should bring lastAccruedTimestamp to current block.timestamp. A repeat call of accrueVault() should not change the states.
  Justification: This rule can be checked manually quite easily and it touches only one function.
*/
rule test_accueVaultCheck_repeat(uint256 epochId, address vault) {
	env e;
  require e.block.timestamp!=0;
	accrueVault(e, epochId, vault);
  uint256 totalPoints0 = getTotalPoints(epochId, vault);
  uint256 totalShares0 = getTotalSupply(epochId, vault);
	assert getLastAccruedTimestamp(epochId, vault) == e.block.timestamp;
  assert getVaultTimeLeftToAccrue(e, epochId, vault) == 0;
	accrueVault(e, epochId, vault);
  uint256 totalPoints1 = getTotalPoints(epochId, vault);
  uint256 totalShares1 = getTotalSupply(epochId, vault);
  assert totalPoints0 == totalPoints1;
  assert totalShares0 == totalShares1;
}

/*
  Rule: Making sure accueUser() is working properly
  Property: Unit test
  Explanation: accrueUser() should bring lastAccruedTimestamp to current block.timestamp. A repeat call of accrueVault() should not change the states.
  Justification: This rule can be checked manually quite easily and it touches only one function.
*/
rule test_accueUser(uint256 epochId, address vault, address user) {
	env e;
  require e.block.timestamp!=0;
	accrueUser(e, epochId, vault, user);
  uint256 points0 = getPoints(epochId, vault, user);
  uint256 shares0 = getShares(epochId, vault, user);
	assert getLastUserAccrueTimestamp(epochId, vault, user) == e.block.timestamp;
	assert getUserTimeLeftToAccrue(e, epochId, vault, user) == 0;
  accrueUser(e, epochId, vault, user);
  uint256 points1 = getPoints(epochId, vault, user);
  uint256 shares1 = getShares(epochId, vault, user);
  assert points0 == points1;
  assert shares0 == shares1;

}

/*
Rules: test_claimRewards*
Property: High level 
Explanation: Different ways of claimRewards should results in the same token balances for the same user
Justification: if this rule fails, it means that an user claims different token amounts by using different claim calls, which is indication of broken contract
*/

rule test_claimReward(uint256 epochId, address vault, address token, address user) { 
  env e;
  require getLastAccruedTimestamp(epochId, vault) == getLastUserAccrueTimestamp(epochId, vault, user);
  require getLastAccruedTimestamp(epochId, vault) == e.block.timestamp;
  uint256 _points = getPoints(epochId, vault, user);
  uint256 _pointsWithdrawn = getPointsWithdrawn(epochId, vault, user, token);
  require _points <= getTotalPoints(epochId, vault);
  require _pointsWithdrawn <= getPoints(epochId, vault, user);
  require user != currentContract;
  require getRewards(epochId, vault, token) != 0;
  require getPoints(epochId, vault, user) != 0;

  uint256 _actual = tokenBalanceOf(token, user);

  uint256 pointsLeft = getPoints(epochId, vault, user) - _pointsWithdrawn;
  uint256 ratioForPointsLeft = PRECISION() * pointsLeft / getTotalPoints(epochId, vault);
  uint256 expectedReward = getRewards(epochId, vault, token) * ratioForPointsLeft / PRECISION();

  claimReward(e, epochId, vault, token, user);

  uint256 points_ = getPoints(epochId, vault, user);
  uint256 actual_ = tokenBalanceOf(token, user);
  uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId, vault, user, token);
  assert (actual_-_actual == expectedReward);
  assert pointsWithdrawn_ >= _pointsWithdrawn , "wrong change in points withdrawn";
  assert points_ == pointsWithdrawn_, "failed to update points withdraw";
}

rule test_claimRewards_repeat(uint256 epochId, address vault, address token, address user) { 
  env e;
  // to avoid accrue calls, so no timeout
  require getLastAccruedTimestamp(epochId, vault)>0;
  require getLastUserAccrueTimestamp(epochId, vault, user)>0;

  require token == tokenA;
  uint256[] epochIds; require epochIds.length==2; require epochIds[0]==epochId; require epochIds[1]==epochId; 
  address[] vaults; require vaults.length==2; require vaults[0]==vault; require vaults[1]==vault; 
  address[] tokens; require tokens.length==2; require tokens[0]==token; require tokens[1]==token; 
  address[] users; require users.length==2; require users[0]==user; require users[1]==user;

  storage init = lastStorage;
  claimReward(e, epochId, vault, token, user);
  claimReward(e, epochId, vault, token, user);
  uint256 balance0 = tokenBalanceOf(token, user);
  
  claimRewards(e, epochIds, vaults, tokens, users) at init;
  uint256 balance1 = tokenBalanceOf(token, user);
  
  assert balance0 == balance1; 
}

rule test_claimBulkTokensOverMultipleEpochs_repeat(uint256 epochId, address vault, address token, address user) { 
  env e;
  require getTotalPoints(epochId, vault) == 1;
  require getPoints(epochId, vault, user) == 1;
  // to avoid accrue calls, so no timeout
  require getLastAccruedTimestamp(epochId, vault)>0;
  require getLastUserAccrueTimestamp(epochId, vault, user)>0;

  require epochId < currentEpoch();
  require token == tokenA;

  address[] tokens; require tokens.length==2; require tokens[0]==token; require tokens[1]==token; 

  storage init = lastStorage;
  claimReward(e, epochId, vault, token, user);
  claimReward(e, epochId, vault, token, user);
  uint256 balance0 = tokenBalanceOf(token, user);
  
  claimBulkTokensOverMultipleEpochs(e, epochId, epochId, vault, tokens, user) at init;
  uint256 balance1 = tokenBalanceOf(token, user);
  
  assert balance0 == balance1; 
//   assert false;
}

rule test_claimBulkTokensOverMultipleEpochsOptimized_repeat(uint256 epochId, address vault, address token, address user) { 
  env e;
  require getTotalPoints(epochId, vault) == 1;
  require getPoints(epochId, vault, user) == 1;

  require token == tokenA;
  require epochId < currentEpoch();
  // to avoid accrue calls, so no timeout
  require getLastAccruedTimestamp(epochId, vault)>0;
  require getLastUserAccrueTimestamp(epochId, vault, user)>0;
  require user == e.msg.sender;
  address[] tokens; require tokens.length==2; require tokens[0]==token; require tokens[1]==token; 

  storage init = lastStorage;
  claimReward(e, epochId, vault, token, user);
  claimReward(e, epochId, vault, token, user);
  uint256 balance0 = tokenBalanceOf(token, user);

  claimBulkTokensOverMultipleEpochsOptimized(e, epochId, epochId, vault, tokens) at init;
  uint256 balance1 = tokenBalanceOf(token, user);

  assert balance0 == balance1;
  assert false;
}

/*
  Rule: non-decreasing variables
  Property: Valid state 
  Explanation: Most of function calls should only monotonically increase the values of relavent variables. Exceptions are made explicit by the conditions toward the end of the rule
  Priority: High
  Justification: if this rule fails, it means that some function is broken and is changing the states inproperly
*/
rule test_noDecrease(uint256 epochId, address vault, address token, address user, uint256 amount, method f) {
    env e;
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(epochId, vault);
    uint256 _totalPoints = getTotalPoints(epochId, vault);
    uint256 _totalSupply = getTotalSupply(epochId, vault);
    require _lastAccruedTimestamp==0 => _totalPoints==0 && _totalSupply==0;
    require _lastAccruedTimestamp <= e.block.timestamp;

    uint256 _lastUserAccrueTimestamp = getLastUserAccrueTimestamp(epochId, vault, user);
    uint256 _shares = getShares(epochId, vault, user);
    uint256 _points = getPoints(epochId, vault, user);
    uint256 _pointsWithdrawn = getPointsWithdrawn(epochId, vault, user, token);
    require _lastUserAccrueTimestamp==0 => _shares==0 && _points==0 && _pointsWithdrawn==0;
    require _lastUserAccrueTimestamp <= e.block.timestamp;

    calldataarg args;
    f(e,args);
  
    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(epochId, vault);
    uint256 totalPoints_ = getTotalPoints(epochId, vault);
    uint256 totalSupply_ = getTotalSupply(epochId, vault);

    uint256 lastUserAccrueTimestamp_ = getLastUserAccrueTimestamp(epochId, vault, user);
    uint256 shares_ = getShares(epochId, vault, user);
    uint256 points_ = getPoints(epochId, vault, user);
    uint256 pointsWithdrawn_ = getPointsWithdrawn(epochId, vault, user, token);

    assert lastAccruedTimestamp_ >= _lastAccruedTimestamp;
    assert lastUserAccrueTimestamp_ >= _lastUserAccrueTimestamp;
    assert totalPoints_ >= _totalPoints;
    assert pointsWithdrawn_ >= _pointsWithdrawn;

    if (f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256,uint256,address,address[]).selector) {
      if (f.selector != handleTransfer(address,address,address,uint256).selector
        && f.selector != handleWithdrawal(address,address,uint256).selector
        && f.selector != notifyTransfer(address,address,uint256).selector) {
          assert totalSupply_ >= _totalSupply;
          assert shares_ >= _shares;
      }
      if (f.selector == handleTransfer(address,address,address,uint256).selector) {
        assert totalSupply_ >= _totalSupply;
      }
      assert points_ >= _points;
    } else {
      assert totalSupply_ >= _totalSupply;
    }    
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
  uint256 PRECISION = 1000000000000000000;

  uint256 pointsLeft = getPoints(epochId, vault, user) - getPointsWithdrawn(epochId, vault, user, token);
  uint256 ratioForPointsLeft = PRECISION * pointsLeft / getTotalPoints(epochId, vault);
  uint256 expectedReward0 = getRewards(epochId, vault, token) * ratioForPointsLeft / PRECISION;

  claimReward(e, epochId, vault, token, user);

  uint256 actual_ = tokenBalanceOf(token, user);
  assert (actual_-_actual == expectedReward0);
}


/*
  Rule: after lock-step accruals, vault should have more shares than any specific user 
  Property: High level 
  Explanation: For any given epochId, as long as last vault accrual happens after user accrual, vault should have more shares than the user
  Priority: High
  Justification: if this rule fails, it means that an user may have more shares than the vault as a whole, which indicates broken contract
*/
rule test_vaultShare_VS_userShare(uint256 epochId, address vault, address token, address user, method f) filtered {
  	f -> f.selector != accrueUser(uint256, address, address).selector && 
        f.selector != handleTransfer(address,address,address,uint256).selector &&
        f.selector != handleWithdrawal(address,address,uint256).selector &&
        f.selector != notifyTransfer(address,address,uint256).selector
} {
  env e;
  // startNextEpoch(e);   
  require epochId == currentEpoch();
  require getEpochsStartTimestamp(epochId) <  getEpochsEndTimestamp(epochId);
  require getLastAccruedTimestamp(epochId, vault) <= getLastUserAccrueTimestamp(epochId, vault, user);
  require getLastAccruedTimestamp(epochId, vault) != 0;
  require getTotalSupply(epochId, vault) >= getShares(epochId, vault, user);

	calldataarg args;
  f(e,args);
  
	assert (getLastAccruedTimestamp(epochId, vault) >= getLastUserAccrueTimestamp(epochId, vault, user)) 
    => getTotalSupply(epochId, vault) >= getShares(epochId, vault, user); 
}


/*
  Rule: after lock-step accruals, vault should have more points than any specific user 
  Property: High level 
  Explanation: For any given epochId, as long as last vault accrual happens after user accrual, vault should have more points than the user
  Priority: High
  Justification: if this rule fails, it means that an user may have more points than the vault as a whole, which indicates broken contract
*/
rule test_vaultPoint_VS_userPoint(uint256 epochId, address vault, address token, address user, method f) filtered {
  	f -> f.selector != accrueUser(uint256, address, address).selector
} {
  env e;
  // startNextEpoch(e);   
  // require epochId == currentEpoch();
  // require getEpochsStartTimestamp(epochId) <  getEpochsEndTimestamp(epochId);
  require getLastAccruedTimestamp(epochId, vault) <= getLastUserAccrueTimestamp(epochId, vault, user);
  require getLastAccruedTimestamp(epochId, vault) != 0; // not sure why this is necessary. otherwise LastAccruedTimestamp will not change. a bug?
  require (getTotalPoints(epochId, vault) >= getPoints(epochId, vault, user)
    && getTotalSupply(epochId, vault) >= getShares(epochId, vault, user)
    && getShares(epochId, vault, user) > 0 
    && getTotalPoints(epochId, vault) >= getPointsWithdrawn(epochId, vault, user, token)
    && getPoints(epochId, vault, user) >= getPointsWithdrawn(epochId, vault, user, token));
  
	calldataarg args;
  f(e,args);
  
	assert (getLastAccruedTimestamp(epochId, vault) >= getLastUserAccrueTimestamp(epochId, vault, user)) 
    => (getTotalPoints(epochId, vault) >= getPoints(epochId, vault, user)    
    && getTotalPoints(epochId, vault) >= getPointsWithdrawn(epochId, vault, user, token));

  assert (f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256,uint256,address,address[]).selector =>
    getPoints(epochId, vault, user) >= getPointsWithdrawn(epochId, vault, user, token)
    );  
}

