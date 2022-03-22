import "reward_manager_methods.spec"

using DummyERC20A as _token0
using DummyERC20B as token

///////////////////////// CHECK EFFECTS ///////////////////////////

// what functions can decrease a users points?
// RESULT - claimBulk, claimReward, claimRewards
rule whoDecreasedMyPoints(uint256 epoch, address vault, address user, method f) filtered {f -> !f.isView} {
    env e;
    uint256 pointsBefore = getPoints(epoch,vault,user);
    calldataarg args;
    f(e,args);
    uint256 pointsAfter = getPoints(epoch,vault,user);
    assert pointsAfter >= pointsBefore;
}

// what functions can increase a users pointsWithdrawn?
// RESULT - claimBulkOptimized
rule whoIncreasedMyPointsWithdrawn(uint256 epoch, address vault, address token, address user, method f) filtered {f -> !f.isView} {
    env e;
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epoch,vault,user,token);
    calldataarg args;
    f(e,args);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epoch,vault,user,token);
    assert pointsWithdrawnAfter <= pointsWithdrawnBefore;
}

// what functions can decrease a users shares?
// RESULT - handleTransfer
rule whoDecreasedMyShares(uint256 epoch, address vault, address user, method f) filtered {f -> !f.isView} {
    env e;
    uint256 before = getShares(epoch,vault,user);
    calldataarg args;
    f(e,args);
    uint256 after = getShares(epoch,vault,user);
    assert after >= before;
}

///////////////////////// FUNCTIONS ///////////////////////////

function claimMethods(uint256 epoch, address vault, address user, address token, method f, env e) {
    if (f.selector == claimReward(uint256, address, address, address).selector) {
        claimReward(e, epoch, vault, token, user);
    } else if (f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector) {
        claimBulkTokensOverMultipleEpochs(e, epoch, epoch, vault, [token], user);
    } else if (f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector) {
        claimBulkTokensOverMultipleEpochsOptimized(e, epoch, epoch, vault, [token]);
    }
}

///////////////////////// UNIT TESTS ///////////////////////////

// cant start new epoch until this one is done
// STATUS - verified
rule timely_epoch_update(method f) {
    env e;
    uint256 epochBefore = currentEpoch();
    calldataarg args;
    f(e, args);
    uint256 epochAfter = currentEpoch();
    assert (epochAfter > epochBefore => epochAfter == epochBefore + 1, "epoch increased by more than 1");
    assert ((epochAfter == epochBefore + 1 => f.selector == startNextEpoch().selector), "epoch increased by illegal function");
    // assert false, "non-reverting path exists";
}

// claimReward always gives right amount of tokens
// STATUS - verified
rule claim_reward_gives_tokens(uint256 epoch, address vault) {
    env e;
    require e.msg.sender != currentContract;
    uint256 tokenBalanceBefore = tokenBalanceOf(_token0, e.msg.sender);
    uint256 tokensForUser = getTokenClaimAmount(e, epoch, vault, _token0, e.msg.sender);
    // amountForUser = getRewards(epoch, vault, )
    claimReward(e, epoch, vault, _token0, e.msg.sender);
    uint256 tokenBalanceAfter = tokenBalanceOf(_token0, e.msg.sender);
    assert tokenBalanceAfter == tokensForUser + tokenBalanceBefore, "wrong amount of tokens received";
}

///////////////////////// INDEPENDENCE RULES ///////////////////////////
    
rule points_independent_epochs(uint256 epoch1, address epoch2, address vault, address user, address token, method f) 
    filtered {f -> 
    f.selector == claimReward(uint256, address, address, address).selector || 
    f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector || 
    f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector}
{
    env e;
    require user == e.msg.sender;
    require epoch1 != epoch2;
    uint256 pointsEpoch1Before = getPoints(epoch1, vault, user);
    uint256 pointsEpoch2Before = getPoints(epoch2, vault, user);
    claimMethods(epoch1, vault, user, token, f, e);
    uint256 pointsEpoch1After = getPoints(epoch1, vault, user);
    uint256 pointsEpoch2After = getPoints(epoch2, vault, user);
    assert pointsEpoch2After == pointsEpoch2Before, "claiming for one epoch affects others";
} 

rule points_independent_vaults(uint256 epoch, address vault1, address vault2, address user, address token, method f) 
    filtered {f -> 
    f.selector == claimReward(uint256, address, address, address).selector || 
    f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector || 
    f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector}
{
    env e;
    require user == e.msg.sender;
    require vault1 != vault2;
    uint256 pointsVault1Before = getPoints(epoch, vault1, user);
    uint256 pointsVault2Before = getPoints(epoch, vault2, user);
    claimMethods(epoch, vault1, user, token, f, e);
    uint256 pointsVault1After = getPoints(epoch, vault1, user);
    uint256 pointsVault2After = getPoints(epoch, vault2, user);
    assert pointsVault2After == pointsVault2Before, "claiming for one vault affects others";
} 

rule points_independent_users(uint256 epoch, address vault, address user1, address user2, address token, method f) 
    filtered {f -> 
    f.selector == claimReward(uint256, address, address, address).selector || 
    f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector || 
    f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector}
{
    env e;
    require user1 == e.msg.sender;
    require user1 != user2;
    uint256 pointsUser1Before = getPoints(epoch, vault, user1);
    uint256 pointsUser2Before = getPoints(epoch, vault, user2);
    claimMethods(epoch, vault, user1, token, f, e);
    uint256 pointsUser1After = getPoints(epoch, vault, user1);
    uint256 pointsUser2After = getPoints(epoch, vault, user2);
    assert pointsUser2After == pointsUser2Before, "claiming for one user affects others";
} 

rule shares_independent_epochs(uint256 epoch1, uint256 epoch2, address vault, address user, address from, address to, uint256 amount) {
    env e;
    require vault == e.msg.sender;
    require epoch1 == currentEpoch();
    require epoch1 != epoch2;
    uint256 sharesEpoch1Before = getShares(epoch1, vault, user);
    uint256 sharesEpoch2Before = getShares(epoch2, vault, user);
    notifyTransfer(e, from, to, amount);
    uint256 sharesEpoch1After = getShares(epoch1, vault, user);
    uint256 sharesEpoch2After = getShares(epoch2, vault, user);
    
    assert sharesEpoch2After == sharesEpoch2Before, "claiming for one epoch affects others";
} 

rule shares_independent_vaults(uint256 epoch, address vault1, address vault2, address user, address from, address to, uint256 amount) {
    env e;
    require vault1 == e.msg.sender;
    require epoch == currentEpoch();
    require vault1 != vault2;
    uint256 sharesVault1Before = getShares(epoch, vault1, user);
    uint256 sharesVault2Before = getShares(epoch, vault2, user);
    notifyTransfer(e, from, to, amount);
    uint256 sharesVault1After = getShares(epoch, vault1, user);
    uint256 sharesVault2After = getShares(epoch, vault2, user);
    
    assert sharesVault2After == sharesVault2Before, "claiming for one user affects others";
} 
rule shares_independent_users(uint256 epoch, address vault, address user1, address user2, address from, address to, uint256 amount) {
    env e;
    require vault == e.msg.sender;
    require epoch == currentEpoch();
    require user1 != user2 && user2 != from && user2 != to;
    uint256 sharesUser1Before = getShares(epoch, vault, user1);
    uint256 sharesUser2Before = getShares(epoch, vault, user2);
    notifyTransfer(e, from, to, amount);
    uint256 sharesUser1After = getShares(epoch, vault, user1);
    uint256 sharesUser2After = getShares(epoch, vault, user2);
    
    assert sharesUser2After == sharesUser2Before, "claiming for one user affects others";
} 
