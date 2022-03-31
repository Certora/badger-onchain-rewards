import "reward_manager_methods.spec"

using DummyERC20A as token
using DummyERC20A as token1
using DummyERC20B as token2

///////////////////////// FUNCTIONS ///////////////////////////

// calls one of three claim functions with their proper inputs
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
}

// claimReward always gives right amount of tokens
// STATUS - verified
rule claim_reward_gives_tokens(uint256 epoch, address vault) {
    env e;
    require e.msg.sender != currentContract;
    uint256 tokenBalanceBefore = tokenBalanceOf(token, e.msg.sender);
    uint256 tokensForUser = getTokenClaimAmount(e, epoch, vault, token, e.msg.sender);
    // amountForUser = getRewards(epoch, vault, )
    claimReward(e, epoch, vault, token, e.msg.sender);
    uint256 tokenBalanceAfter = tokenBalanceOf(token, e.msg.sender);
    assert tokenBalanceAfter == tokensForUser + tokenBalanceBefore, "wrong amount of tokens received";
}

// claimBulkTokensOverMultipleEpochs always gives right amount of tokens
// STATUS - verified
rule claim_bulk_gives_tokens(uint256 epoch, address vault) {
    env e;
    require e.msg.sender != currentContract;
    uint256 tokenBalanceBefore = tokenBalanceOf(token, e.msg.sender);
    uint256 tokensForUser = getTokenClaimAmount(e, epoch, vault, token, e.msg.sender);
    // amountForUser = getRewards(epoch, vault, )
    claimBulkTokensOverMultipleEpochs(e, epoch, epoch, vault, [token], e.msg.sender);
    uint256 tokenBalanceAfter = tokenBalanceOf(token, e.msg.sender);
    assert tokenBalanceAfter == tokensForUser + tokenBalanceBefore, "wrong amount of tokens received";
}

// claimBulkTokensOverMultipleEpochsOptimized always gives right amount of tokens
// STATUS - verified
rule claim_bulk_optimized_gives_tokens(uint256 epoch, address vault) {
    env e;
    require e.msg.sender != currentContract;
    uint256 tokenBalanceBefore = tokenBalanceOf(token, e.msg.sender);
    uint256 tokensForUser = getTokenClaimAmount(e, epoch, vault, token, e.msg.sender);
    // amountForUser = getRewards(epoch, vault, )
    claimBulkTokensOverMultipleEpochsOptimized(e, epoch, epoch, vault, [token]);
    uint256 tokenBalanceAfter = tokenBalanceOf(token, e.msg.sender);
    assert tokenBalanceAfter == tokensForUser + tokenBalanceBefore, "wrong amount of tokens received";
}

// users that depositted tokens for a longer time have more points
// STATUS - verified
rule points_accrue_over_time(uint256 epoch, address vault, address user, address from, uint256 amount) {
    env e;
    env e1;
    env e2;

    require e2.block.timestamp > e1.block.timestamp;
    require e.block.timestamp > e1.block.timestamp;
    require e2.block.timestamp > e.block.timestamp;
    require epoch == currentEpoch();
    require getEpochsEndTimestamp(epoch) == getEpochsStartTimestamp(epoch) + SECONDS_PER_EPOCH();
    require getEpochsEndTimestamp(epoch) > e2.block.timestamp;
    require getEpochsStartTimestamp(epoch) < e1.block.timestamp;
    require user == e1.msg.sender;
    require user == e2.msg.sender;
    require vault == e.msg.sender;
    require amount > 0;
    
    notifyTransfer(e, from, user, amount);
    require getShares(epoch, vault, user) > 0;
    accrueUser(e1, epoch, vault, user);
    uint256 points1 = getPoints(epoch, vault, user);
    accrueUser(e2, epoch, vault, user);
    uint256 points2 = getPoints(epoch, vault, user);
    assert points2 > points1, "points didnt increase with time";
}

// addReward adds the right amount of rewards for the right epoch, vault and token
// STATUS - verfied

rule add_reward_adds_reward(uint256 epoch, address vault, address token, uint256 amount) {
    env e;
    require e.msg.sender != currentContract;

    uint256 rewardsBefore = getRewards(epoch, vault, token);
    addReward(e, epoch, vault, token, amount);
    uint256 rewardsAfter = getRewards(epoch, vault, token);

    assert rewardsAfter == rewardsBefore + amount;
}

///////////////////////// VARIABLE TRANSITIONS ///////////////////////////

// Changing points for one epoch should not effect other epochs
// STATUS - verified
rule points_independent_epochs(uint256 epoch1, uint256 epoch2, address vault, address user, address token, method f)
{
    env e;
    require user == e.msg.sender;
    require epoch1 != epoch2;
    uint256 pointsEpoch1Before = getPoints(epoch1, vault, user);
    uint256 pointsEpoch2Before = getPoints(epoch2, vault, user);
    claimBulkTokensOverMultipleEpochsOptimized(e, epoch1, epoch1, vault, [token]);
    uint256 pointsEpoch1After = getPoints(epoch1, vault, user);
    uint256 pointsEpoch2After = getPoints(epoch2, vault, user);
    assert pointsEpoch2After == pointsEpoch2Before, "claiming for one epoch affects others";
} 

// Changing points for one vault should not effect other vaults
// STATUS - verified
rule points_independent_vaults(uint256 epoch, address vault1, address vault2, address user, address token, method f)
{
    env e;
    require user == e.msg.sender;
    require vault1 != vault2;
    uint256 pointsVault1Before = getPoints(epoch, vault1, user);
    uint256 pointsVault2Before = getPoints(epoch, vault2, user);
    claimBulkTokensOverMultipleEpochsOptimized(e, epoch, epoch, vault1, [token]);
    uint256 pointsVault1After = getPoints(epoch, vault1, user);
    uint256 pointsVault2After = getPoints(epoch, vault2, user);
    assert pointsVault2After == pointsVault2Before, "claiming for one vault affects others";
} 

// Changing points for user epoch should not effect other users
// STATUS - verified
rule points_independent_users(uint256 epoch, address vault, address user1, address user2, address token, method f) 
{
    env e;
    require user1 == e.msg.sender;
    require user1 != user2;
    uint256 pointsUser1Before = getPoints(epoch, vault, user1);
    uint256 pointsUser2Before = getPoints(epoch, vault, user2);
    claimBulkTokensOverMultipleEpochsOptimized(e, epoch, epoch, vault, [token]);
    uint256 pointsUser1After = getPoints(epoch, vault, user1);
    uint256 pointsUser2After = getPoints(epoch, vault, user2);
    assert pointsUser2After == pointsUser2Before, "claiming for one user affects others";
} 

// Changing pointsWithdrawn for one epoch should not effect other epochs
// STATUS - verified
rule points_withdrawn_independent_epochs(uint256 epoch1, address epoch2, address vault, address user, address token, method f) filtered {f -> f.selector == claimReward(uint256, address, address, address).selector || f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector}
{
    env e;
    require user == e.msg.sender;
    require epoch1 != epoch2;
    uint256 pointsWithdrawnEpoch1Before = getPointsWithdrawn(epoch1, vault, user, token);
    uint256 pointsWithdrawnEpoch2Before = getPointsWithdrawn(epoch2, vault, user, token);
    claimMethods(epoch1, vault, user, token, f, e);
    uint256 pointsWithdrawnEpoch1After = getPointsWithdrawn(epoch1, vault, user, token);
    uint256 pointsWithdrawnEpoch2After = getPointsWithdrawn(epoch2, vault, user, token);
    assert pointsWithdrawnEpoch2Before == pointsWithdrawnEpoch2After, "claiming for one epoch affects others";
} 

// Changing pointsWithdrawn for one vault should not effect other vaults
// STATUS - verified
rule points_withdrawn_independent_vaults(uint256 epoch, address vault1, address vault2, address user, address token, method f) filtered {f -> f.selector == claimReward(uint256, address, address, address).selector || f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector}
{
    env e;
    require user == e.msg.sender;
    require vault1 != vault2;
    uint256 pointsWithdrawnVault1Before = getPointsWithdrawn(epoch, vault1, user, token);
    uint256 pointsWithdrawnVault2Before = getPointsWithdrawn(epoch, vault2, user, token);
    claimMethods(epoch, vault1, user, token, f, e);
    uint256 pointsWithdrawnVault1After = getPointsWithdrawn(epoch, vault1, user, token);
    uint256 pointsWithdrawnVault2After = getPointsWithdrawn(epoch, vault2, user, token);
    assert pointsWithdrawnVault2After == pointsWithdrawnVault2Before, "claiming for one vault affects others";
} 

// Changing pointsWithdrawn for one user should not effect other users
// STATUS - verified
rule points_withdrawn_independent_users(uint256 epoch, address vault, address user1, address user2, address token, method f) filtered {f -> f.selector == claimReward(uint256, address, address, address).selector || f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector}
{
    env e;
    require user1 == e.msg.sender;
    require user1 != user2;
    uint256 pointsWithdrawnUser1Before = getPointsWithdrawn(epoch, vault, user1, token);
    uint256 pointsWithdrawnUser2Before = getPointsWithdrawn(epoch, vault, user2, token);
    claimMethods(epoch, vault, user1, token, f, e);
    uint256 pointsWithdrawnUser1After = getPointsWithdrawn(epoch, vault, user1, token);
    uint256 pointsWithdrawnUser2After = getPointsWithdrawn(epoch, vault, user2, token);
    assert pointsWithdrawnUser2After == pointsWithdrawnUser2Before, "claiming for one user affects others";
} 

// Changing pointsWithdrawn for one token should not effect other tokens
// STATUS - verified
rule points_withdrawn_independent_tokens(uint256 epoch, address vault, address user, address token1, address token2, method f) filtered {f -> f.selector == claimReward(uint256, address, address, address).selector || f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector}
{
    env e;
    require user == e.msg.sender;
    require token1 != token2;
    uint256 pointsWithdrawnToken1Before = getPointsWithdrawn(epoch, vault, user, token1);
    uint256 pointsWithdrawnToken2Before = getPointsWithdrawn(epoch, vault, user, token2);
    claimMethods(epoch, vault, user, token1, f, e);
    uint256 pointsWithdrawnToken1After = getPointsWithdrawn(epoch, vault, user, token1);
    uint256 pointsWithdrawnToken2After = getPointsWithdrawn(epoch, vault, user, token2);
    assert pointsWithdrawnToken2After == pointsWithdrawnToken2Before, "claiming for one token affects others";
} 

// Changing shares for one epoch should not effect other epochs
// STATUS - verified
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

// Changing shares for one vault should not effect other vaults
// STATUS - verified
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

// Changing shares for one user should not effect other users
// STATUS - verified
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

