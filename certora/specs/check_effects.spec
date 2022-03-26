import "reward_manager_methods.spec"

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

// what functions can decrease a users points?
// RESULT - claimBulk, claimReward, claimRewards
rule whoChangedMyPoints(uint256 epoch, address vault, address user, method f) filtered {f -> !f.isView} {
    env e;
    uint256 pointsBefore = getPoints(epoch,vault,user);
    calldataarg args;
    f(e,args);
    uint256 pointsAfter = getPoints(epoch,vault,user);
    assert pointsAfter == pointsBefore;
}

// what functions can increase a users pointsWithdrawn?
// RESULT - claimBulkOptimized
rule whoChangedMyPointsWithdrawn(uint256 epoch, address vault, address token, address user, method f) filtered {f -> !f.isView} {
    env e;
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epoch,vault,user,token);
    calldataarg args;
    f(e,args);
    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epoch,vault,user,token);
    assert pointsWithdrawnAfter == pointsWithdrawnBefore;
}

// what functions can decrease a users shares?
// RESULT - handleTransfer
rule whoChangedMyShares(uint256 epoch, address vault, address user, method f) filtered {f -> !f.isView} {
    env e;
    uint256 before = getShares(epoch,vault,user);
    calldataarg args;
    f(e,args);
    uint256 after = getShares(epoch,vault,user);
    assert after == before;
}

// get the list of functions which can change user's balance (It's not a rule that we usually use in real verification, more as a code example)
rule whoChangedMyBalance(address token, address user, method f) filtered {f -> !f.isView && f.selector != accrueVault(uint256, address).selector} {
    uint256 before = tokenBalanceOf(token,user);

    env e;
    calldataarg args;
    f(e,args);

    assert tokenBalanceOf(token,user) == before;
}