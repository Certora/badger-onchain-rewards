import "reward_manager_methods.spec"

// rules and invariants in this spec are wip

function claimMethods(uint256 epoch, address vault, address user, address token, method f, env e) {
    if (f.selector == claimReward(uint256, address, address, address).selector) {
        claimReward(e, epoch, vault, user, token);
    } else if (f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector) {
        claimBulkTokensOverMultipleEpochs(e, epoch, epoch, vault, [token], user);
    } else if (f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector) {
        claimBulkTokensOverMultipleEpochsOptimized(e, epoch, epoch, vault, [token]);
    }
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////                                        UNIT TESTS                                       ////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



// STATUS - verified
// note: when token is allowed to equal to user, finds an exception but with an invalid state (total points < user points)
rule withdrawn_points_and_tokens_received_correlated(method f, uint256 epoch, address vault, address user, address token) 
    filtered {f -> f.selector == claimReward(uint256, address, address, address).selector || f.selector == claimBulkTokensOverMultipleEpochs(uint256, uint256, address, address[], address).selector || f.selector == claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector} {
    env e;
    calldataarg args;
    require user != getAddress() && token != getAddress() && token != user;
    uint256 claimedBefore = getPointsWithdrawn(epoch, vault, user, token);
    uint256 tokenBalanceBefore = tokenBalanceOf(token, user);

    claimMethods(epoch, vault, user, token, f, e);

    uint256 claimedAfter = getPointsWithdrawn(epoch, vault, user, token);
    uint256 tokenBalanceAfter = tokenBalanceOf(token, user);
    assert (tokenBalanceAfter > tokenBalanceBefore => claimedAfter > claimedBefore, "token balance increased without points being counted as withdrawn");
    assert (claimedAfter > claimedBefore => tokenBalanceAfter > tokenBalanceBefore, "points counted as withdrawn but user balance did not increase");
    // assert false, "non-reverting path exists";
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////                                       VALID STATES                                      ////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


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

rule check_tautology_1(uint256 epoch, address vault) {
    assert getTotalSupply(epoch, vault) >= sum_all_shares(epoch, vault);
}

// Total shares should be greater than sum of all users' shares.
// gets better coverage than total_shares_gte_sum_all_shares
// STATUS - unverfied
rule sum_all_shares_gte_any_two(method f, uint256 epoch, address vault, address userA, address userB) {
    env e;
    calldataarg args;
    require (userA != userB) => (sum_all_shares(epoch, vault) >= getShares(epoch, vault, userA) + getShares(epoch, vault, userB));
    f(e, args); // userC exists with funds, calling transfers from it breaks rule
    assert (userA != userB) => (sum_all_shares(epoch, vault) >= getShares(epoch, vault, userA) + getShares(epoch, vault, userB));
}
    


invariant sum_all_shares_gte_any_one(uint256 epoch, address vault)
    forall address user.
    sum_all_shares(epoch, vault) >= getShares(epoch, vault, user)

invariant total_supply_gte_any_one(uint256 epoch, address vault)
    forall address user.
    getTotalSupply(epoch, vault) >= getShares(epoch, vault, user)


ghost sum_all_points(uint256, address) returns uint {
    init_state axiom forall uint256 epoch. forall address vault. sum_all_points(epoch, vault) == 0;
}

hook Sstore points[KEY uint256 epoch][KEY address vault][KEY address user]
    uint256 points
    (uint256 old_points) STORAGE {
        havoc sum_all_points assuming forall uint256 e. forall address v. ((epoch == e && vault == v) => sum_all_points@new(e, v) == sum_all_points@old(e, v) - old_points + points) && ((epoch != e || vault != v) => sum_all_points@new(e, v) == sum_all_points@old(e, v));
    }

// Total points should be greater than sum of all users' points.
// STATUS - invalid
// note: functions are able to break this invariant by having more shares for a single user than the total shares, which contradicts the requireInvariant statement
invariant total_points_gte_sum_all_points(uint256 epoch, address vault)
    getTotalPoints(epoch, vault) >= sum_all_points(epoch, vault)

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////                                     STATE TRANSITIONS                                   ////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////                                    VARIABLE TRANSITIONS                                 ////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////                                        HIGH-LEVEL                                       ////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////