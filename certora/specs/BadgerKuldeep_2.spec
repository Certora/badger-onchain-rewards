import "base.spec"

// high level properties related to the system here

// High level - Total point of a vault should be greater than equal to sum of all user points for the same epoch
// verified
ghost sum_of_all_points(uint256,address) returns uint256{
    init_state axiom forall uint256 currentEpoch.forall address currentVault. sum_of_all_points(currentEpoch,currentVault) == 0;
}

hook Sstore points[KEY uint256 currentEpoch][KEY address currentVault][KEY address u] uint256 new_points
  (uint256 old_points) STORAGE {
  havoc sum_of_all_points assuming forall uint256 epoch.forall address vault.forall address user. 
  (epoch == currentEpoch && vault == currentVault && u == user) ? sum_of_all_points@new(epoch,vault) == sum_of_all_points@old(epoch,vault) + (new_points - old_points) : sum_of_all_points@new(epoch,vault) == sum_of_all_points@old(epoch,vault);
}

invariant total_points_of_vault_GE_sum_of_all_user_points(uint256 currentEpoch, address currentVault)
    getTotalPoints(currentEpoch, currentVault) >= sum_of_all_points(currentEpoch,currentVault)


// High level - Total supply of a vault should be greater than equal to sum of all user shares for the same epoch
// verified
ghost sum_of_all_shares(uint256,address) returns uint256{
    init_state axiom forall uint256 currentEpoch. forall address currentVault. sum_of_all_shares(currentEpoch,currentVault) == 0;
}

hook Sstore shares[KEY uint256 currentEpoch][KEY address currentVault][KEY address u] uint256 new_shares
    (uint256 old_shares) STORAGE {
  havoc sum_of_all_shares assuming forall uint256 epoch. forall address vault. forall address user. 
  (currentEpoch == epoch && currentVault == vault && u == user) ? sum_of_all_shares@new(epoch,vault) == sum_of_all_shares@old(epoch,vault) + new_shares - old_shares : sum_of_all_shares@new(epoch,vault) == sum_of_all_shares@old(epoch,vault);
}

invariant total_supply_of_vault_GE_sum_of_all_user_shares(uint256 currentEpoch, address currentVault)
    getTotalSupply(currentEpoch, currentVault) >= sum_of_all_shares(currentEpoch, currentVault)


// High level - Total points of a user should be greater than equal to sum of points withdrawn for the same vault and for the same epoch
// verified
ghost sum_of_all_points_withdrawn(uint256,address,address) returns uint256{
    init_state axiom forall uint256 currentEpoch.forall address currentVault.forall address currentUser.sum_of_all_points_withdrawn(currentEpoch,currentVault,currentUser) == 0;
}

hook Sstore pointsWithdrawn[KEY uint256 currentEpoch][KEY address currentVault][KEY address currentUser][KEY address rewardToken] uint256 new_points_withdrawn
    (uint256 old_points_withdrawn) STORAGE {
  havoc sum_of_all_points_withdrawn assuming forall uint256 epoch. forall address vault. forall address user. forall address reward. 
  (currentEpoch == epoch && currentVault == vault && currentUser == user && rewardToken == reward) ? sum_of_all_points_withdrawn@new(epoch,vault,user) == sum_of_all_points_withdrawn@old(epoch,vault,user) + (new_points_withdrawn - old_points_withdrawn): sum_of_all_points_withdrawn@new(epoch,vault,user) == sum_of_all_points_withdrawn@old(epoch,vault,user);
}

invariant total_point_by_user_GE_sum_of_all_user_withdrawn_points(uint256 currentEpoch, address currentVault, address currentUser)
    getPoints(currentEpoch, currentVault, currentUser) >= sum_of_all_points_withdrawn(currentEpoch,currentVault,currentUser)


// High Level -- reward token balance in contract should be greater or equal reward amount needed
// unverified
ghost sum_of_all_rewards_amounts(uint256,address) returns uint256{
    init_state axiom forall uint256 currentEpoch.forall address currentVault.sum_of_all_rewards_amounts(currentEpoch,currentVault) == 0;
}

hook Sstore rewards[KEY uint256 currentEpoch][KEY address currentVault][KEY address rewardToken] uint256 new_reward_amount
    (uint256 old_reward_amount) STORAGE {
  havoc sum_of_all_rewards_amounts assuming forall uint256 epoch. forall address vault. forall address reward.
  (currentEpoch == epoch && currentVault == vault && rewardToken == reward) ? sum_of_all_rewards_amounts@new(epoch,vault) == sum_of_all_rewards_amounts@old(epoch,vault) + (new_reward_amount - old_reward_amount): sum_of_all_rewards_amounts@new(epoch,vault) == sum_of_all_rewards_amounts@old(epoch,vault);
}

invariant total_balance_of_reward_token_GE_total_reward_token_amounts(uint256 currentEpoch, address currentVault, address rewardToken)
    tokenBalanceOf(rewardToken, currentContract) >= sum_of_all_rewards_amounts(currentEpoch,currentVault)
    