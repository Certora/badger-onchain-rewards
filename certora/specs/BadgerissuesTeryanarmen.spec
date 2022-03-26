import "reward_manager_methods.spec"

// addReward adds the right amount of rewards for the right epoch, vault and token
// STATUS - failing, error in contract
rule add_rewards_adds_rewards(uint256[] epochs, address[] vaults, address[] tokens, uint256[] amounts, uint256 k) {
    env e;
    require e.msg.sender != currentContract;
    
    require vaults.length == epochs.length;
    require tokens.length == epochs.length;
    require amounts.length == epochs.length;
    require k < epochs.length;

    uint256 rewardsBefore = getRewards(epochs[k],  tokens[k], vaults[k]);
    addRewards(e, epochs, vaults, tokens, amounts);
    uint256 rewardsAfter = getRewards(epochs[k], tokens[k], vaults[k]);

    assert rewardsAfter == rewardsBefore + amounts[k], "correct amount of rewards not added";
}

// addRewards has the same effect as calling addReward multiple times
// STATUS - verified
// @note Found issue with addRewards and addReward, addRewards switches order of tokens and vaults in addReward
rule add_rewards_eq_add_reward(uint256[] epochs, address[] tokens, address[] vaults, uint256[] amounts) {
    env e;
    require e.msg.sender != currentContract;

    require epochs.length == 1;
    require tokens.length == 1;
    require vaults.length == 1;

    uint256 rewardsBefore = getRewards(epochs[0], vaults[0], tokens[0]);
    addRewards(e, epochs, tokens, vaults, amounts);
    uint256 rewardsMiddle = getRewards(epochs[0], vaults[0], tokens[0]);
    addReward(e, epochs[0], vaults[0], tokens[0], amounts[0]);
    uint256 rewardsAfter = getRewards(epochs[0], vaults[0], tokens[0]);

    assert rewardsAfter - rewardsMiddle == rewardsMiddle - rewardsBefore, "rewards changed by different amounts for addReward and addRewards";
}