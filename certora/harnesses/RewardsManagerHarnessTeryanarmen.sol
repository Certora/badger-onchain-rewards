// SPDX-License-Identifier: MIT
pragma solidity 0.8.10;

import "../../contracts/RewardsManager.sol";

contract RewardsManagerHarness is RewardsManager {
    
    // public method calls
    function handleDeposit(address vault, address to, uint256 amount) public {
        _handleDeposit(vault, to, amount);
    }

    function handleWithdrawal(address vault, address to, uint256 amount) public {
        _handleWithdrawal(vault, to, amount);
    }

    function handleTransfer(address vault, address from, address to, uint256 amount) public {
        _handleTransfer(vault, from, to, amount);
    }

    function requireNoDuplicates(address[] memory arr) public {
        _requireNoDuplicates(arr);
    }

    function min(uint256 a, uint256 b) public pure returns (uint256) {
        return _min(a, b);
    }


    // map getters
    function getEpochsStartTimestamp(uint256 epochId) public returns (uint256) {
        return epochs[epochId].startTimestamp;
    }

    function getEpochsEndTimestamp(uint256 epochId) public returns (uint256) {
        return epochs[epochId].endTimestamp;
    }

    function getPoints(uint256 epochId, address vaultAddress, address userAddress) public returns (uint256) {
        return points[epochId][vaultAddress][userAddress];
    }

    function getPointsWithdrawn(uint256 epochId, address vaultAddress, address userAddress, address rewardToken) public returns (uint256) {
        return pointsWithdrawn[epochId][vaultAddress][userAddress][rewardToken];
    }

    function getTotalPoints(uint256 epochId, address vaultAddress) public returns (uint256) {
        return totalPoints[epochId][vaultAddress];
    }

    function getLastAccruedTimestamp(uint256 epochId, address vaultAddress) public returns (uint256) {
        return lastAccruedTimestamp[epochId][vaultAddress];
    }

    function getLastUserAccrueTimestamp(uint256 epochId, address vaultAddress, address userAddress) public returns (uint256) {
        return lastUserAccrueTimestamp[epochId][vaultAddress][userAddress];
    }

    function getLastVaultDeposit(address userAddress) public returns (uint256) {
        return lastVaultDeposit[userAddress];
    }

    function getShares(uint256 epochId, address vaultAddress, address userAddress) public returns (uint256) {
        return shares[epochId][vaultAddress][userAddress];
    }

    function getTotalSupply(uint256 epochId, address vaultAddress) public returns (uint256) {
        return totalSupply[epochId][vaultAddress];
    }

    function getRewards(uint256 epochId, address vaultAddress, address tokenAddress) public returns (uint256) {
        return rewards[epochId][vaultAddress][tokenAddress];
    }

    function tokenBalanceOf(address token, address user) public returns (uint256) {
        return IERC20(token).balanceOf(user);
    }

    // space to create your own destiny 
    function getAddress() public view returns(address) {
        return address(this);
    }

    function getTokenClaimAmount(uint256 epochId, address vault, address token, address user) public returns(uint256) {
        accrueUser(epochId, vault, user);
        accrueVault(epochId, vault);

        // Now that they are accrue, just use the points to estimate reward and send
        uint256 userPoints = points[epochId][vault][user];
        uint256 vaultTotalPoints = totalPoints[epochId][vault];

        uint256 pointsLeft = userPoints - pointsWithdrawn[epochId][vault][user][token];

        // We got some stuff left // Use ratio to calculate what we got left
        uint256 totalAdditionalReward = rewards[epochId][vault][token];

        // We multiply just to avoid rounding
        uint256 ratioForPointsLeft = PRECISION * pointsLeft / vaultTotalPoints;
        uint256 tokensForUser = totalAdditionalReward * ratioForPointsLeft / PRECISION;
        return tokensForUser;
    }

    /*
    // rule testing bug functions 
    // STATUS - successfully breaks total_shares_gte_sum_all_shares
    function addUserSharesWithoutAddingTotal(uint256 epoch, address vault, address user, uint256 amount) public {
        shares[epoch][vault][user] += amount;
    }
    */

}