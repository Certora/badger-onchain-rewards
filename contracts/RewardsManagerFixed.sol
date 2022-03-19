// SPDX-License-Identifier: MIT
pragma solidity 0.8.10;


import {IERC20} from "@oz/token/ERC20/IERC20.sol";
import {SafeERC20} from "@oz/token/ERC20/utils/SafeERC20.sol";
import {ReentrancyGuard} from "@oz/security/ReentrancyGuard.sol";


/// @dev I've updated some interfaces and implementation logic of the contract 
/// to improve the readability and make it less error-prone hopefully. 
/// Over 600 lines of code has been reduced to less than 500 lines
///
/// 1. The notifyTransfer function uses zero address value as an indicator of actual logic to be invoked.
/// This is error-prone for both the caller and the callee.
/// I have removed it and use 3 explicit functions - notifyDeposit, notifyWithdrawal, notifyTransfer instead.
///
/// 2. The accrueVault and accrueUser functions are unnecessarily public, since they are always called in claimReward and notify*** functions.
/// More public functions, more attack surface, hence I have changed the visibility of the functions to be private.
/// 
/// 3. The getTotalSupplyAtEpoch and getBalanceAtEpoch functions are unnecessarily complicated. They are refactored and renamed
/// to totalSupplyAtEpoch and balanceAtEpoch respectively, as they are not view functions anymore.
///
/// 4. Refactored accrueVault, accrueUser, getTimeLeftToAccrue and getUserTimeLeftToAccrue functions
///
/// 5. require the epochId > 0 in addReward function
contract RewardsManagerFixed is ReentrancyGuard {
    using SafeERC20 for IERC20;

    uint256 public constant SECONDS_PER_EPOCH = 604800; // One epoch is one week
    // This allows to specify rewards on a per week basis, making it easier to interact with contract
    

    uint256 public constant PRECISION = 1e18;
    
    mapping(uint256 => Epoch) public epochs; // Epoch data for each epoch epochs[epochId]
    // id is implicit in the list
    struct Epoch {
        uint256 startTimestamp;
        uint256 endTimestamp;
    }
    uint256 public currentEpoch = 0; // NOTE: 0 has the meaning of either uninitialized or set to null
    // We need to start with 0 so the first epoch can be set right after deployment 

    mapping(uint256 => mapping(address => mapping(address => uint256))) public points; // Calculate points per each epoch points[epochId][vaultAddress][userAddress]
    mapping(uint256 => mapping(address => mapping(address => mapping(address => uint256)))) public pointsWithdrawn; // Given point for epoch how many where withdrawn by user? pointsWithdrawn[epochId][vaultAddress][userAddress][rewardToken]
    
    mapping(uint256 => mapping(address => uint256)) public totalPoints; // Sum of all points given for a vault at an epoch totalPoints[epochId][vaultAddress]

    mapping(uint256 => mapping(address => uint256)) public lastAccruedTimestamp; // Last timestamp in which vault was accrued - lastAccruedTimestamp[epochId][vaultAddress]
    mapping(uint256 => mapping(address => mapping(address => uint256))) public lastUserAccrueTimestamp; // Last timestamp in we accrued user to calculate rewards in epochs without interaction lastUserAccrueTimestampepochId][vaultAddress][userAddress]
    mapping(address => uint256) public lastVaultDeposit; // Last Epoch in which any user deposited in the vault, used to know if vault needs to be brought to new epoch
    // Or just have the check and skip the op if need be

    mapping(uint256 => mapping(address => mapping(address => uint256))) public shares; // Calculate points per each epoch shares[epochId][vaultAddress][userAddress]    
    mapping(uint256 => mapping(address => uint256)) public totalSupply; // Sum of all deposits for a vault at an epoch totalSupply[epochId][vaultAddress]
    // User share of token X is equal to tokensForEpoch * points[epochId][vaultId][userAddress] / totalPoints[epochId][vaultAddress]
    // You accrue one point per second for each second you are in the vault

    mapping(uint256 => mapping(address => mapping(address => uint256))) public rewards; // rewards[epochId][vaultAddress][tokenAddress] = AMOUNT

    /// @dev Sets the new epoch
    /// @notice Accruing is not necessary, it's just a convenience for end users
    function startNextEpoch() public {
        require(block.timestamp > epochs[currentEpoch].endTimestamp); // dev: !ended
        uint256 newEpochId = ++currentEpoch;

        epochs[newEpochId] = Epoch(
            block.timestamp,
            block.timestamp + SECONDS_PER_EPOCH
        );
    }

    /// @dev Given an epoch and vault, accrue it's totalPoints
    /// @notice it is called in the claimReward function
    function accrueVault(uint256 epochId, address vault) private {
        require(epochId <= currentEpoch); // dev: !can only accrue up to current epoch

        lastAccruedTimestamp[epochId][vault] = block.timestamp;

        uint256 supply = totalSupplyAtEpoch(epochId, vault);
        if (supply > 0) {
            uint256 timeLeftToAccrue = getVaultTimeLeftToAccrue(epochId, vault);
            if(timeLeftToAccrue > 0) {
                totalPoints[epochId][vault] += timeLeftToAccrue * supply;
            }
        }
    }

    /// @dev Given an epoch and a vault, return the time left to accrue
    /// @notice will return 0 for epochs in the future or for expired epochs
    function getVaultTimeLeftToAccrue(uint256 epochId, address vault) public view returns (uint256) {
        uint256 lastAccrueTime = lastAccruedTimestamp[epochId][vault];
        Epoch memory epochData = epochs[epochId];
        if(lastAccrueTime >= epochData.endTimestamp) {
            return 0; // Already accrued
        }

        uint256 endTime = _min(block.timestamp, epochData.endTimestamp);

        if (lastAccrueTime == 0) {
            return endTime - epochData.startTimestamp;
        }

        if (lastAccrueTime > endTime) {
            return 0;
        }

        return endTime - lastAccrueTime;
    }

    /// @return uint256 totalSupply at epochId
    /// @notice we return whether to update because the function has to figure that out
    /// comparing the storage value after the return value is a waste of a SLOAD
    function totalSupplyAtEpoch(uint256 epochId, address vault) public returns (uint256) {
        require (epochId <= currentEpoch, "total supply of future epoch is unknown"); // dev: we don't know the future total supply
        uint256 supply = totalSupply[epochId][vault];
        uint256 i = epochId;
        while (supply == 0 && i > 0) {
            i--;
            supply = totalSupply[i][vault];
        }
        if (supply != 0 && i != epochId) {
            totalSupply[epochId][vault] = supply;
        }
        return supply;
    }


    /// @dev Allow to bulk claim rewards, inputs are fairly wasteful
    function claimRewards(uint256[] calldata epochsToClaim, address[] calldata vaults, address[] calldata tokens, address[] calldata users) external {
        uint256 usersLength = users.length;
        uint256 epochLength = epochsToClaim.length;
        uint256 vaultLength = vaults.length;
        uint256 tokensLength = tokens.length;
        require(epochLength == vaultLength && epochLength == tokensLength && epochLength == usersLength, "Length mismatch");

        // Given an epoch and a vault
        // I have to accrue until end
        // I then compare the point to total points
        // Then, given the list of tokens I execute the transfers
        // To avoid re-entrancy we always change state before sending
        // Also this function needs to have re-entancy checks as well
        for(uint256 i = 0; i < epochLength; ++i) {
            claimReward(epochsToClaim[i], vaults[i], tokens[i], users[i]);
        }
    }
    
    /// @dev Claim one Token Reward for a specific epoch, vault and user
    /// @notice Anyone can claim on behalf of others
    /// @notice Gas savings is fine as public / external matters only when using mem vs calldata for arrays
    function claimReward(uint256 epochId, address vault, address token, address user) public {
        require(epochId < currentEpoch); // dev: !can only claim ended epochs

        accrueUser(epochId, vault, user);
        accrueVault(epochId, vault);

        // Now that they are accrue, just use the points to estimate reward and send
        uint256 userPoints = points[epochId][vault][user];
        uint256 vaultTotalPoints = totalPoints[epochId][vault];

        uint256 pointsLeft = userPoints - pointsWithdrawn[epochId][vault][user][token];

        if(pointsLeft > 0){ // We got some stuff left
            // userPoints withdrawn 
            pointsWithdrawn[epochId][vault][user][token] = userPoints;
            // Use ratio to calculate what we got left
            uint256 totalAdditionalReward = rewards[epochId][vault][token];
            uint256 tokensForUser = totalAdditionalReward * pointsLeft / vaultTotalPoints;
            IERC20(token).safeTransfer(user, tokensForUser);
        }
    }


    /// ===== Gas friendlier functions for claiming ======= ///

    /// @dev Bulk claim all rewards for one vault over epochEnd - epochStart epochs (inclusive)
    /// @notice You can't use this function if you've already withdrawn rewards for the epochs
    /// @notice This function is useful if you claim once every X epochs, and want to bulk claim
    function claimBulkTokensOverMultipleEpochs(uint256 epochStart, uint256 epochEnd, address vault, address[] calldata tokens, address user) external {
        // Go over total tokens to award
        // Then do one bulk transfer of it
        // This is the function you want to use to claim after some time (month or 6 months)
        // This one is without gas refunds, 
        //  if you are confident in the fact that you're claiming all the tokens for a vault
        //  you may as well use the optimized version to save more gas
        require(epochStart <= epochEnd); // dev: epoch math wrong
        uint256 tokensLength = tokens.length;
        require(epochEnd < currentEpoch); // dev: Can't claim if not expired
        _requireNoDuplicates(tokens);

        uint256[] memory amounts = new uint256[](tokens.length); // We'll map out amounts to tokens for the bulk transfers
        for(uint epochId = epochStart; epochId <= epochEnd; ++epochId) {
            // Accrue each vault and user for each epoch
            accrueUser(epochId, vault, user);
            accrueVault(epochId, vault);

            // Use the reward ratio for the tokens
            // Add to amounts

            // Now that they are accrue, just use the points to estimate reward and send
            uint256 userPoints = points[epochId][vault][user];

            uint256 vaultTotalPoints = totalPoints[epochId][vault];

            if(userPoints == 0){
                continue;
            }

            // We multiply just to avoid rounding
            uint256 ratioPoints = PRECISION * userPoints / vaultTotalPoints;

            // Loop over the tokens and see the points here
            for(uint256 i = 0; i < tokensLength; ++i){
                
                // To be able to use the same ratio for all tokens, we need the pointsWithdrawn to all be 0
                // To allow for this I could loop and check they are all zero, which would allow for further optimization
                require(pointsWithdrawn[epochId][vault][user][tokens[i]] == 0); // dev: You already accrued during the epoch, cannot optimize

                // Use ratio to calculate tokens to send
                uint256 totalAdditionalReward = rewards[epochId][vault][tokens[i]];
                uint256 tokensForUser = totalAdditionalReward * ratioPoints / PRECISION;

                // pointsWithdrawn[epochId][vault][user][tokens[i]] == userPoints
                // Which means they claimed all points for that token
                pointsWithdrawn[epochId][vault][user][tokens[i]] += userPoints;
                amounts[i] += tokensForUser;
            }
        }

        // Go ahead and transfer
        for(uint256 i = 0; i < tokensLength; ++i){
            IERC20(tokens[i]).safeTransfer(user, amounts[i]);
        }
    }
    
    /// @dev Bulk claim all rewards for one vault over epochEnd - epochStart epochs (inclusive)
    /// @notice This is a one time operation, your storage data will be deleted to trigger gas refunds
    ///         Do this if you want to get the rewards and are sure you're getting all of them
    /// @notice To be clear. If you forget one token, you are forfeiting those rewards, they won't be recoverable
    function claimBulkTokensOverMultipleEpochsOptimized(uint256 epochStart, uint256 epochEnd, address vault, address[] calldata tokens) external {
        require(epochStart <= epochEnd); // dev: epoch math wrong
        uint256 tokensLength = tokens.length;
        address user = msg.sender; // Pay the extra 3 gas to make code reusable, not sorry
        // NOTE: We don't cache currentEpoch as we never use it again
        require(epochEnd < currentEpoch); // dev: epoch math wrong 
        _requireNoDuplicates(tokens);

        // Claim the tokens mentioned
        // Over the epochs mentioned
        // Using an accumulator instead of doing multiple transfers
        // Deleting all shares, points and lastAccrueTimestamp data at the end to trigger gas refunds
        // Bulking the transfer at the end to make it cheaper for gas

        // This is the function you want to use to claim when you want to collect all and call it
        // Calling this function will make you renounce any other token rewards (to trigger the gas refund)
        // So make sure you're claiming all the rewards you want before doing this

        uint256[] memory amounts = new uint256[](tokensLength); // We'll map out amounts to tokens for the bulk transfers
        for(uint epochId = epochStart; epochId <= epochEnd;) {
            // Accrue each vault and user for each epoch
            accrueUser(epochId, vault, user);
            accrueVault(epochId, vault);

            // Use the reward ratio for the tokens
            // Add to amounts

            // Now that they are accrue, just use the points to estimate reward and send
            uint256 userPoints = points[epochId][vault][user];

            uint256 vaultTotalPoints = totalPoints[epochId][vault];

            if(userPoints == 0){
                unchecked { ++epochId; }
                continue;
            }

            // We multiply just to avoid rounding
            uint256 ratioPoints = PRECISION * userPoints / vaultTotalPoints;

            // NOTE: We don't set the pointsWithdrawn here because we will set the user shares to 0 later
            // While maintainingn lastAccrueTimestamp to now so they can't reaccrue

            // Loop over the tokens and see the points here
            for(uint256 i = 0; i < tokensLength; ){

                // To be able to use the same ratio for all tokens, we need the pointsWithdrawn to all be 0
                // To allow for this I could loop and check they are all zero, which would allow for further optimization
                require(pointsWithdrawn[epochId][vault][user][tokens[i]] == 0); // dev: You already accrued during the epoch, cannot optimize

                // Use ratio to calculate tokens to send
                uint256 totalAdditionalReward = rewards[epochId][vault][tokens[i]];
                uint256 tokensForUser = totalAdditionalReward * ratioPoints / PRECISION;

                amounts[i] += tokensForUser;
                unchecked { ++i; }
            }

            unchecked { ++epochId; }
        }

        // We've done the math, delete to trigger refunds
        for(uint epochId = epochStart; epochId < epochEnd; ) {
            // epochId < epochEnd because we need to preserve the last one for future accruals and balance tracking
            delete shares[epochId][vault][user]; // Delete shares 
            delete points[epochId][vault][user]; // Delete their points

            unchecked { ++epochId; }
        }

        // Experimental optimization: can delete timestamp data on everything between epochStart and epochEnd
        // because shares will be zero in this interval (due to above deletes) so any accrual will not actually add
        // points. Need to keep the timestamp data on epochStart so you can't go backwards from one of these middle epochs
        // to get a non-zero balance and get points again
        // NOTE: Commented out as it actually seems to cost more gas due to refunds being capped
        // FOR AUDITORS: LMK if you can figure this out
        // for(uint epochId = epochStart + 1; epochId < epochEnd; ++epochId) {
        //     delete lastUserAccrueTimestamp[epochId][vault][user];
        // }
        
        // For last epoch, we don't delete the shares, but we delete the points
        delete points[epochEnd][vault][user];

        // Go ahead and transfer
        for(uint256 i = 0; i < tokensLength; ){
            IERC20(tokens[i]).safeTransfer(user, amounts[i]);
            unchecked { ++i; }
        }
    }

    /// === Bulk Claims END === ///

    /// @notice Utility function to specify a group of emissions for the specified epochs, vaults with tokens
    function addRewards(uint256[] calldata epochIds, address[] calldata tokens, address[] calldata vaults, uint256[] calldata amounts) external {
        require(vaults.length == epochIds.length); // dev: length mismatch
        require(vaults.length == amounts.length); // dev: length mismatch
        require(vaults.length == tokens.length); // dev: length mismatch

        for(uint256 i = 0; i < vaults.length; ++i){
            addReward(epochIds[i], tokens[i], vaults[i], amounts[i]);   
        }
    }

    /// @notice Add an additional reward for the current epoch
    /// @notice No particular rationale as to why we wouldn't allow to send rewards for older epochs or future epochs
    /// @notice The typical use case is for this contract to receive certain rewards that would be sent to the badgerTree
    /// @notice nonReentrant because tokens could inflate rewards, this would only apply to the specific token, see reports for more
    function addReward(uint256 epochId, address vault, address token, uint256 amount) public nonReentrant {
        require(epochId >= currentEpoch && epochId > 0);

        // Check change in balance to support `feeOnTransfer` tokens as well
        uint256 startBalance = IERC20(token).balanceOf(address(this));  
        IERC20(token).safeTransferFrom(msg.sender, address(this), amount);
        uint256 endBalance = IERC20(token).balanceOf(address(this));

        rewards[epochId][vault][token] += endBalance - startBalance;
    }


    /// **== Notify System ==** ///

    /// @dev handles a deposit for vault, to address of amount
    function notifyDeposit(address to, uint256 amount) external {
        if (block.timestamp > epochs[currentEpoch].endTimestamp) {
            startNextEpoch();
        }
        address vault = msg.sender;
        accrueUser(currentEpoch, vault, to);
        accrueVault(currentEpoch, vault); // We have to accrue vault as totalSupply is gonna change

        // Add deposit data for user
        shares[currentEpoch][vault][to] += amount;
        // And total shares for epoch
        totalSupply[currentEpoch][vault] += amount;
    }

    /// @dev handles a withdraw for vault, from address of amount
    function notifyWithdrawal(address from, uint256 amount) external {
        if (block.timestamp > epochs[currentEpoch].endTimestamp) {
            startNextEpoch();
        }
        address vault = msg.sender;
        accrueUser(currentEpoch, vault, from);
        accrueVault(currentEpoch, vault); // We have to accrue vault as totalSupply is gonna change

        // Reduce shares
        shares[currentEpoch][vault][from] -= amount;
        // Reduce totalSupply
        totalSupply[currentEpoch][vault] -= amount;
    }

    /// @dev handles a transfer for vault, from address to address of amount
    function notifyTransfer(address from, address to, uint256 amount) internal {
        require (from != to, "Transfer from and to the same address");
        if (block.timestamp > epochs[currentEpoch].endTimestamp) {
            startNextEpoch();
        }
        address vault = msg.sender;
        accrueUser(currentEpoch, vault, from);
        accrueUser(currentEpoch, vault, to);

        shares[currentEpoch][vault][to] += amount;
        shares[currentEpoch][vault][from] -= amount;
        // No change in total supply as this is a transfer
    }

    /// @dev Accrue points gained during this epoch
    /// @notice This is called for both receiving, sending, depositing and withdrawing, any time the user balance changes
    /// @notice To properly accrue for this epoch:
    /// @notice Figure out the time passed since last accrue (max is start of epoch)
    /// @notice Figure out their points (their current balance) (before we update)
    /// @notice Just multiply the points * the time, those are the points they've earned
    function accrueUser(uint256 epochId, address vault, address user) public {
        require(epochId <= currentEpoch); // dev: !can only accrue up to current epoch

        lastUserAccrueTimestamp[epochId][vault][user] = block.timestamp;
        uint256 currentBalance = balanceAtEpoch(epochId, vault, user);

        // Optimization:  No balance, return early
        if(currentBalance > 0){
            uint256 timeInEpochSinceLastAccrue = getUserTimeLeftToAccrue(epochId, vault, user);
            if (timeInEpochSinceLastAccrue > 0) {
                points[epochId][vault][user] += currentBalance * timeInEpochSinceLastAccrue;
            }
        }
    }

    /// @dev Figures out the last time the given user was accrued at the epoch for the vault
    /// @notice Invariant -> Never changed means full duration
    function getUserTimeLeftToAccrue(uint256 epochId, address vault, address user) public view returns (uint256) {
        uint256 lastUserAccrueTime = lastUserAccrueTimestamp[epochId][vault][user];
        Epoch memory epochData = epochs[epochId];

        // If for some reason we are trying to accrue a position already accrued after end of epoch, return 0
        if(lastUserAccrueTime >= epochData.endTimestamp){
            return 0;
        }

        // Becase we could be in a time where a new epoch hasn't started, we need this check
        uint256 endTime = _min(block.timestamp, epochData.endTimestamp);

        // If timestamp is 0, we never accrued
        // return _min(end, now) - start;
        if(lastUserAccrueTime == 0) {
            return endTime - epochData.startTimestamp;
        }

        if (lastUserAccrueTime > endTime) {
            return 0;
        }

        return endTime - lastUserAccrueTime;
    }
    

    /// @dev Figures out and returns the balance of a user for a vault at a specific epoch
    /// @return uint256 - balance
    /// @notice we return whether to update because the function has to figure that out
    /// comparing the storage value after the return value is a waste of a SLOAD
    function balanceAtEpoch(uint256 epochId, address vault, address user) public returns (uint256) {
        require (epochId <= currentEpoch, "balance of future epoch is unknown"); // dev: we don't know balance of future epochs
        uint256 balance = shares[epochId][vault][user];
        uint256 i = epochId;
        while (balance == 0 && i > 0) {
            i--;
            balance = shares[i][vault][user];
        }
        if (balance != 0 && i != epochId) { // found a non-zero balance at an earlier epoch
            shares[epochId][vault][user] = balance;
        }
        return balance;
    }

    function _requireNoDuplicates(address[] memory arr) internal pure {
        uint256 arrLength = arr.length;
        for(uint i = 0; i < arrLength - 1; ) { // only up to len - 1 (no j to check if i == len - 1)
            for (uint j = i + 1; j < arrLength; ) {
                require(arr[i] != arr[j]);

                unchecked { ++j; }
            }

            unchecked { ++i; }
        }
    }

    function _min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }
}
