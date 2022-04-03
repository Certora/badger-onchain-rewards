import "erc20.spec"
import "RMBase.spec"



/********************************
*                               *
*          ADDREWARDS           * 
*                               *
********************************/

// STATUS: VERIFIED
/// PROPERTY 23
// checks addRewards function correctly 
rule sanityOfAddReward(uint256 epoch, address vault, address token, uint256 amount){
    env e;
    uint256 rewardsBefore = getRewards(epoch, vault, token);
    uint256 balanceBefore = tokenBalanceOf(token, currentContract);
    addReward(e, epoch, vault, token, amount);
    uint256 rewardsAfter = getRewards(epoch, vault, token);
    uint256 balanceAfter = tokenBalanceOf(token, currentContract);
    assert rewardsAfter + balanceBefore == rewardsBefore + balanceAfter, "addReward malfunction";
    assert e.msg.sender != currentContract => rewardsAfter == rewardsBefore + amount, "addReward malfunction";
}

// STATUS: VERIFIED
// checks addReward cant be called for past epochs
rule correctAddRewardRevert(uint256 epoch, address vault, address token, address user){
    env e;
    uint currentEp = currentEpoch();
    addReward@withrevert(e, epoch, vault,token, user);
    assert epoch < currentEp => lastReverted, "addReward should revert";
}

// STATUS: FAILS
// token and vault args are swapped in addRewards function !
// PROPERTY 38
// STATUS FIX CONTRACT:  VERIFIED
rule sanityOfAddRewards(uint256[] epochs, address[] vaults, address[] tokens, uint256[] amounts){
    env e;

    require epochs.length == vaults.length && epochs.length == tokens.length && epochs.length == amounts.length;
    require epochs.length == 1;
    uint256 epoch = epochs[0];
    address vault = vaults[0];
    address token = tokens[0]; 
    uint256 amount = amounts[0];
    uint256 rewardsBefore = getRewards(epoch, vault, token); 
    uint256 balanceBefore = tokenBalanceOf(token, currentContract); 
    addRewards(e, epochs, vaults, tokens, amounts); 
    uint256 rewardsAfter = getRewards(epoch, vault, token);
    uint256 balanceAfter = tokenBalanceOf(token, currentContract);
    assert rewardsAfter + balanceBefore == rewardsBefore + balanceAfter, "addRewards malfunction";
    assert e.msg.sender != currentContract => rewardsAfter == rewardsBefore + amount, "addRewards malfunction";

}



/********************************
*                               *
*         NOTIFYTRANSFER        *
*                               *
********************************/
// STATUS: VERIFIED
// PROPERTY 43
// checks integrity of handleDeposit function  
rule integrityOfHandleDeposit(address vault, address to, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    uint256 sharesBefore = getShares(epoch, vault, to);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    handleDeposit(e, vault, to, amount);
    uint256 sharesAfter = getShares(epoch, vault, to);
    uint256 supplyAfter = getTotalSupply(epoch, vault);
    assert sharesAfter == sharesBefore + amount, "wrong change in shares";
    assert supplyAfter == supplyBefore + amount, "wrong change in supply";
    assert getLastAccruedTimestamp(epoch, vault) == e.block.timestamp, "wrong update to vault accrue timestamp";
    assert getLastUserAccrueTimestamp(epoch, vault, to) == e.block.timestamp, "wrong update vault accrue user timestamp";
}

// STATUS: VERIFIED
// PROPERTY 44
// checks integrity of handleWithdrawal function  
rule integrityOfHandleWithdrawal(address vault, address from, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    uint256 sharesBefore = getShares(epoch, vault, from);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    handleWithdrawal(e, vault, from, amount);
    uint256 sharesAfter = getShares(epoch, vault, from);
    uint256 supplyAfter = getTotalSupply(epoch, vault);
    assert sharesAfter == sharesBefore - amount, "wrong change in shares";
    assert supplyAfter == supplyBefore - amount, "wrong change in supply";
    assert getLastAccruedTimestamp(epoch, vault) == e.block.timestamp, "wrong update to vault accrue timestamp";
    assert getLastUserAccrueTimestamp(epoch, vault, from) == e.block.timestamp, "wrong update vault accrue user timestamp";
}


// STATUS: VERIFIED
// PROPERTY 45
// checks integrity of handleTransfer function  
rule integrityOfHandleTransfer(address vault, address from, address to, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    uint256 sharesFromBefore = getShares(epoch, vault, from);
    uint256 sharesToBefore = getShares(epoch, vault, to);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    handleTransfer(e, vault, from, to, amount);
    uint256 sharesFromAfter = getShares(epoch, vault, from);
    uint256 sharesToAfter = getShares(epoch, vault, to);
    uint256 supplyAfter = getTotalSupply(epoch, vault);
    assert from != to => sharesToAfter == sharesToBefore + amount, "wrong change in shares To";
    assert from != to => sharesFromAfter == sharesFromBefore - amount, "wrong change in shares From";
    assert from == to => sharesFromAfter == sharesFromBefore , "wrong change in shares ";
    assert supplyAfter == supplyBefore , "wrong change in supply";
    assert getLastUserAccrueTimestamp(epoch, vault, from) == e.block.timestamp, "wrong update vault accrue user timestamp";
    assert getLastUserAccrueTimestamp(epoch, vault, to) == e.block.timestamp, "wrong update vault accrue user timestamp";
}

// STATUS: VERIFIED
// PROPERTY 25
// We check case either from or to are non zero
// NOTE: the block.timestamp updates are not verified by the proved
// it seems he has hard time and over approximate this when there is a call to another internal function
// checks integrity of handleTransfer function  
rule integrityOfNotifyTransfer( address from, address to, uint amount){
    env e;
    uint256 epoch = currentEpoch();
    address vault = e.msg.sender;
    uint256 sharesFromBefore = getShares(epoch, vault, from);
    uint256 sharesToBefore = getShares(epoch, vault, to);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    notifyTransfer(e, from, to, amount);
    uint256 sharesFromAfter = getShares(epoch, vault, from);
    uint256 sharesToAfter = getShares(epoch, vault, to);
    uint256 supplyAfter = getTotalSupply(epoch, vault);

    require from != 0 || to != 0;

    assert from == 0 => ((sharesToAfter == sharesToBefore + amount) && (supplyAfter == supplyBefore + amount)), "something wrong with _handleDeposit amount updates";
    //assert from == 0 =>( getLastUserAccrueTimestamp(epoch, vault, to) >= e.block.timestamp && getLastAccruedTimestamp(epoch, vault) >= e.block.timestamp), "something wrong with _handleDeposit accrual updates";
    assert (to == 0) => ((sharesFromAfter == sharesFromBefore - amount) && (supplyAfter == supplyBefore - amount)), "something wrong with _handleWithdrawal amount updates";  
    //assert to == 0 =>( getLastUserAccrueTimestamp(epoch, vault, from) >= e.block.timestamp && getLastAccruedTimestamp(epoch, vault) >= e.block.timestamp), "something wrong with _handleWithdrawal accrual updates";
    assert (to != 0 && from != 0 && to != from) => ((sharesToAfter == sharesToBefore + amount) && (sharesFromAfter == sharesFromBefore - amount) && (supplyAfter == supplyBefore )), "something wrong with _handleTransfer amount updates";  
    assert (to != 0 && from != 0 && to == from) => ((sharesToAfter == sharesToBefore ) &&  (supplyAfter == supplyBefore )), "something wrong with _handleTransfer when to = from amount updates";  

    //assert (to != 0 && from != 0) =>( getLastUserAccrueTimestamp(epoch, vault, from) >= e.block.timestamp && getLastUserAccrueTimestamp(epoch, vault, to) >= e.block.timestamp), "something wrong with _handleTransfer accrual updates";
}


// STATUS: FAILS
// PROPERTY 25
// malicious vault can inflate supply
// We check case either from and to are both zero
// it seems he has hard time and over approximate this when there is a call to another internal function
// checks integrity of handleTransfer function  
rule integrityOfNotifyTransferZero(uint amount){
    env e;
    uint256 epoch = currentEpoch();
    address vault = e.msg.sender;
    uint256 sharesBefore = getShares(epoch, vault, 0);
    uint256 supplyBefore = getTotalSupply(epoch, vault);
    notifyTransfer(e, 0, 0, amount);
    uint256 sharesAfter = getShares(epoch, vault, 0);
    uint256 supplyAfter = getTotalSupply(epoch, vault);


    assert supplyAfter == supplyBefore && sharesBefore == sharesAfter, "something wrong with this case";

    //assert (to != 0 && from != 0) =>( getLastUserAccrueTimestamp(epoch, vault, from) >= e.block.timestamp && getLastUserAccrueTimestamp(epoch, vault, to) >= e.block.timestamp), "something wrong with _handleTransfer accrual updates";
}


/********************************
*                               *
*      REQUIRENODUPLICATES      *
*                               *
********************************/

// STATUS: Verified
// PROPERTY 46
// checking sanity of internal function
rule sanityOfrequireNoDuplicates(address[] arr) {
    uint l = arr.length;
    requireNoDuplicates@withrevert(arr);

    uint i;
    uint j;

    assert (i != j && arr[i] == arr[j] && i < l && j < l ) => lastReverted;
}



/********************************
*                               *
*           accrueUser          *
*                               *
********************************/

// STATUS: unVerified
// PROPERTY 32
// checking accrueUser revert for futur epochs
rule correctaccrueUserRevert(uint256 epoch, address vault, address user) {
    env e;
    uint256 currentEp = currentEpoch();
    accrueUser@withrevert(e, epoch, vault, user);



    assert epoch > currentEp => lastReverted, "accrue user should revert";
}


/********************************
*                               *
*           accrueVault          *
*                               *
********************************/

// STATUS: unVerified
// PROPERTY 34
// checking accrueVault revert for futur epochs
rule correctaccrueVaultRevert(uint256 epoch, address vault) {
    env e;
    uint256 currentEp = currentEpoch();
    accrueVault@withrevert(e, epoch, vault);
    assert epoch > currentEp => lastReverted, "accrue vault should revert";
}


// STATUS: unVerified
// PROPERTY 
// checking accrueVault revert for futur epochs
rule sanityOfAccrueVault(uint256 epoch, address vault) {
    env e;
    uint256 totalPointsBefore = getTotalPoints(epoch, vault);
    accrueVault(e, epoch, vault);
    uint256 totalPointsAfter = getTotalPoints(epoch, vault);
    uint256 totalSup = getTotalSupply(epoch, vault);


    assert totalSup > 0 => totalPointsAfter > totalPointsBefore, "accrue vault should revert";
}


/********************************
*                               *
*     getTotalSupplyAtEpoch     *
*                               *
********************************/

// STATUS: Verified
// checking getTotalSupplyAtEpoch return correct shouldUpdate value
rule correctShouldUpdateVaultReturn(uint256 epoch, address vault) {
    env e;
    bool shouldUpdate = getShouldUpdateVault(epoch, vault);
    uint lastAccrueEpoch;
    assert (lastAccrueEpoch > 0 && lastAccrueEpoch <= epoch && getLastAccruedTimestamp(lastAccrueEpoch, vault) != 0 && getLastAccruedTimestamp(epoch, vault) == 0 ) => shouldUpdate, "something wrong with the function return";
}


/********************************
*                               *
*     getBalanceAtEpoch     *
*                               *
********************************/

// STATUS: Verified
// checking getBalanceAtEpoch return correct shouldUpdate value
rule correctShouldUpdateUserReturn(uint256 epoch, address vault, address user) {
    env e;
    bool shouldUpdate = getShouldUpdateUser(epoch, vault, user);
    uint lastAccrueEpoch;
    assert (lastAccrueEpoch > 0 && lastAccrueEpoch <= epoch && getLastUserAccrueTimestamp(lastAccrueEpoch, vault, user) != 0 && getLastUserAccrueTimestamp(epoch, vault, user) == 0 ) => shouldUpdate, "something wrong with the function return";
}


/********************************
*                               *
*             min               *
*                               *
********************************/


// STATUS: Verified
// PROPERTY 47
// checking sanity of internal function
rule sanityOfMin(uint a, uint b) {
    uint min_a_b = min(a, b);

    assert a < b => a == min_a_b, "wrong min function";
}

/********************************
*                               *
*   getVaultTimeLeftToAccrue    *
*                               *
********************************/

// STATUS: unVerified
// have to add some requierements
// checking getBalanceAtEpoch return correct shouldUpdate value
rule vaultTimeLeftToAccrueUpperBound(uint256 epoch, address vault) {
    env e;
    uint timeLeft = getVaultTimeLeftToAccrue(e, epoch, vault);
    assert timeLeft < 68400, "something wrong with the function return";
}


/********************************
*                               *
*   getUserTimeLeftToAccrue    *
*                               *
********************************/

// STATUS: unVerified
// have to add some requierements
// checking getBalanceAtEpoch return correct shouldUpdate value
rule userTimeLeftToAccrueUpperBound(uint256 epoch, address vault, address user) {
    env e;
    uint timeLeft = getUserTimeLeftToAccrue(e, epoch, vault, user);
    assert timeLeft < 68400, "something wrong with the function return";
}


/********************************
*                               *
*         CLAIM REWARD*S         *
*                               *
********************************/


// STATUS: VERIFIED
// PROPERTY 36
// checks claimReward cant be called for present or futur epochs
rule correctClaimRewardRevert(uint256 epoch, address vault, address token, address user){
    env e;
    uint currentEp = currentEpoch();
    claimReward@withrevert(e, epoch, vault,token, user);
    assert epoch >= currentEp => lastReverted, "claimReward should revert";
}

// STATUS: VERIFIED
// PROPERTY 36
// checks claimRewards cant be called for present or futur epochs
rule correctClaimRewardsRevert(uint256[] epochs, address[] vaults, address[] tokens, address[] users){
    env e;
    require epochs.length == 1 && vaults.length == 1 && tokens.length == 1 && users.length == 1;
    uint currentEp = currentEpoch();
    uint epoch = epochs[0];
    claimRewards@withrevert(e, epochs, vaults, tokens, users);
    assert epoch >= currentEp => lastReverted, "claimRewards should revert";
}


// STATUS: VERIFIED
// PROPERTY 37
// checks claimReward cant give correct token amount to user
rule sanityOfClaimRewardTokens(uint256 epoch, address vault, address token) {
    env e;
    require e.msg.sender != currentContract;
    address user = e.msg.sender;
    uint256 tokenBalanceBefore = tokenBalanceOf(token, user);
    uint256 tokensForUser = getTokenReward(e, epoch, vault, token, user);

    claimReward(e, epoch, vault, token, user);

    uint256 tokenBalanceAfter = tokenBalanceOf(token, user);

    assert tokenBalanceAfter == tokensForUser + tokenBalanceBefore, "something wrong with claimReward tokens received";

}

rule sanityOfClaimRewardPoints(uint256 epoch, address vault, address token) {
    env e;
    require e.msg.sender != currentContract;
    address user = e.msg.sender;
    
    uint256 pointsWithdrawnBefore = getPointsWithdrawn(epoch, vault, token, user);
    uint256 pointsLeft = getPointsLeft(e, epoch, vault, token, user);

    claimReward(e, epoch, vault, token, user);

    uint256 pointsWithdrawnAfter = getPointsWithdrawn(epoch, vault, token, user);

    assert pointsWithdrawnAfter == pointsWithdrawnBefore + pointsLeft, "something wrong with claimReward pointWithdrawn increase received";

}

