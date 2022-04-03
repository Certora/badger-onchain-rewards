import "erc20.spec"
import "RMBase.spec"


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

// NOTE: I broke rule verification in two parts
// Part 1 is ok
// Part 2 fails
// for handleTransfer if both to = from = 0 then totalSupply can be inflated artificially 
// this issue depends on the implementation of the vault contract
// in most cases it is ok
// but it preferable to be explicit and add require ( to != 0 || from != 0) in handleTransfer function
// also there is not check on amount != 0 which lead to waste of gas
// see: https://docs.google.com/document/d/1rP8IqMvUNj2Mzc5xuDovQoNL1PQJrZe2fqPFHO_stmo/edit#heading=h.4d34og8

// STATUS: VERIFIED
// PROPERTY 25
// We check case either from or to are non zero
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
    assert (to == 0) => ((sharesFromAfter == sharesFromBefore - amount) && (supplyAfter == supplyBefore - amount)), "something wrong with _handleWithdrawal amount updates";  
    assert (to != 0 && from != 0 && to != from) => ((sharesToAfter == sharesToBefore + amount) && (sharesFromAfter == sharesFromBefore - amount) && (supplyAfter == supplyBefore )), "something wrong with _handleTransfer amount updates";  
    assert (to != 0 && from != 0 && to == from) => ((sharesToAfter == sharesToBefore ) &&  (supplyAfter == supplyBefore )), "something wrong with _handleTransfer when to = from amount updates";  
}


// STATUS: FAILS
// PROPERTY 25
// malicious vault can inflate supply
// We check case either from and to are both zero
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

}