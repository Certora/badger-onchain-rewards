// Check Shares

import "erc20.spec"
import "rewardsManagerMethods.spec"

/*
Rules: sumSharesOverEV_Eq_TotalSupply
Property: Valid state 
Explanation: When all users accrue to the same timestamp as the vault, the sum of all users' shares should be equivalent to the totalShares of the vault
Priority: High
Justification: if this rule fails, it means that points system is broken
*/
ghost sumSharesOverEV(uint256, address) returns uint256 {
	init_state axiom forall uint256 E. forall address V. sumSharesOverEV(E, V) == 0;
}

hook Sstore shares[KEY uint256 e][KEY address v][KEY address u] uint256 ps(uint256 old_ps) STORAGE {
	havoc sumSharesOverEV assuming forall uint256 E. forall address V.  
        (e == E && v==V => sumSharesOverEV@new(E, V) == sumSharesOverEV@old(E, V) - old_ps + ps) &&
        (e != E || v!=V => sumSharesOverEV@new(E, V) == sumSharesOverEV@old(E, V));
}


rule test_sumSharesEqTotalSupply(uint256 e, address v, method f) {
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(e, v);
    uint256 _sumSharesOverEV = sumSharesOverEV(e, v);
    uint256 _totalSupply = getTotalSupply(e, v);
    require forall address u. getLastUserAccrueTimestamp(e, v, u)==_lastAccruedTimestamp;
    require _sumSharesOverEV == _totalSupply;

    env ev;
    require _lastAccruedTimestamp == ev.block.timestamp && ev.block.timestamp!=0;
    calldataarg args;
    f(ev,args);

    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(e, v);
    uint256 sumSharesOverEV_ = sumSharesOverEV(e, v);
    uint256 totalSupply_ = getTotalSupply(e, v);

    if (f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector) {
        assert (forall address u. getLastUserAccrueTimestamp(e, v, u)==lastAccruedTimestamp_)
            => sumSharesOverEV_ == totalSupply_, "shares do not add up";
    } else {
        assert (forall address u. getLastUserAccrueTimestamp(e, v, u)==lastAccruedTimestamp_)
            => sumSharesOverEV_ <= totalSupply_, "shares do not add up";
    }
}   


