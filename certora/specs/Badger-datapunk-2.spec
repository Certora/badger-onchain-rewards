// Check Points - This is really long running

import "erc20.spec"
import "rewardsManagerMethods.spec"

/*
Rules: sumPointsOverEV_Eq_TotalPoints
Property: Valid state 
Explanation: When all users accrue to the same timestamp as the vault, the sum of all users' points should be equivalent to the totalPoints of the vault
Priority: High
Justification: if this rule fails, it means that points system is broken
*/
ghost sumPointsOverEV(uint256, address) returns uint256 {
	init_state axiom forall uint256 E. forall address V. sumPointsOverEV(E, V) == 0;
}

hook Sstore points[KEY uint256 e][KEY address v][KEY address u] uint256 ps(uint256 old_ps) STORAGE {
	havoc sumPointsOverEV assuming forall uint256 E. forall address V.  
        (e == E && v==V => sumPointsOverEV@new(E, V) == sumPointsOverEV@old(E, V) - old_ps + ps) &&
        (e != E || v!=V => sumPointsOverEV@new(E, V) == sumPointsOverEV@old(E, V));
}


rule test_sumPointsEqTotalPoints(uint256 e, address v, method f) {
    uint256 _lastAccruedTimestamp = getLastAccruedTimestamp(e, v);
    uint256 _sumPointsOverEV = sumPointsOverEV(e, v);
    uint256 _totalPoints = getTotalPoints(e, v);
    require _totalPoints == 1;
    
    require forall address u. getLastUserAccrueTimestamp(e, v, u) == _lastAccruedTimestamp;
    require _sumPointsOverEV == _totalPoints;
    
    env ev;
    require _lastAccruedTimestamp == ev.block.timestamp && ev.block.timestamp!=0;
    calldataarg args;
    f(ev,args);

    uint256 lastAccruedTimestamp_ = getLastAccruedTimestamp(e, v);
    uint256 sumPointsOverEV_ = sumPointsOverEV(e, v);
    uint256 totalPoints_ = getTotalPoints(e, v);

    if (f.selector != claimBulkTokensOverMultipleEpochsOptimized(uint256, uint256, address, address[]).selector) {
        assert (forall address u. getLastUserAccrueTimestamp(e, v, u)==lastAccruedTimestamp_)
            => sumPointsOverEV_ == totalPoints_, "points do not add up";
    } else {
        assert (forall address u. getLastUserAccrueTimestamp(e, v, u)==lastAccruedTimestamp_)
            => sumPointsOverEV_ <= totalPoints_, "points do not add up";
    }
}   
