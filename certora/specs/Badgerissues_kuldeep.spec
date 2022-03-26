import "base.spec"

// notify_transfer_work_as_expected rule in BadgerKuldeep_1.spec file acted strangely for case when from == to == 0
// which leads to thinking what will happen when from == to, not necessarily 0.

// handle transfer allows from == to
// and this seems to be increasing users points which means any user can transfer to himself
// to earn more points which eventually means rewards tokens.

// This can be fixed by the contract using the Reward Manager contract by checking from != to on their side
// but will be better to put this check in the handleTransfer method of the Reward Manager contract.


rule user_able_to_accrue_points_transferring_to_himself() {
    env e;

    uint256 epochId = currentEpoch();
    address vault;
    
    address from; 
    address to;

    require from == to;
    require from != 0 && to != 0;

    address user;
    uint256 amount;

    require amount > 0;
    
    uint256 userPointsBeforeTransfer = getPoints(epochId, vault, user);

    handleTransfer(e,vault, from, to,amount);

    uint256 userPointsAfterTransfer = getPoints(epochId, vault, user);

    assert userPointsAfterTransfer == userPointsBeforeTransfer, "user should not get points for transferring to himself";
}

