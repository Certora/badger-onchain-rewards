certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badgerissues_kuldeep.spec \
    --solc solc8.10  \
    --optimistic_loop \
    --cloud \
    --send_only \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --rule user_able_to_accrue_points_transferring_to_himself \
    --msg "user_able_to_accrue_points_transferring_to_himself"
