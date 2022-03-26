certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badgerissues_kuldeep.spec \
    --solc ~/solc/0.8.10/solc-macos \
    --optimistic_loop \
    --cloud \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --rule user_able_to_accrue_points_transferring_to_himself \
    --msg "user_able_to_accrue_points_transferring_to_himself"
