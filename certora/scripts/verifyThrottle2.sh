certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/BadgerThrottle2.spec \
    --solc solc-0.8.10 \
    --optimistic_loop \
    --loop_iter 2 \
    --cloud \
    --short_output \
    --packages @oz=certora/openzeppelin/contracts \
    --short_output \
    # --rule claimBulkTokensOverMultipleEpochsUnitTest \
    --msg "$1"
