certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/RM_highlevel.spec \
    --solc solc8.10  \
    --optimistic_loop \
    --loop_iter 2 \
    --packages @oz=certora/openzeppelin/contracts \
    --send_only \
    --cloud \
    --rule "$1" \
    --msg "$2"
