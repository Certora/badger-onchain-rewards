solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/itsLikeAReward.spec \
    --send_only \
    --loop_iter 2 \
--staging    --packages @oz=certora/openzeppelin/contracts \
    --msg "$1"
