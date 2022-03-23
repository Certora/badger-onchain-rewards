solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/itsLikeAReward.spec \
    --optimistic_loop \
    --send_only \
    --packages @oz=certora/openzeppelin/contracts \
    --msg "$1"
