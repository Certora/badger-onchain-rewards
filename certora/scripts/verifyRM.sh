solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarnessTeryanarmen.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/itsLikeAReward.spec \
    --solc solc \
    --optimistic_loop \
    --send_only \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --msg "$1"
