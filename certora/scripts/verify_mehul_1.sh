solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badger_mehul_1.spec \
    --send_only \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --msg "$1"

#     --loop_iter 2 \