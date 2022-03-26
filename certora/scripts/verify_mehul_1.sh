solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badger_mehul_1.spec \
    --send_only \
    --optimistic_loop \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --msg "$1" $2

#     --loop_iter 2   --rule $1 \