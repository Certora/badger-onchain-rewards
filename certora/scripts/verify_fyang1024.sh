certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badger_fyang1024.spec \
    --solc solc8.10 \
    --optimistic_loop \
    --cloud \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --msg "$1"