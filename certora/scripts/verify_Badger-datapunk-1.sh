certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badger-datapunk-1.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc8.10  \
    --send_only \
    --cloud \
    --optimistic_loop \
    --loop_iter 2 \
    --msg "$(basename $BASH_SOURCE)"
