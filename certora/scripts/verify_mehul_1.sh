certoraRun certora/harnesses/RewardsManagerHarnessMehul.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessMehul:certora/specs/Badger_mehul_1.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc8.10  \
    --send_only \
    --cloud \
    --optimistic_loop \
    --loop_iter 1 \
    --msg "$(basename $BASH_SOURCE)"
