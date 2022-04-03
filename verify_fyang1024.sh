certoraRun certora/harnesses/RewardsManagerHarnessFyang.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessFyang:certora/specs/Badger_fyang1024.spec \
    --solc solc8.10 \
    --optimistic_loop \
    --cloud \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --send_only \
    --msg "$(basename $BASH_SOURCE)"