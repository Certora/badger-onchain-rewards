certoraRun certora/harnesses/RewardsManagerHarnessMehul.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessMehul:certora/specs/Badgerissues_mehul.spec \
    --send_only \
    --solc solc8.10  \
    --optimistic_loop \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --cloud \
    --msg "$(basename $BASH_SOURCE)"
