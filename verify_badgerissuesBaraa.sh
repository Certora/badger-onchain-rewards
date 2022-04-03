certoraRun certora/harnesses/RewardsManagerHarnessBaraa.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessBaraa:certora/specs/Badgerissues_Baraa42.spec \
    --solc solc8.10  \
    --optimistic_loop \
    --loop_iter 1 \
    --packages @oz=certora/openzeppelin/contracts \
    --send_only \
    --cloud \
    --msg "$(basename $BASH_SOURCE)"
