certoraRun certora/harnesses/RewardsManagerHarnessBaraa.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessBaraa:certora/specs/Badger_Baraa42_1.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc8.10  \
    --send_only \
    --cloud \
    --optimistic_loop \
    --loop_iter 2 \
    --msg "$(basename $BASH_SOURCE)"
