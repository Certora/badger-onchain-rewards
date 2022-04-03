certoraRun certora/harnesses/RewardsManagerHarnessBaraa.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessBaraa:certora/specs/Badger_Baraa42_2.spec \
    --solc solc8.10  \
    --optimistic_loop \
    --loop_iter 2 \
    --packages @oz=certora/openzeppelin/contracts \
    --send_only \
--staging    --cloud \
    --msg "$(basename $BASH_SOURCE)"
