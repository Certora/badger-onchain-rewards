certoraRun certora/harnesses/RewardsManagerHarnessThrottle.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessThrottle:certora/specs/BadgerThrottle2.spec \
    --solc solc8.10  \
    --optimistic_loop \
    --loop_iter 2 \
    --short_output \
    --packages @oz=certora/openzeppelin/contracts \
    --send_only \
    --cloud \
    --msg "$(basename $BASH_SOURCE)"
