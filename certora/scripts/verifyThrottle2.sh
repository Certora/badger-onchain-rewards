certoraRun certora/harnesses/RewardsManagerHarnessThrottle.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessThrottle:certora/specs/BadgerThrottle2.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc8.10  \
    --send_only \
    --short_output \
    --cloud \
    --optimistic_loop \
    --loop_iter 2 \
    --msg "$(basename $BASH_SOURCE)"
