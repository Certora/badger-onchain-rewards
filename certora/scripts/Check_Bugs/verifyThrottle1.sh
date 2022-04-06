certoraRun certora/harnesses/RewardsManagerHarnessThrottle.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessThrottle:certora/specs/BadgerThrottle1.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc8.10  \
    --send_only \
    --short_output \
    --cloud \
    --optimistic_loop \
    --msg "$(basename $BASH_SOURCE)"
