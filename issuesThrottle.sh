certoraRun certora/harnesses/RewardsManagerHarnessThrottle.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessThrottle:certora/specs/BadgerissuesThrottle.spec \
    --solc solc8.10 \
    --optimistic_loop \
    --packages @oz=certora/openzeppelin/contracts \
    --send_only \
--staging    --cloud \
    --msg "$(basename $BASH_SOURCE)"
