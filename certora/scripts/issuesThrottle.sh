certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/BadgerissuesThrottle.spec \
    --solc solc-0.8.10 \
    --optimistic_loop \
    --packages @oz=certora/openzeppelin/contracts \
    # --rule accrueUserShouldUpdateUserShares \
    --msg "$1"
