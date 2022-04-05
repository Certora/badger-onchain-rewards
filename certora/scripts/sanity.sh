certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/sanity.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc8.10 \
    --cloud \
    --optimistic_loop \
    --msg "$1"
