solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarnessTeryanarmen.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/check_effects.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc \
    --cloud \
    --optimistic_loop \
    --msg "$1"