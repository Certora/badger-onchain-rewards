solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badger-datapunk-2.spec \
    --optimistic_loop \
    --loop_iter 2 \
    --packages @oz=certora/openzeppelin/contracts \
    --short_output
    #  \
    # --rule "$1" \
    # --msg "$1"
