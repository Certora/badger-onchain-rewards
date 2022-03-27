solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badger-datapunk-1.spec \
    --optimistic_loop \
    --loop_iter 2 \
    --packages @oz=certora/openzeppelin/contracts 
    #  \
    # --rule "$1" \
    # --msg "$1"
