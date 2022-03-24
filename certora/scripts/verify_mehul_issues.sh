solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badgerissues_mehul.spec \
    --send_only \
    --optimistic_loop \
    --packages @oz=certora/openzeppelin/contracts \
    --rule sumOfUserBalancesShouldMatchTotalSupply \
    --msg "${1}"

    #     --rule rewardsMatchCalculation \ runs for >30 min