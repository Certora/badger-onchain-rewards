solc-select use 0.8.10

certoraRun contracts/RewardsManager.sol:RewardsManager \
  --verify RewardsManager:certora/specs/Badgerissues_mehul.spec \
  --send_only \
  --optimistic_loop \
  --packages @oz=certora/openzeppelin/contracts \
  --msg "$1" $2