certoraRun certora/harnesses/RewardsManagerHarnessTeryanarmen.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessTeryanarmen:certora/specs/BadgerissuesTeryanarmen.spec \
    --solc solc8.10 \
    --optimistic_loop \
    --packages @oz=certora/openzeppelin/contracts \
    --send_only \
    --cloud \
    --msg "$(basename $BASH_SOURCE)"
    
