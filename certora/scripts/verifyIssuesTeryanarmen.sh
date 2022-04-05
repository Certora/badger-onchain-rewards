certoraRun certora/harnesses/RewardsManagerHarnessTeryanarmen.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarnessTeryanarmen:certora/specs/BadgerissuesTeryanarmen.spec \
    --packages @oz=certora/openzeppelin/contracts \
    --solc solc8.10 \
    --send_only \
    --cloud \
    --optimistic_loop \
    --msg "$(basename $BASH_SOURCE)"
    
