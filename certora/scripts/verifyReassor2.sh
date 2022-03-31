#!/bin/sh

solc-select use 0.8.10

certoraRun certora/harnesses/RewardsManagerHarness.sol certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify RewardsManagerHarness:certora/specs/Badger_Reassor2.spec \
    --optimistic_loop \
    --packages @oz=certora/openzeppelin/contracts \
    --msg "$1"
