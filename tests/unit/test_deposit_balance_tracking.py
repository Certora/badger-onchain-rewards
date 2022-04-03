import brownie
from brownie import *

AddressZero = "0x0000000000000000000000000000000000000000"
MaxUint256 = str(int(2 ** 256 - 1))

"""
  Changing epoch allows to retrieve previous balances 
"""

def test_epoch_zero_to_one_weirdness(rewards_contract, user, fake_vault):
  """
    Epoch 0 is meant to represent undefined
    In this test we prove the odd behaviour that epoch zero causes
    The second you deploy, please make sure to go to epoch 1 as fast as possible
  """
  epoch = 0
  ## We start in epoch 0
  assert rewards_contract.currentEpoch() == epoch

  INITIAL_DEPOSIT = 1e18

  rewards_contract.notifyTransfer(AddressZero, user, INITIAL_DEPOSIT, {"from": fake_vault})
  assert rewards_contract.shares(epoch, fake_vault, user) == INITIAL_DEPOSIT

  ## Here come's the weird part
  ## Because prev epoch was zero, we can't get the prev balance
  tx = rewards_contract.startNextEpoch({"from": user})
  new_epoch = 1

  assert rewards_contract.currentEpoch() == new_epoch
  
  assert rewards_contract.shares(new_epoch, fake_vault, user) == 0 ## Need to port them over via getBalanceAtEpoch

  ## Update the balance
  assert rewards_contract.getBalanceAtEpoch(new_epoch, fake_vault, user)[0] == 0



def test_epoch_changes_balances_are_preserved(initialized_contract, user, fake_vault):
    """
      This test proves that balances are preserved across epochs
    """
    epoch = 1
    ## We start in epoch 0
    assert initialized_contract.currentEpoch() == epoch

    INITIAL_DEPOSIT = 1e18

    initialized_contract.notifyTransfer(AddressZero, user, INITIAL_DEPOSIT, {"from": fake_vault})
    
    assert initialized_contract.shares(epoch, fake_vault, user) == INITIAL_DEPOSIT
    assert initialized_contract.getBalanceAtEpoch(epoch, fake_vault, user)[0] == INITIAL_DEPOSIT


    chain.sleep(initialized_contract.SECONDS_PER_EPOCH() + 1)
    chain.mine()

    ## Because prev epoch was zero, we can't get the prev balance
    tx = initialized_contract.startNextEpoch({"from": user})
    new_epoch = 2

    assert initialized_contract.currentEpoch() == new_epoch
  

    ## For this epoch it won't be there (as we don't look back to epoch 0)
    assert initialized_contract.getBalanceAtEpoch(new_epoch, fake_vault, user)[0] == INITIAL_DEPOSIT ## Invariant is maintained

    ## Do it again to proove it's not a fluke
    chain.sleep(initialized_contract.SECONDS_PER_EPOCH() + 1)
    chain.mine()

    initialized_contract.startNextEpoch({"from": user})
    new_epoch = 3

    assert initialized_contract.currentEpoch() == new_epoch

    ## For this epoch it won't be there (as we don't look back to epoch 0)
    assert initialized_contract.getBalanceAtEpoch(new_epoch, fake_vault, user)[0] == INITIAL_DEPOSIT ## Invariant is maintained

  
def test_epoch_changes_balances_are_preserved_after_tons_of_epochs(initialized_contract, user, fake_vault):
    epoch = 1
    ## We start in epoch 0
    assert initialized_contract.currentEpoch() == epoch

    INITIAL_DEPOSIT = 1e18

    initialized_contract.notifyTransfer(AddressZero, user, INITIAL_DEPOSIT, {"from": fake_vault})
    
    assert initialized_contract.shares(epoch, fake_vault, user) == INITIAL_DEPOSIT

    ## Wait 6 epochs
    for x in range(1, 6):
      chain.sleep(initialized_contract.SECONDS_PER_EPOCH() + 1)
      chain.mine()
      initialized_contract.startNextEpoch({"from": user})

    ## See if we get the balance
    ## Old Epoch Balance is still there (no storage changes)
    assert initialized_contract.shares(epoch, fake_vault, user) == INITIAL_DEPOSIT

    current_epoch = initialized_contract.currentEpoch()
    ## New Current Epoch Balance is not there
    assert initialized_contract.shares(current_epoch, fake_vault, user) == 0

    ## Balance was correctly ported over
    assert initialized_contract.getBalanceAtEpoch(current_epoch, fake_vault, user)[0] == INITIAL_DEPOSIT

def test_epoch_changes_balances_are_preserved_and_change_properly_after_tons_of_epochs(initialized_contract, user, fake_vault):
    epoch = 1
    ## We start in epoch 0
    assert initialized_contract.currentEpoch() == epoch

    INITIAL_DEPOSIT = 1e18

    initialized_contract.notifyTransfer(AddressZero, user, INITIAL_DEPOSIT, {"from": fake_vault})
    
    assert initialized_contract.shares(epoch, fake_vault, user) == INITIAL_DEPOSIT

    ## Wait 6 epochs
    for x in range(1, 6):
      chain.sleep(initialized_contract.SECONDS_PER_EPOCH() + 1)
      chain.mine()
      initialized_contract.startNextEpoch({"from": user})


    SECOND_DEPOSIT = 3e18
    
    initialized_contract.notifyTransfer(AddressZero, user, SECOND_DEPOSIT, {"from": fake_vault})


    ## See if we get the balance
    ## Old Epoch Balance is still there (no storage changes)
    assert initialized_contract.shares(epoch, fake_vault, user) == INITIAL_DEPOSIT

    current_epoch = initialized_contract.currentEpoch()
    ## New Current Epoch Balance is already there, as `notifyTransfer` accrues and sets up shares automatically
    assert initialized_contract.shares(current_epoch, fake_vault, user) == INITIAL_DEPOSIT + SECOND_DEPOSIT


    ## Wait until end of epoch and do another transfer to check if time can break this property
    chain.sleep(initialized_contract.SECONDS_PER_EPOCH() + 1)
    chain.mine()

    THIRD_DEPOSIT = 6e18
    initialized_contract.notifyTransfer(AddressZero, user, THIRD_DEPOSIT, {"from": fake_vault})

    assert initialized_contract.shares(current_epoch, fake_vault, user) == INITIAL_DEPOSIT + SECOND_DEPOSIT + THIRD_DEPOSIT

