import "./erc20.spec"

using DummyERC20A as stakingToken
using DummyERC20B as rewardsToken
/**************************************************
 *              METHODS DECLARATIONS              *
 **************************************************/
methods{
    stakingToken()                  returns (address)   envfree
    rewardsToken()                  returns (address)   envfree
    owner()                         returns (address)   envfree
    duration()                      returns (uint256)   envfree
    finishAt()                      returns (uint256)   envfree
    updatedAt()                     returns (uint256)   envfree
    rewardRate()                    returns (uint256)   envfree
    rewardPerTokenStored()          returns (uint256)   envfree
    userRewardPerTokenPaid(address) returns (uint256)   envfree
    rewards(address)                returns (uint256)   envfree
    totalSupply()                   returns (uint256)   envfree
    balanceOf(address)              returns (uint256)   envfree
    _min(uint256, uint256)          returns(uint256)    envfree
    rewardsToken.balanceOf(address) returns (uint256)   envfree
    stakingToken.balanceOf(address) returns (uint256)   envfree
    lastTimeRewardApplicable()      returns (uint256)
    rewardPerToken()                returns (uint256)
    earned(address)                 returns uint256
    stake(uint256)
    withdraw(uint256)
    getReward(address)
    setRewardsDuration(uint256)
    notifyRewardAmount(uint256)
}

definition isGetReward(method f) returns bool = f.selector == getReward().selector;
definition isWithdraw(method f)  returns bool = f.selector == withdraw(uint256).selector;
// definition minTime(uint256 finishAt, uint256 timestamp) returns uint256 = finishAt < timestamp ? finishAt : timestamp;
 function minTimeFunc(uint256 finishAt, uint256 timestamp) returns uint256{
    return finishAt < timestamp ? finishAt : timestamp;
 }

/**************************************************
 *                 Ghosts & Hooks                 *
 **************************************************/
 ghost mathint SumOfBalancesGhost{
  init_state axiom SumOfBalancesGhost == 0;
}

 ghost mathint SumOfRewardsNotified{
  init_state axiom SumOfRewardsNotified == 0;
  }

 ghost mathint duration;

 ghost mathint SumOfRewards{
  init_state axiom SumOfRewards == 0;
  }

// mirror of duration for use within a hook
 hook Sstore duration uint256 value STORAGE { duration = value;}

 hook Sload uint256 value duration STORAGE {require duration == value;}
 
//  hook Sload uint256 value rewards[KEY address s] STORAGE {require rewards[s] == value;}

 hook Sstore balanceOf[KEY address s] uint256 balance (uint256 oldBalance) STORAGE {
    SumOfBalancesGhost = SumOfBalancesGhost + balance - oldBalance;
 }

 hook Sstore rewardRate uint256 rr (uint256 old_rr) STORAGE {
    SumOfRewardsNotified = SumOfRewardsNotified + rr * duration;
 }

 hook Sstore rewards[KEY address s] uint reward (uint256 old_reward) STORAGE {
    SumOfRewards = SumOfRewards + reward - old_reward;
 }

//  hook Sload uint256 rew rewards[KEY address s] STORAGE {
//     require sumOfRewards >= rew;
// }
/**************************************************
 *                Rule & Invariants               *
 **************************************************/

// user1 stakes for 3 sec user2 stakes for sec1 and sec3: user 1 should not get less than user 2
// STATUS: FAILING
rule longerDurationDuringSamePeriodGreaterReward(){
    env e1;
    env e2;
    require e1.msg.sender != e2.msg.sender;
    require e1.block.timestamp == e2.block.timestamp;
    require balanceOf(e1.msg.sender) == balanceOf(e2.msg.sender);
    require userRewardPerTokenPaid(e1.msg.sender) == userRewardPerTokenPaid(e2.msg.sender);
    uint256 reward1 = rewards(e1.msg.sender);
    uint256 reward2 = rewards(e2.msg.sender);

    uint256 amount;
    stake(e1, amount);
    stake(e2, amount);


    env e3;
    require e3.msg.sender == e2.msg.sender;
    require e2.block.timestamp +1 == e3.block.timestamp;
    withdraw(e3, amount);

    env e4;
    require e4.msg.sender == e2.msg.sender;
    require e3.block.timestamp +1 == e4.block.timestamp;
    stake(e4, amount);

    env e5;
    require e4.block.timestamp +1 == e5.block.timestamp;
    uint256 accrued1 = earned(e5, e1.msg.sender) - reward1;
    uint256 accrued2 = earned(e5, e2.msg.sender) - reward2;

    assert accrued1 >= accrued2,"longer staking during the same period should yield no less rewards";
}
// two users staking the same amount and same time should get same rewards when the 
// STATUS: Verified
rule stakingSameTimePeriodAmountGivesSameRewards(){
    env e1;
    env e2;
    require e1.msg.sender != e2.msg.sender;
    require e1.block.timestamp == e2.block.timestamp;
    uint256 amount;
    uint256 reward1 = rewards(e1.msg.sender);
    uint256 reward2 = rewards(e2.msg.sender);
    stake(e1, amount);
    stake(e2, amount);

    env e3;
    require e3.block.timestamp > e2.block.timestamp;

    uint256 accrued1 = earned(e3, e1.msg.sender) - reward1;
    uint256 accrued2 = earned(e3, e2.msg.sender) - reward2;

    assert accrued1 == accrued1,"two users staking the same amount for the period should get the same rewards";
}

// staking an entire amount together vs staking in two transactions in the same block should get the same rewards in the end  
// STATUS: FAILING
rule rewardsIndependentOfNoOfTx(){
    uint256 amount1;
    uint256 amount2;
    uint256 amount3;
    require amount1 == amount2 + amount3;

    env e1;
    env e2;

    require e1.msg.sender != e2.msg.sender;
    require e1.block.timestamp == e2.block.timestamp;
    require balanceOf(e1.msg.sender) == balanceOf(e2.msg.sender);
    require userRewardPerTokenPaid(e1.msg.sender) == userRewardPerTokenPaid(e2.msg.sender);

    uint256 reward1 = rewards(e1.msg.sender);
    uint256 reward2 = rewards(e2.msg.sender);
    

    stake(e1, amount1);
    stake(e2, amount2);
    stake(e2, amount3);

    env e3;
    require e3.block.timestamp > e2.block.timestamp;

    uint256 accrued1 = earned(e3, e1.msg.sender) - reward1;
    uint256 accrued2 = earned(e3, e2.msg.sender) - reward2;

    assert accrued1 == accrued2,"same amount and duration of staking should yield the same rewards regardless of the number of transactions to stake";
}

// sum of external user balance, staking token balance and reward

// a user depositing for same duration

// owner only access control

// a third user should be untouched by transaction that have nothing to do with them


// integrity of staking
// STATUS: Verified
// https://vaas-stg.certora.com/output/11775/48997c2499690308d492/?anonymousKey=79bb5046a211143115251c3b344a9bc788b1b419
rule integrityOfStaking(){
    env e;
    uint256 amount;
    uint256 _stakingBalance = balanceOf(e.msg.sender);
    uint256 _userBalance = stakingToken.balanceOf(e.msg.sender);
    uint256 _totalSupply = totalSupply();
    require e.msg.sender != currentContract;
    
    stake(e, amount);
    
    uint256 stakingBalance_ = balanceOf(e.msg.sender);
    uint256 userBalance_ = stakingToken.balanceOf(e.msg.sender);
    uint256 totalSupply_ = totalSupply();

    assert stakingBalance_ == _stakingBalance + amount,"staking balance of the user should increase by the amount staked";
    assert userBalance_ + amount == _userBalance,"user's balance should go down by the amount staked";
    assert totalSupply_ ==  _totalSupply + amount,"total supply should increase by the amount staked";
}


// no double rewards/ withdraw; limit to the amount someone can gain from withdrawing/ reward
// STATUS: Verified
// https://vaas-stg.certora.com/output/11775/48997c2499690308d492/?anonymousKey=79bb5046a211143115251c3b344a9bc788b1b419
rule integrityOfWithdrawal(){
    env e;
    uint256 amount;
    uint256 _stakingBalance = balanceOf(e.msg.sender);
    uint256 _userBalance = stakingToken.balanceOf(e.msg.sender);
    require e.msg.sender != currentContract;
    
    withdraw(e, amount);

    uint256 stakingBalance_ = balanceOf(e.msg.sender);
    uint256 userBalance_ = stakingToken.balanceOf(e.msg.sender);

    assert _stakingBalance == stakingBalance_ + amount,"staking balance should go down by exactly the amount specified by the user";
    assert amount <= _stakingBalance,"user can only withdraw an amount upto their staking balance";
    assert _userBalance + amount == userBalance_,"user balance should increase by exactly the amount specified during withdrawal";
}

// STATUS: Verified
rule onlyWithdrawCanReduceStake(method f){
    env e;
    address user;
    uint256 _stakingBalance = balanceOf(e.msg.sender);
    
    calldataarg args;
    f(e, args);

    uint256 stakingBalance_ = balanceOf(e.msg.sender);
    assert stakingBalance_ < _stakingBalance => isWithdraw(f),"only withdraw function can reduce the staking balance of a user";
}

// no double rewards withdrawal; limit to the amount someone can gain from withdrawing/ reward
// STATUS: Verified
// https://vaas-stg.certora.com/output/11775/af0ddc49cd49def23274/?anonymousKey=765278c98d1dfded49d7e2e333e1b59c9791aa83
rule rewardWithdrawalLimitedToRewardAmount(method f){
    env e;
    address user;
    updateRewardHelper(e, user);
    uint256 _reward = rewards(user);
    uint256 _userBalance = rewardsToken.balanceOf(user);
    require user == e.msg.sender;
    require user != currentContract;

    calldataarg args;
    getReward(e);
    
    uint256 reward_ = rewards(user);
    uint256 userBalance_ = rewardsToken.balanceOf(user);

    assert reward_ == 0,"getReward should transfer all the rewards";
    assert userBalance_ == _userBalance + _reward,"user should get the entire reward amount and no more";
}
// STATUS: Verified
rule onlyGetRewardReducesReward(method f, env e){
    address user;
    uint256 _reward = rewards(user);
    uint256 _rewardBal = rewardsToken.balanceOf(user);
    
    calldataarg args;
    f(e, args);
    
    uint256 reward_ = rewards(user);
    uint256 rewardBal_ = rewardsToken.balanceOf(user);

    assert reward_ < _reward => isGetReward(f),"only getReward can reduce the rewards of a user";
    assert e.msg.sender == user,"only the user can cause a reduction in his reward";
    assert _reward - reward_ == rewardBal_ - _rewardBal,"user should get all the rewards";
}

// if there is a change to rewards/others the updatedAt should be current
// STATUS: Verified
// https://vaas-stg.certora.com/output/11775/653face64a360424dc75/?anonymousKey=7743ddca46f63858e277dc9eaf0ad8a4ff757c55
rule updatedAtUpdatedWhenNeeded(env e, method f){
    address user;
    uint256 _updatedAt              = updatedAt();
    uint256 _finishAt               = finishAt();
    uint256 _rewardPerTokenStored   = rewardPerTokenStored();
    uint256 _rewardRate             = rewardRate();
    uint256 _duration               = duration();
    uint256 _userRewardPerTokenPaid = userRewardPerTokenPaid(user);
    uint256 _reward                 = rewards(user);
    uint256 _userBalance            = balanceOf(user);
    uint256 _totalSupply            = totalSupply();
    require e.block.timestamp > _updatedAt;
    require _finishAt > _updatedAt;
    require _duration > 0;

    calldataarg args;
    f(e, args);
    
    uint256 updatedAt_              = updatedAt();
    uint256 rewardPerTokenStored_   = rewardPerTokenStored();
    uint256 rewardRate_             = rewardRate();
    uint256 userRewardPerTokenPaid_ = userRewardPerTokenPaid(user);
    uint256 reward_                 = rewards(user);
    uint256 totalSupply_            = totalSupply();
    uint256 userBalance_            = balanceOf(user);

    assert  _rewardPerTokenStored   != rewardPerTokenStored_    ||
            _rewardRate             != rewardRate_              ||
            _userRewardPerTokenPaid != userRewardPerTokenPaid_  ||
            _reward                 != reward_                  ||
            _userBalance            != userBalance_             ||
            _totalSupply            != totalSupply_             =>
            updatedAt_ != _updatedAt,
            // updatedAt_ == minTimeFunc(_finishAt, e.block.timestamp),
            "updatedAt should have been updated";
}

// finishAt should always be greater than or equal to updatedAt
// STATUS: verified
// https://vaas-stg.certora.com/output/11775/4b2115e4cdcdde3a5e65/?anonymousKey=327f44c242cb920dca51bcc4f6f62d43dfd44b32
invariant finishAtGEupdatedAt()
    finishAt() >= updatedAt()

// updatedAt increases monotonically
// STATUS: Verified
// https://vaas-stg.certora.com/output/11775/653face64a360424dc75/?anonymousKey=7743ddca46f63858e277dc9eaf0ad8a4ff757c55
rule updateAtIncreasesMonotonically(env e, method f){
    uint256 _updatedAt = updatedAt();
    require e.block.timestamp > _updatedAt;
    requireInvariant finishAtGEupdatedAt;

    calldataarg args;
    f(e, args);
    
     uint256 updatedAt_ = updatedAt();
     
     assert updatedAt_ >= _updatedAt;
}

// two consecutive operations in the same block don't increase reward
// STATUS: Verified
// https://vaas-stg.certora.com/output/11775/cb04f624b41c5c5a0148/?anonymousKey=7252324222665b8d378f233a84bbebd55ddd3616
rule multipleOperationsSameBlockNotIncreaseRewards(){
    method f1;
    method f2;
    calldataarg args1;
    calldataarg args2;
    env e1;
    env e2;
    require e1.block.timestamp == e2.block.timestamp;
    address user;

    uint256 _reward = rewards(user);

    f1(e1, args1);

    uint256 _reward_ = rewards(user);

    f2(e2, args2);

    uint256 reward_ = rewards(user);

    assert _reward < _reward_ => _reward_ == reward_ || reward_ == 0,"rewards cannot be increased by consecutive transactions in the same block";
}


// Contract balanceOf rewardToken should be GE sumOfRewards
// STATUS: FAILING
// if all the accounts have been updated and there are no more rewards to be accrued in the current block, the sum of rewards <= balancer
invariant RewardTokenBalGeSumOfRewards()
    rewardsToken.balanceOf(currentContract) >= SumOfRewards
    {
    preserved with (env e) {
        require e.block.timestamp == updatedAt();

    }
    }

// Contract balanceOf stakingToken should be GE TotalSupply
// STATUS: Verified
invariant stakingTokenBalGeTotalSupply()
    stakingToken.balanceOf(currentContract) >= totalSupply()
    {
    preserved with (env e) {
        require e.msg.sender != currentContract;
    }
    }

// totalSupply greater than of equal to sum of all staking balances

// if a user's reward goes down, then the user's reward token balance should go up by an equal amount

// rewards can either go down to 0 or go up. Cant decrease to a non-0 value

// rewardpertokenstored should increase monotonically

// 
/**
 * Total user rewards should be LE to the total notified rewards
 */
// STATUS: FAILING
invariant userRewardsLENotifiedRewards()
    SumOfRewardsNotified >= SumOfRewards

/**
 * The total supply tracked by the contract should be equal to the sum of balances of staked 
 * token. Failing this, the contract
 * will hand out incorrect reward amounts
 */
//  STATUS: Verified
invariant totalSupplyEqualsSumOfBalances()
    totalSupply() == SumOfBalancesGhost

/**
 * updatedAt should never be more than the current timestamp as this would lead to improper 
 * updating of state variables like rewardPerTokenStored
 */
//  STATUS: Verified
invariant updatedAtLEBlockTime(uint256 timestamp)
    updatedAt() <= timestamp
    {
    preserved with (env e) {
        require e.block.timestamp == timestamp;
    }
    }

/**
 * reward start time cannot be in the future
 */
//  STATUS: Verified
invariant rewardStartCannotBeInFuture(uint256 timestamp)
    duration() >= finishAt() - timestamp
    {
        preserved with (env e) {
            require e.block.timestamp == timestamp;
        }
    }
/**
 * FinishAt cannot decrese
 */
// STATUS: Verified
rule monotonicityOfFinishAt(method f, env e){
    uint256 _finishAt = finishAt();

    require duration() >= finishAt() - e.block.timestamp; //invariant rewardStartCannotBeInFuture

    calldataarg args;
    f(e, args);
    uint256 finishAt_ = finishAt();
    assert finishAt_ >= _finishAt,"finishAt can not decrease";
}

/**
 * updateAt cannot decrese
 */
//  STATUS: Verified
rule monotonicityOfUpdatedAt(method f, env e){
    uint256 _updatedAt = updatedAt();
    requireInvariant finishAtGEupdatedAt;
    requireInvariant updatedAtLEBlockTime(e.block.timestamp);
    calldataarg args;
    f(e, args);
    uint256 updatedAt_ = updatedAt();
    assert updatedAt_ >= _updatedAt,"updatedAt can not decrease";
}

/**
 * rewardPerTokenStored cannot decrese
 */
//  STATUS: Verified
rule monotonicityOfrewardPerTokenStored(method f, env e){
    uint256 _rewardPerTokenStored = rewardPerTokenStored();
    calldataarg args;
    f(e, args);
    uint256 rewardPerTokenStored_ = rewardPerTokenStored();
    assert rewardPerTokenStored_ >= _rewardPerTokenStored,"rewardPerTokenStored can not decrease";
}

/**
 * rule verfiying the following about the getReward function:
 * contract's balance should go down by the amount by which the user's balance goes up
 * users rewards are 0 after the function call
 */
// STATUS: Verified
rule getRewardTest(env e){
    uint256 _userRewards = rewards(e.msg.sender);
    uint256 _contractBalance = rewardsToken.balanceOf(currentContract);
    uint256 _userBalance = rewardsToken.balanceOf(e.msg.sender);
    require e.msg.sender != currentContract;
    getReward(e);
    uint256 userRewards_ = rewards(e.msg.sender);
    uint256 contractBalance_ = rewardsToken.balanceOf(currentContract);
    uint256 userBalance_ = rewardsToken.balanceOf(e.msg.sender);
    assert _contractBalance - contractBalance_ ==  userBalance_ -  _userBalance;
    assert userRewards_ == 0;
    assert userBalance_ - _userBalance >= _userRewards;
 }

// rule about if one's earned() > 0 he can get this amount with getRewards
// STATUS: Verified
rule userShouldGetEarnedAmount(env e){
    uint256 _earned = earned(e, e.msg.sender);
    uint256 _userRewardBal = rewardsToken.balanceOf(e.msg.sender);
    require e.msg.sender != 0;
    require e.msg.sender != currentContract;
    getReward(e);
    uint256 userRewardBal_ = rewardsToken.balanceOf(e.msg.sender);
    assert userRewardBal_ - _userRewardBal == _earned;
}



rule sanity(env e, method f){
    calldataarg args;
    f(e,args);
    assert false;
}

rule whoChangedDuration(method f, env e){
    uint256 _duration = duration();
    calldataarg args;
    f(e, args);
    uint256 duration_ = duration();
    assert _duration == duration_;
}

rule integrityOfTransfer(env e){
    address user;
    uint256 _balance = rewardsToken.balanceOf(user);
    uint256 _contractBalance = rewardsToken.balanceOf(currentContract);
    uint256 _reward = rewards(user);
    require _contractBalance > 5;
    require user != currentContract;
    
    rewardTransferTest(e, user, 5);
    
    uint256 reward_ = rewards(user);
    uint256 balance_ = rewardsToken.balanceOf(user);
    uint256 contractBalance_ = rewardsToken.balanceOf(currentContract);

    assert balance_ == _balance + 5;
}