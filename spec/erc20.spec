/***
 * This spec file adds `DISPATCHER` summaries for the methods in the ERC20
 * specification.  It is useful for writing specifications that work with
 * arbitrary ERC20 contracts; if using it, you should add a variety of ERC20
 * implementations to the scene.
 *
 * See [Using DISPATCHER for ERC20 contracts][guide] in the user guide for more
 * information.
 *
 * [guide]: https://docs.certora.com/en/latest/docs/user-guide/multicontract/index.html#using-dispatcher-for-erc20-contracts
 */

methods {
    name()                                returns (string)  => DISPATCHER(true)
    symbol()                              returns (string)  => DISPATCHER(true)
    decimals()                            returns (string)  => DISPATCHER(true)
    totalSupply()                         returns (uint256) => DISPATCHER(true)
    balanceOf(address)                    returns (uint256) => DISPATCHER(true)
    allowance(address,address)            returns (uint)    => DISPATCHER(true)
    approve(address,uint256)              returns (bool)    => DISPATCHER(true)
    transfer(address,uint256)             returns (bool)    => DISPATCHER(true)
    transferFrom(address,address,uint256) returns (bool)    => DISPATCHER(true)
}