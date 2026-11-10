// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

/// Minimal ERC-20 for tests. `hook` (if set) is called on every transfer, to test the
/// pools' reentrancy lock.
contract MockERC20 {
    string public name;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    uint256 public totalSupply;
    address public hook;
    bytes public hookData;

    constructor(string memory n) {
        name = n;
    }

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
    }

    function setHook(address h, bytes calldata data) external {
        hook = h;
        hookData = data;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        _move(msg.sender, to, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        uint256 allowed = allowance[from][msg.sender];
        require(allowed >= amount, "allowance");
        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;
        _move(from, to, amount);
        return true;
    }

    function _move(address from, address to, uint256 amount) internal {
        require(balanceOf[from] >= amount, "balance");
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        if (hook != address(0)) {
            (bool ok, bytes memory ret) = hook.call(hookData);
            if (!ok) {
                assembly {
                    revert(add(ret, 32), mload(ret))
                }
            }
        }
    }
}

/// Stand-in factory for router unit tests: a plain pair registry.
contract MockFactory {
    mapping(address => mapping(address => address)) public getPool;

    function setPool(address a, address b, address pool) external {
        getPool[a][b] = pool;
        getPool[b][a] = pool;
    }
}
