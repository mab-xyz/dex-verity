// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./ref/MockERC20.sol";

interface IPool {
    function initPool(address t0, address t1) external;
    function getReserves() external view returns (uint256, uint256);
    function lpBalanceOf(address owner) external view returns (uint256);
    function lpAllowance(address owner, address spender) external view returns (uint256);
    function lpTotalSupply() external view returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transfer(address dst, uint256 amount) external returns (bool);
    function transferFrom(address src, address dst, uint256 amount) external returns (bool);
    function mint(address recipient) external returns (uint256);
    function burn(address recipient) external returns (uint256, uint256);
    function swap(uint256 out0, uint256 out1, address recipient) external;
    function sync() external;
}

interface IRouter {
    function getAmountOut(uint256 amountIn, uint256 reserveIn, uint256 reserveOut) external returns (uint256);
    function quote(uint256 amountA, uint256 reserveA, uint256 reserveB) external returns (uint256);
    function swapExactIn(uint256 amountIn, uint256 amountOutMin, address tokenIn, address tokenOut,
        address recipient, uint256 deadline) external returns (uint256);
    function addLiquidity(address tokenA, address tokenB, uint256 amountADesired, uint256 amountBDesired,
        uint256 amountAMin, uint256 amountBMin, address recipient, uint256 deadline) external returns (uint256);
    function removeLiquidity(address tokenA, address tokenB, uint256 liquidity, uint256 amountAMin,
        uint256 amountBMin, address recipient, uint256 deadline) external returns (uint256, uint256);
}

/// Deploys the Verity-compiled contracts from `out/<Name>.bin` (scripts/build-evm.sh).
abstract contract DexBase is Test {
    function deployBin(string memory name, bytes memory ctorArgs) internal returns (address addr) {
        bytes memory code = bytes.concat(vm.parseBytes(string.concat("0x", vm.readFile(string.concat("out/", name, ".bin")))), ctorArgs);
        assembly {
            addr := create(0, add(code, 32), mload(code))
        }
        require(addr != address(0), string.concat("deploy failed: ", name));
    }

    /// Two mock tokens ordered by address (token0 < token1) and a pool initialised for them.
    function newPair() internal returns (MockERC20 t0, MockERC20 t1, IPool pool) {
        MockERC20 a = new MockERC20("A");
        MockERC20 b = new MockERC20("B");
        (t0, t1) = address(a) < address(b) ? (a, b) : (b, a);
        pool = IPool(deployBin("Pool", ""));
        pool.initPool(address(t0), address(t1));
    }

    /// Reference integer square root (floor).
    function isqrt(uint256 n) internal pure returns (uint256 r) {
        if (n == 0) return 0;
        r = n;
        uint256 x = n / 2 + 1;
        while (x < r) {
            r = x;
            x = (n / x + x) / 2;
        }
    }

    function refAmountOut(uint256 amountIn, uint256 rIn, uint256 rOut) internal pure returns (uint256) {
        uint256 inFee = amountIn * 997;
        return inFee * rOut / (rIn * 1000 + inFee);
    }
}

interface IFactory {
    function getPool(address a, address b) external view returns (address);
    function allPoolsLength() external view returns (uint256);
    function poolAt(uint256 i) external view returns (address);
    function createPool(address a, address b, bytes calldata initcode) external returns (address);
}
