// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./MockERC20.sol";

/// Hand-written Solidity reference for Dex.Pool's arithmetic (mint/burn/swap), used by the
/// differential suite. Same formulas: isqrt first mint minus 1000 locked, proportional
/// later mints/burns (floor), 0.3% fee k-check, 2^112 balance cap.
contract RefPool {
    MockERC20 public token0;
    MockERC20 public token1;
    uint256 public reserve0;
    uint256 public reserve1;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;

    constructor(MockERC20 t0, MockERC20 t1) {
        token0 = t0;
        token1 = t1;
    }

    function _sqrt(uint256 n) internal pure returns (uint256 z) {
        if (n > 3) {
            z = n;
            uint256 x = n / 2 + 1;
            while (x < z) {
                z = x;
                x = (n / x + x) / 2;
            }
        } else if (n != 0) {
            z = 1;
        }
    }

    function mint(address to) external returns (uint256 liquidity) {
        uint256 b0 = token0.balanceOf(address(this));
        uint256 b1 = token1.balanceOf(address(this));
        require(b0 < 1 << 112 && b1 < 1 << 112, "OVERFLOW");
        uint256 a0 = b0 - reserve0;
        uint256 a1 = b1 - reserve1;
        if (totalSupply == 0) {
            uint256 root = _sqrt(a0 * a1);
            require(root > 1000, "INITIAL");
            liquidity = root - 1000;
            balanceOf[address(0)] += 1000;
            totalSupply = 1000;
        } else {
            uint256 l0 = a0 * totalSupply / reserve0;
            uint256 l1 = a1 * totalSupply / reserve1;
            liquidity = l0 < l1 ? l0 : l1;
        }
        require(liquidity > 0, "MINTED");
        totalSupply += liquidity;
        balanceOf[to] += liquidity;
        reserve0 = b0;
        reserve1 = b1;
    }

    function burn(address to, uint256 liquidity) external returns (uint256 amount0, uint256 amount1) {
        uint256 b0 = token0.balanceOf(address(this));
        uint256 b1 = token1.balanceOf(address(this));
        amount0 = liquidity * b0 / totalSupply;
        amount1 = liquidity * b1 / totalSupply;
        require(amount0 > 0 && amount1 > 0, "BURNED");
        balanceOf[msg.sender] -= liquidity;
        totalSupply -= liquidity;
        token0.transfer(to, amount0);
        token1.transfer(to, amount1);
        reserve0 = token0.balanceOf(address(this));
        reserve1 = token1.balanceOf(address(this));
    }

    function swap(uint256 out0, uint256 out1, address to) external {
        require(out0 > 0 || out1 > 0, "OUTPUT");
        require(out0 < reserve0 && out1 < reserve1, "LIQUIDITY");
        uint256 r0 = reserve0;
        uint256 r1 = reserve1;
        if (out0 > 0) token0.transfer(to, out0);
        if (out1 > 0) token1.transfer(to, out1);
        uint256 b0 = token0.balanceOf(address(this));
        uint256 b1 = token1.balanceOf(address(this));
        require(b0 < 1 << 112 && b1 < 1 << 112, "OVERFLOW");
        uint256 in0 = b0 > r0 - out0 ? b0 - (r0 - out0) : 0;
        uint256 in1 = b1 > r1 - out1 ? b1 - (r1 - out1) : 0;
        require(in0 > 0 || in1 > 0, "INPUT");
        require((b0 * 1000 - in0 * 3) * (b1 * 1000 - in1 * 3) >= r0 * r1 * 1000000, "K");
        reserve0 = b0;
        reserve1 = b1;
    }
}
