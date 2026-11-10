// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "../DexBase.sol";
import "../ref/RefPool.sol";

/// Differential: the Verity-compiled Pool and the Solidity RefPool, driven through the same
/// operations, mint the same shares, pay the same amounts, accept/reject the same swaps
/// and end with the same reserves and supply.
contract PoolDiffTest is DexBase {
    MockERC20 a0;
    MockERC20 a1;
    MockERC20 b0;
    MockERC20 b1;
    IPool vpool;
    RefPool rpool;
    address lp = address(0x1111);

    function setUp() public {
        (a0, a1, vpool) = newPair();
        b0 = new MockERC20("B0");
        b1 = new MockERC20("B1");
        rpool = new RefPool(b0, b1);
    }

    function _add(uint256 x0, uint256 x1) internal returns (bool okV, bool okR, uint256 lv, uint256 lr) {
        a0.mint(address(vpool), x0);
        a1.mint(address(vpool), x1);
        b0.mint(address(rpool), x0);
        b1.mint(address(rpool), x1);
        try vpool.mint(lp) returns (uint256 l) { okV = true; lv = l; } catch {}
        try rpool.mint(lp) returns (uint256 l) { okR = true; lr = l; } catch {}
    }

    function _swap(uint256 amountIn, uint256 out, bool zeroForOne) internal returns (bool okV, bool okR) {
        (zeroForOne ? a0 : a1).mint(address(vpool), amountIn);
        (zeroForOne ? b0 : b1).mint(address(rpool), amountIn);
        (uint256 o0, uint256 o1) = zeroForOne ? (uint256(0), out) : (out, uint256(0));
        try vpool.swap(o0, o1, address(0xBEEF)) { okV = true; } catch {}
        try rpool.swap(o0, o1, address(0xBEEF)) { okR = true; } catch {}
    }

    function _sameState() internal view {
        (uint256 v0, uint256 v1) = vpool.getReserves();
        assertEq(v0, rpool.reserve0());
        assertEq(v1, rpool.reserve1());
        assertEq(vpool.lpTotalSupply(), rpool.totalSupply());
        assertEq(vpool.lpBalanceOf(lp), rpool.balanceOf(lp));
    }

    function testFuzzSameSequence(uint96 x0, uint96 x1, uint96 y0, uint96 y1, uint96 amountIn, uint256 outSeed,
        bool zeroForOne) public {
        (bool okV, bool okR, uint256 lv, uint256 lr) = _add(x0, x1);
        assertEq(okV, okR, "first mint accepted differently");
        assertEq(lv, lr);
        _sameState();
        if (!okV) return;
        (okV, okR, lv, lr) = _add(y0, y1);
        assertEq(okV, okR, "second mint accepted differently");
        assertEq(lv, lr);
        _sameState();
        (uint256 r0, uint256 r1) = vpool.getReserves();
        uint256 rOut = zeroForOne ? r1 : r0;
        uint256 out = rOut == 0 ? 0 : bound(outSeed, 0, rOut);
        (okV, okR) = _swap(amountIn, out, zeroForOne);
        assertEq(okV, okR, "swap accepted differently");
        _sameState();
    }
}
