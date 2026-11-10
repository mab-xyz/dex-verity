// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "../DexBase.sol";

/// Fuzzed properties of the compiled Pool (P2–P4, L3, L4) against the reference formulas.
contract PoolFuzzTest is DexBase {
    MockERC20 t0;
    MockERC20 t1;
    IPool pool;
    address lp = address(0x1111);
    address trader = address(0x2222);

    function setUp() public {
        (t0, t1, pool) = newPair();
    }

    function _seed(uint256 r0, uint256 r1) internal {
        t0.mint(address(pool), r0);
        t1.mint(address(pool), r1);
        pool.mint(lp);
    }

    /// P2–P4 + L3 on chain: the exact formula output is accepted, strictly below the
    /// reserve, k does not decrease, and one more wei is rejected.
    function testFuzzSwapExactFormula(uint112 r0, uint112 r1, uint112 amountIn, bool zeroForOne) public {
        vm.assume(r0 > 1e6 && r1 > 1e6 && amountIn > 0);
        vm.assume(uint256(r0) + amountIn < (uint256(1) << 112) && uint256(r1) + amountIn < (uint256(1) << 112));
        _seed(r0, r1);
        (uint256 rIn, uint256 rOut) = zeroForOne ? (uint256(r0), uint256(r1)) : (uint256(r1), uint256(r0));
        uint256 out = refAmountOut(amountIn, rIn, rOut);
        assertLt(out, rOut);
        vm.assume(out > 0);
        (zeroForOne ? t0 : t1).mint(address(pool), amountIn);
        uint256 snap = vm.snapshotState();
        // One wei more fails the k-check, or the liquidity check first when it would
        // drain the whole reserve.
        vm.expectRevert(out + 1 >= rOut ? bytes("Pool: INSUFFICIENT_LIQUIDITY") : bytes("Pool: K"));
        pool.swap(zeroForOne ? 0 : out + 1, zeroForOne ? out + 1 : 0, trader);
        vm.revertToState(snap);
        pool.swap(zeroForOne ? 0 : out, zeroForOne ? out : 0, trader);
        (uint256 n0, uint256 n1) = pool.getReserves();
        assertGe(n0 * n1, uint256(r0) * r1);
    }

    /// L4: burning `liq` shares pays liq*balance/supply of each token, never more than the balance.
    function testFuzzBurnProportional(uint112 r0, uint112 r1, uint256 frac) public {
        vm.assume(r0 > 1e6 && r1 > 1e6);
        _seed(r0, r1);
        uint256 supply = pool.lpTotalSupply();
        uint256 liq = bound(frac, 1, pool.lpBalanceOf(lp));
        uint256 e0 = liq * r0 / supply;
        uint256 e1 = liq * r1 / supply;
        vm.assume(e0 > 0 && e1 > 0);
        vm.prank(lp);
        pool.transfer(address(pool), liq);
        (uint256 a0, uint256 a1) = pool.burn(trader);
        assertEq(a0, e0);
        assertEq(a1, e1);
        assertLe(a0, r0);
        assertLe(a1, r1);
        assertEq(pool.lpTotalSupply(), supply - liq);
    }
}
