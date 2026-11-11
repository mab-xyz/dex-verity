// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "../DexBase.sol";

/// Unit tests of the Verity-compiled Router against Verity-compiled pools, with a
/// stand-in registry for the factory.
contract RouterTest is DexBase {
    MockERC20 t0;
    MockERC20 t1;
    IPool pool;
    IRouter router;
    MockFactory factory;
    address alice = address(0xA11CE);
    address bob = address(0xB0B);

    function setUp() public {
        (t0, t1, pool) = newPair();
        factory = new MockFactory();
        factory.setPool(address(t0), address(t1), address(pool));
        router = IRouter(deployBin("Router", abi.encode(address(factory))));
        t0.mint(alice, 100e18);
        t1.mint(alice, 100e18);
        vm.startPrank(alice);
        t0.approve(address(router), type(uint256).max);
        t1.approve(address(router), type(uint256).max);
        vm.stopPrank();
    }

    function _seed() internal {
        vm.prank(alice);
        router.addLiquidity(address(t0), address(t1), 10e18, 20e18, 0, 0, alice, block.timestamp);
    }

    function testGetAmountOutMatchesFormula() public {
        assertEq(router.getAmountOut(1e18, 10e18, 20e18), refAmountOut(1e18, 10e18, 20e18));
    }

    function testQuote() public {
        assertEq(router.quote(3e18, 10e18, 20e18), 6e18);
    }

    function testFirstAddLiquidityUsesDesired() public {
        vm.prank(alice);
        uint256 liq = router.addLiquidity(address(t0), address(t1), 10e18, 20e18, 0, 0, alice, block.timestamp);
        assertEq(liq, isqrt(10e18 * 20e18) - 1000);
        assertEq(t0.balanceOf(address(pool)), 10e18);
        assertEq(t1.balanceOf(address(pool)), 20e18);
    }

    // R3: never takes more than desired; the excess side is cut to the pool price.
    function testAddLiquidityTakesOptimalAmounts() public {
        _seed();
        uint256 before0 = t0.balanceOf(alice);
        uint256 before1 = t1.balanceOf(alice);
        vm.prank(alice);
        router.addLiquidity(address(t0), address(t1), 1e18, 5e18, 0, 0, alice, block.timestamp);
        assertEq(before0 - t0.balanceOf(alice), 1e18);
        assertEq(before1 - t1.balanceOf(alice), 2e18);
    }

    // R3, other branch: B is the scarce side, so A is cut to the pool price.
    function testAddLiquidityTakesOptimalA() public {
        _seed();
        uint256 before0 = t0.balanceOf(alice);
        uint256 before1 = t1.balanceOf(alice);
        vm.prank(alice);
        router.addLiquidity(address(t0), address(t1), 5e18, 2e18, 0, 0, alice, block.timestamp);
        assertEq(before0 - t0.balanceOf(alice), 1e18);
        assertEq(before1 - t1.balanceOf(alice), 2e18);
    }

    // R3 (`quoteAmounts_bounds`) on the bytecode: never more than desired, and one side is
    // the desired amount.
    function testFuzzAddLiquidityWithinDesired(uint256 aDesired, uint256 bDesired) public {
        _seed();
        aDesired = bound(aDesired, 1e9, 50e18);
        bDesired = bound(bDesired, 1e9, 50e18);
        uint256 before0 = t0.balanceOf(alice);
        uint256 before1 = t1.balanceOf(alice);
        vm.prank(alice);
        router.addLiquidity(address(t0), address(t1), aDesired, bDesired, 0, 0, alice, block.timestamp);
        uint256 taken0 = before0 - t0.balanceOf(alice);
        uint256 taken1 = before1 - t1.balanceOf(alice);
        assertLe(taken0, aDesired);
        assertLe(taken1, bDesired);
        assertTrue(taken0 == aDesired || taken1 == bDesired);
    }

    function testAddLiquidityMinimumEnforced() public {
        _seed();
        vm.prank(alice);
        vm.expectRevert(bytes("Router: INSUFFICIENT_B_AMOUNT"));
        router.addLiquidity(address(t0), address(t1), 1e18, 5e18, 0, 3e18, alice, block.timestamp);
    }

    // R2: the output is the formula's, and the minimum is enforced.
    function testSwapExactInBothDirections() public {
        _seed();
        uint256 expected = refAmountOut(1e18, 10e18, 20e18);
        vm.prank(alice);
        uint256 out = router.swapExactIn(1e18, expected, address(t0), address(t1), bob, block.timestamp);
        assertEq(out, expected);
        assertEq(t1.balanceOf(bob), expected);
        (uint256 r0, uint256 r1) = pool.getReserves();
        uint256 back = refAmountOut(1e18, r1, r0);
        vm.prank(alice);
        assertEq(router.swapExactIn(1e18, 0, address(t1), address(t0), bob, block.timestamp), back);
        assertEq(t0.balanceOf(bob), back);
    }

    function testSwapSlippageReverts() public {
        _seed();
        uint256 expected = refAmountOut(1e18, 10e18, 20e18);
        vm.prank(alice);
        vm.expectRevert(bytes("Router: INSUFFICIENT_OUTPUT_AMOUNT"));
        router.swapExactIn(1e18, expected + 1, address(t0), address(t1), bob, block.timestamp);
    }

    // R1: deadline.
    function testExpiredDeadlineReverts() public {
        _seed();
        vm.warp(1000);
        vm.prank(alice);
        vm.expectRevert(bytes("Router: EXPIRED"));
        router.swapExactIn(1e18, 0, address(t0), address(t1), bob, 999);
    }

    function testUnknownPairReverts() public {
        MockERC20 c = new MockERC20("C");
        vm.prank(alice);
        vm.expectRevert(bytes("Router: POOL_NOT_FOUND"));
        router.swapExactIn(1e18, 0, address(t0), address(c), bob, block.timestamp);
    }

    // R4: remove liquidity respects minimums and returns proportional amounts.
    function testRemoveLiquidity() public {
        _seed();
        uint256 liq = pool.lpBalanceOf(alice);
        uint256 supply = pool.lpTotalSupply();
        vm.prank(alice);
        pool.approve(address(router), liq);
        vm.prank(alice);
        (uint256 a, uint256 b) = router.removeLiquidity(address(t0), address(t1), liq, 0, 0, bob, block.timestamp);
        assertEq(a, liq * 10e18 / supply);
        assertEq(b, liq * 20e18 / supply);
        assertEq(t0.balanceOf(bob), a);
        assertEq(t1.balanceOf(bob), b);
    }

    function testRemoveLiquidityMinimumEnforced() public {
        _seed();
        uint256 liq = pool.lpBalanceOf(alice);
        vm.prank(alice);
        pool.approve(address(router), liq);
        vm.prank(alice);
        vm.expectRevert(bytes("Router: INSUFFICIENT_A_AMOUNT"));
        router.removeLiquidity(address(t0), address(t1), liq, 10e18, 0, bob, block.timestamp);
    }
}
