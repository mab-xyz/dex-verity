// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "../DexBase.sol";

/// Unit tests of the Verity-compiled Pool (deployed by this test, which is its factory).
contract PoolTest is DexBase {
    MockERC20 t0;
    MockERC20 t1;
    IPool pool;
    address alice = address(0xA11CE);
    address bob = address(0xB0B);

    function setUp() public {
        (t0, t1, pool) = newPair();
    }

    function _deposit(uint256 a0, uint256 a1, address to) internal returns (uint256) {
        t0.mint(address(pool), a0);
        t1.mint(address(pool), a1);
        return pool.mint(to);
    }

    // L1: initPool only from the factory, only once.
    function testInitPoolOnlyOnce() public {
        vm.expectRevert(bytes("Pool: ALREADY_INITIALIZED"));
        pool.initPool(address(t0), address(t1));
    }

    function testInitPoolOnlyFactory() public {
        IPool other = IPool(deployBin("Pool", ""));
        vm.prank(alice);
        vm.expectRevert(bytes("Pool: FORBIDDEN"));
        other.initPool(address(t0), address(t1));
    }

    // L5: the first mint gives isqrt(a0*a1) - 1000 and locks 1000 at address 0.
    function testFirstMintLocksMinimumLiquidity() public {
        uint256 liq = _deposit(4e18, 1e18, alice);
        assertEq(liq, isqrt(4e18 * 1e18) - 1000);
        assertEq(pool.lpBalanceOf(alice), liq);
        assertEq(pool.lpBalanceOf(address(0)), 1000);
        assertEq(pool.lpTotalSupply(), liq + 1000);
        (uint256 r0, uint256 r1) = pool.getReserves();
        assertEq(r0, 4e18);
        assertEq(r1, 1e18);
    }

    function testFirstMintTooSmallReverts() public {
        t0.mint(address(pool), 1000);
        t1.mint(address(pool), 1000);
        vm.expectRevert(bytes("Pool: INSUFFICIENT_INITIAL_LIQUIDITY"));
        pool.mint(alice);
    }

    function testSecondMintIsProportional() public {
        _deposit(4e18, 1e18, alice);
        uint256 supply = pool.lpTotalSupply();
        uint256 liq = _deposit(2e18, 1e18, bob); // token1 is the binding side
        assertEq(liq, (uint256(1e18) * supply) / 1e18 < (uint256(2e18) * supply) / 4e18
            ? (uint256(1e18) * supply) / 1e18 : (uint256(2e18) * supply) / 4e18);
        assertEq(pool.lpTotalSupply(), supply + liq);
    }

    // L3/L8: swap with the exact getAmountOut passes the k-check; one more wei fails.
    function testSwapExactOutputPassesK() public {
        _deposit(10e18, 10e18, alice);
        uint256 amountIn = 1e18;
        uint256 out = refAmountOut(amountIn, 10e18, 10e18);
        t0.mint(address(pool), amountIn);
        pool.swap(0, out, bob);
        assertEq(t1.balanceOf(bob), out);
        (uint256 r0, uint256 r1) = pool.getReserves();
        assertEq(r0, 11e18);
        assertEq(r1, 10e18 - out);
        assertGe(r0 * r1, uint256(10e18) * 10e18);
    }

    function testSwapOneWeiTooMuchFailsK() public {
        _deposit(10e18, 10e18, alice);
        uint256 amountIn = 1e18;
        uint256 out = refAmountOut(amountIn, 10e18, 10e18) + 1;
        t0.mint(address(pool), amountIn);
        vm.expectRevert(bytes("Pool: K"));
        pool.swap(0, out, bob);
    }

    function testSwapRejectsZeroOutputAndDrain() public {
        _deposit(10e18, 10e18, alice);
        vm.expectRevert(bytes("Pool: INSUFFICIENT_OUTPUT_AMOUNT"));
        pool.swap(0, 0, bob);
        vm.expectRevert(bytes("Pool: INSUFFICIENT_LIQUIDITY"));
        pool.swap(10e18, 0, bob);
    }

    function testSwapWithoutInputReverts() public {
        _deposit(10e18, 10e18, alice);
        vm.expectRevert(bytes("Pool: INSUFFICIENT_INPUT_AMOUNT"));
        pool.swap(0, 1e18, bob);
    }

    function testSwapToTokenReverts() public {
        _deposit(10e18, 10e18, alice);
        t0.mint(address(pool), 1e18);
        vm.expectRevert(bytes("Pool: INVALID_TO"));
        pool.swap(0, 1, address(t1));
    }

    // L4: burn returns shares proportional to the balances.
    function testBurnIsProportional() public {
        uint256 liq = _deposit(4e18, 1e18, alice);
        uint256 supply = pool.lpTotalSupply();
        vm.prank(alice);
        pool.transfer(address(pool), liq);
        (uint256 a0, uint256 a1) = pool.burn(bob);
        assertEq(a0, liq * 4e18 / supply);
        assertEq(a1, liq * 1e18 / supply);
        assertEq(t0.balanceOf(bob), a0);
        assertEq(t1.balanceOf(bob), a1);
        assertEq(pool.lpTotalSupply(), 1000);
        (uint256 r0, uint256 r1) = pool.getReserves();
        assertEq(r0, 4e18 - a0);
        assertEq(r1, 1e18 - a1);
    }

    // L6: sync sets the reserves to the balances.
    function testSyncMatchesBalances() public {
        _deposit(4e18, 1e18, alice);
        t0.mint(address(pool), 123);
        pool.sync();
        (uint256 r0,) = pool.getReserves();
        assertEq(r0, 4e18 + 123);
    }

    function testBalanceAbove112BitsReverts() public {
        t0.mint(address(pool), uint256(1) << 112);
        t1.mint(address(pool), 1e18);
        vm.expectRevert(bytes("Pool: OVERFLOW"));
        pool.mint(alice);
    }

    // L7: a token that calls back into the pool during a transfer hits the lock.
    function testReentrancyIsBlocked() public {
        _deposit(10e18, 10e18, alice);
        t1.setHook(address(pool), abi.encodeWithSelector(IPool.sync.selector));
        t0.mint(address(pool), 1e18);
        vm.expectRevert();
        pool.swap(0, 1e17, bob);
    }

    // LP share ledger.
    function testLpTransferAndAllowance() public {
        uint256 liq = _deposit(4e18, 1e18, alice);
        vm.prank(alice);
        pool.approve(bob, liq);
        assertEq(pool.lpAllowance(alice, bob), liq);
        vm.prank(bob);
        pool.transferFrom(alice, bob, liq);
        assertEq(pool.lpBalanceOf(bob), liq);
        assertEq(pool.lpBalanceOf(alice), 0);
        assertEq(pool.lpAllowance(alice, bob), 0);
        vm.prank(bob);
        vm.expectRevert(bytes("Pool: INSUFFICIENT_ALLOWANCE"));
        pool.transferFrom(alice, bob, 1);
    }
}
