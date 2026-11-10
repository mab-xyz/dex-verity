// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "../DexBase.sol";

/// Drives random sequences of pool operations (bounded, always well-formed so most calls
/// succeed) and records k before/after each successful swap.
contract PoolHandler is Test {
    IPool public pool;
    MockERC20 public t0;
    MockERC20 public t1;
    address[] public actors;
    bool public kDecreased;
    uint256 public swaps;

    constructor(IPool p, MockERC20 a, MockERC20 b) {
        pool = p;
        t0 = a;
        t1 = b;
        actors.push(address(0xA1));
        actors.push(address(0xA2));
        actors.push(address(0xA3));
    }

    function actorCount() external view returns (uint256) {
        return actors.length;
    }

    function _actor(uint256 i) internal view returns (address) {
        return actors[i % actors.length];
    }

    function add(uint256 who, uint96 a0, uint96 a1) external {
        a0 = uint96(bound(a0, 1e3, 1e24));
        a1 = uint96(bound(a1, 1e3, 1e24));
        t0.mint(address(pool), a0);
        t1.mint(address(pool), a1);
        try pool.mint(_actor(who)) {} catch {
            pool.sync(); // absorb the transfer so reserves track balances
        }
    }

    function remove(uint256 who, uint256 frac) external {
        address a = _actor(who);
        uint256 bal = pool.lpBalanceOf(a);
        if (bal == 0) return;
        uint256 liq = bound(frac, 1, bal);
        vm.prank(a);
        pool.transfer(address(pool), liq);
        try pool.burn(a) {} catch {
            // shares stay at the pool address; they still count towards the supply
        }
    }

    function swap(uint96 amountIn, bool zeroForOne) external {
        (uint256 r0, uint256 r1) = pool.getReserves();
        if (r0 == 0 || r1 == 0) return;
        amountIn = uint96(bound(amountIn, 1, 1e24));
        (uint256 rIn, uint256 rOut) = zeroForOne ? (r0, r1) : (r1, r0);
        uint256 out = (uint256(amountIn) * 997 * rOut) / (rIn * 1000 + uint256(amountIn) * 997);
        if (out == 0) return;
        (zeroForOne ? t0 : t1).mint(address(pool), amountIn);
        uint256 kBefore = r0 * r1;
        try pool.swap(zeroForOne ? 0 : out, zeroForOne ? out : 0, address(0xBEEF)) {
            (uint256 n0, uint256 n1) = pool.getReserves();
            if (n0 * n1 < kBefore) kDecreased = true;
            swaps++;
        } catch {
            pool.sync();
        }
    }

    function donate(uint96 amount, bool token0) external {
        (token0 ? t0 : t1).mint(address(pool), bound(amount, 1, 1e22));
        pool.sync();
    }

    function lpTransfer(uint256 from, uint256 to, uint256 amount) external {
        address a = _actor(from);
        uint256 bal = pool.lpBalanceOf(a);
        if (bal == 0) return;
        vm.prank(a);
        pool.transfer(_actor(to), bound(amount, 0, bal));
    }
}

/// Invariants of the compiled Pool under random operation sequences:
/// LP conservation (L2), reserves = balances (L6), k monotone on swaps (L3), reserve cap.
contract PoolInvariantTest is DexBase {
    PoolHandler handler;
    IPool pool;
    MockERC20 t0;
    MockERC20 t1;

    function setUp() public {
        (t0, t1, pool) = newPair();
        handler = new PoolHandler(pool, t0, t1);
        // The handler is not the pool's factory; it only uses the public entry points.
        targetContract(address(handler));
    }

    function invariant_lpSupplyIsSumOfHolders() public view {
        uint256 sum = pool.lpBalanceOf(address(0)) + pool.lpBalanceOf(address(pool));
        for (uint256 i = 0; i < handler.actorCount(); i++) {
            sum += pool.lpBalanceOf(handler.actors(i));
        }
        assertEq(sum, pool.lpTotalSupply());
    }

    function invariant_reservesMatchBalances() public view {
        (uint256 r0, uint256 r1) = pool.getReserves();
        assertEq(r0, t0.balanceOf(address(pool)));
        assertEq(r1, t1.balanceOf(address(pool)));
    }

    function invariant_reservesBelowCap() public view {
        (uint256 r0, uint256 r1) = pool.getReserves();
        assertLt(r0, uint256(1) << 112);
        assertLt(r1, uint256(1) << 112);
    }

    function invariant_kNeverDecreasesOnSwap() public view {
        assertFalse(handler.kDecreased());
    }
}
