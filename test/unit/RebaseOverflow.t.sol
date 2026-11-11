// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "../DexBase.sol";

/// Truthful balances with an explicit negative rebase, scoped to this regression.
contract RebaseToken is MockERC20 {
    constructor() MockERC20("Rebase") {}

    function shrink(address owner, uint256 target) external {
        require(target <= balanceOf[owner], "not a shrink");
        totalSupply -= balanceOf[owner] - target;
        balanceOf[owner] = target;
    }
}

/// Reachability witness for current behavior, not a claim that overflow is desirable.
contract RebaseOverflowTest is DexBase {
    function test_sameDepositsWithoutRebasesPreserveLedger() public {
        RebaseToken a = new RebaseToken();
        RebaseToken b = new RebaseToken();
        IPool pool = IPool(deployBin("Pool", ""));
        (address t0, address t1) = address(a) < address(b)
            ? (address(a), address(b)) : (address(b), address(a));
        pool.initPool(t0, t1);
        uint256[4] memory deposits = [uint256(1 << 100), (1 << 100) - 1, (1 << 55) - 1, 1];
        uint256 supply;
        for (uint256 i; i < deposits.length; i++) {
            // The same deposits as the witness, but no balance shrink between mints.
            pool.sync();
            a.mint(address(pool), deposits[i]);
            b.mint(address(pool), deposits[i]);
            assertEq(pool.mint(address(this)), i == 0 ? deposits[i] - 1000 : deposits[i]);
            supply += deposits[i];
            assertLedger(pool, supply);
        }
    }

    function test_rebasesReachSupplyOverflowFromDeployment() public {
        RebaseToken a = new RebaseToken();
        RebaseToken b = new RebaseToken();
        IPool pool = IPool(deployBin("Pool", ""));
        (address t0, address t1) = address(a) < address(b)
            ? (address(a), address(b)) : (address(b), address(a));
        pool.initPool(t0, t1);
        a.mint(address(pool), 1 << 100);
        b.mint(address(pool), 1 << 100);
        assertEq(pool.mint(address(this)), (1 << 100) - 1000);
        assertLedger(pool, 1 << 100);

        grow(a, b, pool, 1 << 100, (1 << 200) - (1 << 100));
        assertLedger(pool, 1 << 200);
        grow(a, b, pool, 1 << 55, (1 << 255) - (1 << 200));
        assertLedger(pool, 1 << 255);

        // Each quotient fits; only the final supply addition overflows.
        grow(a, b, pool, 2, 1 << 255);
        assertEq(pool.lpTotalSupply(), 0);
        assertEq(pool.lpBalanceOf(address(0)), 1000);
        assertEq(pool.lpBalanceOf(address(this)), type(uint256).max - 999);
        assertGt(pool.lpBalanceOf(address(this)), pool.lpTotalSupply());
    }

    function assertLedger(IPool pool, uint256 supply) internal view {
        assertEq(pool.lpTotalSupply(), supply);
        assertEq(pool.lpBalanceOf(address(0)), 1000);
        assertEq(pool.lpBalanceOf(address(this)), supply - 1000);
    }

    function grow(RebaseToken a, RebaseToken b, IPool pool, uint256 balance, uint256 minted) internal {
        a.shrink(address(pool), 1);
        b.shrink(address(pool), 1);
        pool.sync();
        (uint256 r0, uint256 r1) = pool.getReserves();
        assertEq(r0, 1);
        assertEq(r1, 1);
        a.mint(address(pool), balance - 1);
        b.mint(address(pool), balance - 1);
        assertEq(pool.mint(address(this)), minted);
        (r0, r1) = pool.getReserves();
        assertEq(r0, balance);
        assertEq(r1, balance);
        assertLt(r0, 1 << 112);
        assertLt(r1, 1 << 112);
    }
}
