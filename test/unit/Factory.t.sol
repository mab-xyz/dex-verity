// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "../DexBase.sol";

/// Unit tests of the Verity-compiled Factory, and the full stack router → factory → pool.
contract FactoryTest is DexBase {
    IFactory factory;
    bytes poolInitcode;
    MockERC20 a;
    MockERC20 b;
    address alice = address(0xA11CE);

    function setUp() public {
        poolInitcode = vm.parseBytes(string.concat("0x", vm.readFile("out/Pool.bin")));
        factory = IFactory(deployBin("Factory", abi.encode(keccak256(poolInitcode))));
        a = new MockERC20("A");
        b = new MockERC20("B");
    }

    function _sorted() internal view returns (address t0, address t1) {
        (t0, t1) = address(a) < address(b) ? (address(a), address(b)) : (address(b), address(a));
    }

    function testCreatePoolDeterministicAddressAndRegistry() public {
        (address t0, address t1) = _sorted();
        address pool = factory.createPool(address(b), address(a), poolInitcode);
        bytes32 salt = keccak256(abi.encode(t0, t1));
        assertEq(pool, vm.computeCreate2Address(salt, keccak256(poolInitcode), address(factory)));
        assertEq(factory.getPool(t0, t1), pool);
        assertEq(factory.getPool(t1, t0), pool);
        assertEq(factory.allPoolsLength(), 1);
        assertEq(factory.poolAt(0), pool);
        // initialised by the factory with the sorted tokens: a second init is rejected
        vm.prank(address(factory));
        vm.expectRevert(bytes("Pool: ALREADY_INITIALIZED"));
        IPool(pool).initPool(t0, t1);
    }

    function testDuplicatePairReverts() public {
        factory.createPool(address(a), address(b), poolInitcode);
        vm.expectRevert(bytes("Factory: POOL_EXISTS"));
        factory.createPool(address(b), address(a), poolInitcode);
    }

    function testIdenticalAndZeroTokensRevert() public {
        vm.expectRevert(bytes("Factory: IDENTICAL_ADDRESSES"));
        factory.createPool(address(a), address(a), poolInitcode);
        vm.expectRevert(bytes("Factory: ZERO_ADDRESS"));
        factory.createPool(address(0), address(a), poolInitcode);
    }

    function testWrongInitcodeReverts() public {
        bytes memory other = bytes.concat(poolInitcode, hex"00");
        vm.expectRevert(bytes("Factory: WRONG_INITCODE"));
        factory.createPool(address(a), address(b), other);
    }

    function testFullStackThroughRouter() public {
        address pool = factory.createPool(address(a), address(b), poolInitcode);
        IRouter router = IRouter(deployBin("Router", abi.encode(address(factory))));
        a.mint(alice, 100e18);
        b.mint(alice, 100e18);
        vm.startPrank(alice);
        a.approve(address(router), type(uint256).max);
        b.approve(address(router), type(uint256).max);
        uint256 liq = router.addLiquidity(address(a), address(b), 10e18, 10e18, 0, 0, alice, block.timestamp);
        assertEq(liq, 10e18 - 1000);
        uint256 out = router.swapExactIn(1e18, 0, address(a), address(b), alice, block.timestamp);
        assertEq(out, refAmountOut(1e18, 10e18, 10e18));
        vm.stopPrank();
        (uint256 r0, uint256 r1) = IPool(pool).getReserves();
        assertGe(r0 * r1, uint256(10e18) * 10e18);
    }
}
