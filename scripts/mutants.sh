#!/bin/bash
# Mutation testing of the Foundry suites against the compiled Pool: each mutant edits
# out/Pool.yul (sed), rebuilds out/Pool.bin, and must make at least one test fail.
# Prints one line per mutant: KILLED or SURVIVED. Exit 1 if any mutant survives.
set -uo pipefail
cd "$(dirname "$0")/.."
SOLC=${SOLC:-solc}
scripts/build-evm.sh
cp out/Pool.yul out/Pool.yul.orig
cp out/Pool.bin out/Pool.bin.orig
survived=0
mutant() {
  local name=$1 expr=$2
  sed "$expr" out/Pool.yul.orig > out/Pool.yul
  if cmp -s out/Pool.yul out/Pool.yul.orig; then echo "INVALID $name (no change)"; survived=1; return; fi
  "$SOLC" --strict-assembly --evm-version cancun --optimize --bin out/Pool.yul 2>/dev/null \
    | awk '/Binary representation:/{getline; print; exit}' | tr -d '\n' > out/Pool.bin
  if forge test --no-match-path "test/invariant/*" >/dev/null 2>&1 \
     && forge test --match-path "test/invariant/*" >/dev/null 2>&1; then
    echo "SURVIVED $name"; survived=1
  else
    echo "KILLED $name"
  fi
}
mutant fee-removed          's/mul(in0, 3))/mul(in0, 0))/g; s/mul(in1, 3))/mul(in1, 0))/g'
mutant k-check-flipped      's/if lt(mul(adj0, adj1), mul(mul(r0, r1), 1000000))/if gt(mul(adj0, adj1), mul(mul(r0, r1), 1000000))/g'
mutant k-check-removed      's/if lt(mul(adj0, adj1), mul(mul(r0, r1), 1000000))/if 0/g'
mutant min-liquidity-unlocked 's/add(lockedBal, 1000)/add(lockedBal, 0)/g'
mutant burn-cap-removed     's/if iszero(lt(nb0, 5192296858534827628530496329220096))/if 0/g; s/if iszero(lt(nb1, 5192296858534827628530496329220096))/if 0/g'
mutant lock-ignored         's/if tload(9) {/if 0 {/g'
mutant supply-overflow-unchecked 's/if lt(add(t0, liquidity), t0) {/if 0 {/g'
cp out/Pool.yul.orig out/Pool.yul
cp out/Pool.bin.orig out/Pool.bin
rm -f out/Pool.yul.orig out/Pool.bin.orig
exit $survived
