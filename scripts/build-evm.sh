#!/bin/bash
# Compile the Verity contracts to Yul (lake exe dex-compile) and the Yul to EVM creation
# bytecode, one hex file per contract in out/<Name>.bin (read by the Foundry tests).
set -euo pipefail
cd "$(dirname "$0")/.."
SOLC=${SOLC:-solc}
lake exe dex-compile out >/dev/null 2>&1 || { echo "dex-compile failed" >&2; exit 1; }
for yul in out/*.yul; do
  name=$(basename "$yul" .yul)
  "$SOLC" --strict-assembly --evm-version cancun --optimize --bin "$yul" \
    2>/dev/null | awk '/Binary representation:/{getline; print; exit}' | tr -d '\n' > "out/$name.bin"
  [ -s "out/$name.bin" ] || { echo "no bytecode for $name" >&2; exit 1; }
done
