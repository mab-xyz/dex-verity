import Lake
open Lake DSL

package «dex-verity» where
  version := v!"0.1.0"

-- Verity with the mab-xyz fork fixes (struct/composite returns, ECM checks, ...).
require verity from git
  "https://github.com/mab-xyz/verity.git"@"adc0582f34096d32bd9f3a0a274b7bc8d70ecd3b"

@[default_target]
lean_lib «Dex» where
  globs := #[.andSubmodules `Dex]

/-- Emits Yul + ABI for the DEX contracts: `lake exe dex-compile OUT_DIR`. -/
lean_exe «dex-compile» where
  root := `DexCompile
  supportInterpreter := true
