import Lake
open Lake DSL

package «dex-verity» where
  version := v!"0.1.0"

-- Verity with the mab-xyz fork fixes (composite returns, ECM checks, real
-- keccak256/CREATE2 semantics and copyBytes in the EDSL, ...).
require verity from git
  "https://github.com/mab-xyz/verity.git"@"7fe2fad4cd7fad034808d45d11d83f884cca3bef"

@[default_target]
lean_lib «Dex» where
  globs := #[.andSubmodules `Dex]

/-- Emits Yul + ABI for the DEX contracts: `lake exe dex-compile OUT_DIR`. -/
lean_exe «dex-compile» where
  root := `DexCompile
  supportInterpreter := true
