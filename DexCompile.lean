import Compiler.CompileDriver
import Dex

/-! `lake exe dex-compile OUT_DIR`: Yul, ABI and storage layout for every DEX contract. -/

def dexSpecs : List Compiler.CompilationModel.CompilationModel :=
  [Dex.Pool.spec, Dex.Router.spec, Dex.Factory.spec]

def main (args : List String) : IO UInt32 := do
  let out := args.headD "out"
  IO.FS.createDirAll out
  Compiler.compileSpecsWithOptions dexSpecs out false [] {} none none none (some out)
  pure 0
