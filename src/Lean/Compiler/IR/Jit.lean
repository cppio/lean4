prelude
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.Regalloc

namespace Lean

namespace IR

opaque JitCompiledDecl : Type

@[extern "lean_jit_compile"]
opaque jitCompile (env : @& Environment) (decls : @& Array IR.Decl) : Except String (Array JitCompiledDecl)

@[extern "lean_jit_eval"]
unsafe def jitEval α (compiledDecl : @& JitCompiledDecl) : α :=
  jitEval α compiledDecl

builtin_initialize jitCompiledExt : EnvExtension (PHashMap Name JitCompiledDecl) ←
  registerEnvExtension do return {}

@[export lean_jit_lookup]
def jitLookup (env : Environment) (name : Name) : Option JitCompiledDecl :=
  jitCompiledExt.getState env |>.find? name

def compileJit [Monad m] [MonadEnv m] [MonadError m] (names : Array Name) (regalloc := true) : m Unit := do
  let env ← Lean.getEnv
  let decls ← names.mapM fun name => do
    let some decl := findEnvDecl env name
      | throwError "unknown declaration '{name}'"
    return if regalloc then decl.regalloc else decl
  match jitCompile env decls with
  | .error e => throwError e
  | .ok compiledDecls =>
  setEnv <| jitCompiledExt.modifyState env <| names.zip compiledDecls |>.foldl fun map (name, compiledDecl) => map.insert name compiledDecl

unsafe def evalConstJit [Monad m] [MonadEnv m] [MonadError m] α (constName : Name) : m α := do
  let some compiledDecl := jitCompiledExt.getState (← Lean.getEnv) |>.find? constName
    | throwError "cannot find jit compiled {constName}"
  return jitEval α compiledDecl

partial def FnBody.maxVarId : FnBody → Index
  | vdecl x _ _ b => b.maxVarId.max x.idx.succ
  | jdecl _ xs v b => xs.foldl (fun x y => x.max y.x.idx.succ) (v.maxVarId.max b.maxVarId)
  | set _ _ _ b
  | setTag _ _ b
  | uset _ _ _ b
  | sset _ _ _ _ _ b
  | inc _ _ _ _ b
  | dec _ _ _ _ b
  | del _ b
  | mdata _ b => b.maxVarId
  | case _ _ _ cs => (cs.map fun | .ctor _ b => b.maxVarId | .default b => b.maxVarId).foldl .max 0
  | ret _
  | jmp ..
  | unreachable => 0

@[export lean_ir_decl_max_var_id]
partial def Decl.maxVarId : Decl → Index
  | fdecl _ xs _ body _ => xs.foldl (fun x y => x.max y.x.idx.succ) body.maxVarId
  | extern .. => 0

partial def FnBody.maxJPId : FnBody → Index
  | jdecl j _ v b => v.maxVarId.max b.maxVarId |>.max j.idx.succ
  | vdecl _ _ _ b
  | set _ _ _ b
  | setTag _ _ b
  | uset _ _ _ b
  | sset _ _ _ _ _ b
  | inc _ _ _ _ b
  | dec _ _ _ _ b
  | del _ b
  | mdata _ b => b.maxVarId
  | case _ _ _ cs => (cs.map fun | .ctor _ b => b.maxVarId | .default b => b.maxVarId).foldl .max 0
  | ret _
  | jmp ..
  | unreachable => 0

@[export lean_ir_decl_max_jp_id]
partial def Decl.maxJPId : Decl → Index
  | fdecl _ _ _ body _ => body.maxJPId
  | extern .. => 0
