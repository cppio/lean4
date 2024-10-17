prelude
import Lean.Attributes
import Lean.Util.Recognizers

namespace Lean.Rewriting

private def validateLHSLevel : Level → Option Unit
  | .zero | .param _ => return
  | .succ lhs => validateLHSLevel lhs
  | _ => failure

private partial def validateLHS (bvars : Array Nat) (lhs : Expr) : Option (Array Nat) := do
  if let .bvar bvar := lhs then
    return if bvars.contains bvar then bvars else bvars.push bvar
  else
    let .const _ us := lhs.getAppFn
      | failure
    us.forM validateLHSLevel
    lhs.getAppArgs.foldlM validateLHS bvars

private structure RewriteRule where
  lhs : Expr
  rhs : Expr
  bvarCount : Nat

private initialize rewritingExt :
  PersistentEnvExtension
    (Name × Array RewriteRule)
    (Name × RewriteRule)
    (NameMap (Array RewriteRule × Array RewriteRule))
← registerPersistentEnvExtension {
  mkInitial := return {}
  addImportedFn := fun allImportedEntries =>
    return allImportedEntries.foldl (init := {}) fun entries importedEntries =>
      importedEntries.foldl (init := entries) fun entries (name, newRules) =>
        entries.insert name <|
          if let some (rules, moduleRules) := entries.find? name then
            (rules ++ newRules, moduleRules)
          else
            (newRules, #[])
  addEntryFn := fun entries (name, rule) =>
    entries.insert name <|
      if let some (rules, moduleRules) := entries.find? name then
        (rules.push rule, moduleRules.push rule)
      else
        (#[rule], #[rule])
  exportEntriesFn := fun entries =>
    entries.fold (init := #[]) fun exportedEntries name (_, moduleRules) =>
      if moduleRules.isEmpty
      then exportedEntries
      else exportedEntries.push (name, moduleRules)
}

initialize registerBuiltinAttribute {
  name := `rewrite
  descr := "Definitional Rewrite Rule"
  add := fun decl _stx kind => do
    let .global := kind
      | throwError "{kind} rewrite attribute is invalid"
    let ci ← Lean.getConstInfo decl
    let some (_, lhs, rhs) := ci.type.getForallBody.eq?
      | throwError "rewrite attribute can only be applied to an equation"
    if !lhs.isApp then
      throwError "rewrite lhs must be an application"
    let some bvars := validateLHS #[] lhs
      | throwError "rewrite lhs not supported"
    if bvars.size < ci.type.getForallBinderNames.length then
      throwError "rewrite rule contains unused variables"
    modifyEnv fun env =>
      rewritingExt.addEntry env (lhs.getAppFn.constName!, { lhs, rhs, bvarCount := bvars.size })
}

private structure MatchState where
  bvars : Array (Option Expr)
  levels : NameMap Level := {}

private def matchLHSLevel [Monad M] : Level → Level → StateT MatchState (OptionT M) Unit
  | .param name, level => do
    let state ← get
    if let some l := state.levels.find? name then
      if !level.isEquiv l then
        failure
    else
      set { state with levels := state.levels.insert name level }
  | .zero, .zero => return
  | .succ lhs, .succ level => matchLHSLevel lhs level
  | _, _ => failure

private partial def matchLHS [Monad M] (whnf : Expr → M Expr) (lhs expr : Expr) (outer : Bool) : StateT MatchState (OptionT M) Unit := do
  if let .bvar bvar := lhs then
    let state ← get
    if let some e := state.bvars.get! bvar then
      if !expr.eqv e then
        failure
    else
      set { state with bvars := state.bvars.set! bvar expr }
  else
    let lhsFn := lhs.getAppFn
    let expr ← if outer then pure expr else whnf expr
    let .const fn us := expr.getAppFn
      | failure
    if fn != lhsFn.constName! || us.length != lhsFn.constLevels!.length then
      failure
    for lhsLevel in lhsFn.constLevels!, u in us do
      matchLHSLevel lhsLevel u
    let lhsArgs := lhs.getAppArgs
    let args := expr.getAppArgs
    if args.size < lhsArgs.size || (!outer && args.size > lhsArgs.size) then
      failure
    for lhsArg in lhsArgs, arg in args do
      matchLHS whnf lhsArg arg false

def reduceRewrite [Monad M] (whnf : Expr → M Expr) (env : Environment) (e : Expr) : M (Option Expr) := do
  let some fn := e.getAppFn.constName?
    | return none
  let some (rules, _) := rewritingExt.getState env |>.find? fn
    | return none
  for { lhs, rhs, bvarCount } in rules do
    let some (_, { bvars, levels }) ← matchLHS whnf lhs e true |>.run { bvars := mkArray bvarCount none }
      | continue
    let bvars := bvars.map Option.get!
    let rhs := rhs.instantiateLevelParamsCore levels.find?
    let rhs := rhs.instantiate bvars
    let rhs := mkAppRange rhs lhs.getAppNumArgs e.getAppNumArgs e.getAppArgs
    return rhs
  return none

@[export lean_rewriting_reduce]
private def rewritingReduce : (Expr → Expr) → Environment → Expr → Option Expr :=
  reduceRewrite (M := Id)
