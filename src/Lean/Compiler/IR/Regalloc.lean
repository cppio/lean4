prelude
import Lean.Compiler.IR.NormIds

namespace Lean.IR

private abbrev VarIds := Std.HashSet VarId

private def Arg.varIds : Arg → VarIds
  | var id => {id}
  | irrelevant => {}

private def Expr.varIds : Expr → VarIds
  | lit _ => {}
  | reset _ x
  | proj _ x
  | uproj _ x
  | sproj _ _ x
  | box _ x
  | unbox x
  | isShared x => {x}
  | ctor _ ys
  | fap _ ys
  | pap _ ys => ys.foldl (· ∪ ·.varIds) {}
  | reuse x _ _ ys
  | ap x ys => ys.foldl (· ∪ ·.varIds) {x}

private structure LivenessResult where
  body : FnBody
  varIds : VarIds
  deriving Inhabited

private def LivenessResult.map (f : FnBody → FnBody) (xs : VarIds) : LivenessResult → LivenessResult
  | ⟨body, varIds⟩ =>
    let xs := xs.filter (!varIds.contains ·)
    if xs.isEmpty
    then ⟨f body, varIds⟩
    else ⟨.mdata ⟨xs.toList.map fun x => (`free, .ofNat x.idx)⟩ (f body), varIds ∪ xs⟩

private def LivenessResult.remove (x : VarId) : LivenessResult → LivenessResult
  | ⟨body, varIds⟩ => ⟨body, varIds.erase x⟩

private partial def FnBody.livenessAux : FnBody → ReaderM (Std.HashMap JoinPointId VarIds) LivenessResult
  | vdecl x ty e b => return (← b.livenessAux).map (vdecl x ty e) (e.varIds.insert x) |>.remove x
  | jdecl j xs v b => fun joinVarIds =>
    let ⟨v', varIds⟩ := v.livenessAux joinVarIds |>.map id (xs.foldl (·.insert ·.x) {})
    b.livenessAux (joinVarIds.insert j varIds) |>.map (jdecl j xs v') {}
  | set x i y b => return (← b.livenessAux).map (set x i y) (y.varIds.insert x)
  | setTag x cidx b => return (← b.livenessAux).map (setTag x cidx) {x}
  | uset x i y b => return (← b.livenessAux).map (uset x i y) {x, y}
  | sset x i offset y ty b => return (← b.livenessAux).map (sset x i offset y ty) {x, y}
  | inc x n c persistent b => return (← b.livenessAux).map (inc x n c persistent) {x}
  | dec x n c persistent b => return (← b.livenessAux).map (dec x n c persistent) {x}
  | del x b => return (← b.livenessAux).map (del x) {x}
  | mdata _ b => b.livenessAux
  | case tid x xType cs => do
    let cs' ← cs.mapM fun
      | .ctor info b => do let ⟨body, varIds⟩ ← b.livenessAux; return (AltCore.ctor info body, varIds)
      | .default b => do let ⟨body, varIds⟩ ← b.livenessAux; return (.default body, varIds)
    let varIds' := cs'.foldl (· ∪ ·.snd) {x}
    let cs' := cs'.map fun
      | (.ctor info b, varIds) => .ctor info <| LivenessResult.body <| .map id varIds' ⟨b, varIds⟩
      | (.default b, varIds) => .default <| LivenessResult.body <| .map id varIds' ⟨b, varIds⟩
    return ⟨case tid x xType cs', varIds'⟩
  | ret x => return ⟨ret x, x.varIds⟩
  | jmp j ys => fun joinVarIds =>
    let varIds := joinVarIds[j]!
    let xs := ys.foldl (· ∪ ·.varIds) {}
    let xs := xs.filter (!varIds.contains ·)
    if xs.isEmpty
    then ⟨jmp j ys, varIds⟩
    else ⟨mdata ⟨xs.toList.map fun x => (`free.jmp, .ofNat x.idx)⟩ (jmp j ys), varIds ∪ xs⟩
  | unreachable => return ⟨unreachable, {}⟩

private def FnBody.liveness (body : FnBody) : FnBody :=
  livenessAux body {} |>.body

private structure FreeVarSet where
  freeVars : VarIdSet
  unusedIdx : Nat

private instance : Inhabited FreeVarSet where
  default := ⟨{}, 0⟩

private instance : Inter FreeVarSet where
  inter lhs rhs :=
    let unusedIdx := lhs.unusedIdx.max rhs.unusedIdx
    let lhs' := lhs.freeVars.union <| .ofList <| .map .mk <| .range' lhs.unusedIdx (unusedIdx - lhs.unusedIdx)
    let rhs' := rhs.freeVars.union <| .ofList <| .map .mk <| .range' rhs.unusedIdx (unusedIdx - rhs.unusedIdx)
    ⟨lhs'.intersectBy (fun _ _ _ => ⟨⟩) rhs', unusedIdx⟩

private def FreeVarSet.insertAll (xs : List VarId) : FreeVarSet → FreeVarSet
  | ⟨freeVars, unusedIdx⟩ => ⟨xs.foldl .insert freeVars, unusedIdx⟩

private def FreeVarSet.pop : FreeVarSet → VarId × FreeVarSet
  | { freeVars, unusedIdx } =>
    if let some x := freeVars.min
    then (x, { freeVars := freeVars.erase x, unusedIdx })
    else (⟨unusedIdx⟩, { freeVars, unusedIdx := unusedIdx + 1 })

private structure RegallocCtx where
  map : Std.HashMap VarId VarId
  freeVars : FreeVarSet

private abbrev RegallocM := ReaderT RegallocCtx (StateM (Std.HashMap JoinPointId FreeVarSet))

private def VarId.rename (x : VarId) : RegallocM VarId
  | ctx => return ctx.map[x]!

private def Arg.rename : Arg → RegallocM Arg
  | var id => return var (← id.rename)
  | irrelevant => return irrelevant

private def Param.rename (p : Param) : RegallocM Param :=
  return { p with x := ← p.x.rename }

private def Expr.rename : Expr → RegallocM Expr
  | ctor i ys => return ctor i (← ys.mapM Arg.rename)
  | reset n x => return reset n (← x.rename)
  | reuse x i updtHeader ys => return reuse (← x.rename) i updtHeader (← ys.mapM Arg.rename)
  | proj i x => return proj i (← x.rename)
  | uproj i x => return uproj i (← x.rename)
  | sproj n offset x => return sproj n offset (← x.rename)
  | fap c ys => return fap c (← ys.mapM Arg.rename)
  | pap c ys => return pap c (← ys.mapM Arg.rename)
  | ap x ys => return ap (← x.rename) (← ys.mapM Arg.rename)
  | box ty x => return box ty (← x.rename)
  | unbox x => return unbox (← x.rename)
  | lit v => return lit v
  | isShared x => return isShared (← x.rename)

private def free (d : MData) (k : RegallocM α) : RegallocM α
  | { map, freeVars } =>
    let d := d.entries.filterMap fun
      | (`free, .ofNat i) => some (map.get! ⟨i⟩)
      | (`free.jmp, .ofNat _) => none -- TODO
      | _ => none
    k { map, freeVars := freeVars.insertAll d }

private def alloc (x : VarId) (k : RegallocM α) : RegallocM α
  | { map, freeVars } =>
    let (y, freeVars') := freeVars.pop
    k { map := map.insert x y, freeVars := freeVars' }

private partial def FnBody.regalloc : FnBody → RegallocM FnBody
  | vdecl x ty e b => alloc x <| return vdecl (← x.rename) ty (← e.rename) (← b.regalloc)
  | jdecl j xs v b => do
    let b' ← b.regalloc
    xs.foldl (fun k x => alloc x.x k) do
    let v' ← v.regalloc { map := (← read).map, freeVars := (← get)[j]! }
    return jdecl j (← xs.mapM Param.rename) v' b'
  | set x i y b => return set (← x.rename) i (← y.rename) (← b.regalloc)
  | setTag x cidx b => return setTag (← x.rename) cidx (← b.regalloc)
  | uset x i y b => return uset (← x.rename) i (← y.rename) (← b.regalloc)
  | sset x i offset y ty b => return sset (← x.rename) i offset (← y.rename) ty (← b.regalloc)
  | inc x n c persistent b => return inc (← x.rename) n c persistent (← b.regalloc)
  | dec x n c persistent b => return dec (← x.rename) n c persistent (← b.regalloc)
  | del x b => return del (← x.rename) (← b.regalloc)
  | mdata d b => free d b.regalloc
  | case tid x xType cs =>
    return case tid (← x.rename) xType <| ← cs.mapM fun
      | .ctor info b => return .ctor info (← b.regalloc)
      | .default b => return .default (← b.regalloc)
  | ret x => return ret (← x.rename)
  | jmp j ys => do
    let ctx ← read
    modify fun joinSets => joinSets.modify j (· ∩ ctx.freeVars)
    return jmp j (← ys.mapM Arg.rename)
  | unreachable => return unreachable

def Decl.regalloc (decl : Decl) : Decl :=
  match decl.normalizeIds with
  | fdecl f xs type body info =>
    let k := return fdecl f (← xs.mapM Param.rename) type (← body.liveness.regalloc) info
    xs.foldr (fun x => alloc x.x) k |>.run ⟨{}, default⟩ |>.run' {}
  | extern f xs type ext => extern f xs type ext
