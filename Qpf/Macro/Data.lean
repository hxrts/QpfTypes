import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Data.QPF.Multivariate.Constructions.Fix

import Qpf.Elab.ShapeType

import Qpf.Macro.Data.Constructors
import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.Count
import Qpf.Macro.Data.View
import Qpf.Macro.Data.Ind
import Qpf.Macro.Common
import Qpf.Macro.Comp

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)
open Parser.Term (namedArgument)
open PrettyPrinter (delab)

open Macro (withQPFTraceNode elabCommandAndTrace)

private def Array.enum (as : Array α) : Array (Nat × α) :=
  (Array.range as.size).zip as

/-! ## Universe utilities -/

private def getUniverseDepsLevel : Level → List Name
  | .zero => []
  | .succ l => getUniverseDepsLevel l
  | .max l1 l2 => getUniverseDepsLevel l1 ++ getUniverseDepsLevel l2
  | .imax l1 l2 => getUniverseDepsLevel l1 ++ getUniverseDepsLevel l2
  | .param n => [n]
  | .mvar _ => []

private def getUniverseDeps (e : Expr) : MetaM (List Name) := do
  let rec visit (e : Expr) : MetaM (List Name) := do
    match e with
    | .sort l => pure (getUniverseDepsLevel l)
    | .forallE _ t b _ => do
        let dt ← visit t
        let db ← visit b
        pure (dt ++ db)
    | .app f a => do
        let df ← visit f
        let da ← visit a
        pure (df ++ da)
    | .lam _ t b _ => do
        let dt ← visit t
        let db ← visit b
        pure (dt ++ db)
    | .const _ ls => pure (ls.foldl (fun acc l => acc ++ getUniverseDepsLevel l) [])
    | .letE _ t v b _ => do
        let dt ← visit t
        let dv ← visit v
        let db ← visit b
        pure (dt ++ dv ++ db)
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => pure []
  visit e

private def computeResultUniverse (usedUnivs : List Name) : Level :=
  match usedUnivs with
  | [] => .zero
  | u :: us => us.foldl (fun acc n => .max acc (.param n)) (.param u)

/--
  Given a natural number `n`, produce a sequence of `n` calls of `.fs`, ending in `.fz`.

  The result corresponds to a `i : PFin2 _` such that `i.toNat == n`
-/
private def PFin2.quoteOfNat : Nat → Term
  | 0   => mkIdent ``PFin2.fz
  | n+1 => Syntax.mkApp (mkIdent ``PFin2.fs) #[(quoteOfNat n)]

private def Fin2.quoteOfNat : Nat → Term
  | 0   => mkIdent ``Fin2.fz
  | n+1 => Syntax.mkApp (mkIdent ``Fin2.fs) #[(quoteOfNat n)]


namespace Data.Command

/-!
  ## Parser
  for `data` and `codata` declarations
-/
section
  open Lean.Parser Lean.Parser.Command

  def inductive_like (cmd : String) : Parser
    := leading_parser cmd >> declId  >> optDeclSig
                        >> Parser.optional  (symbol " :=" <|> " where")
                        >> many ctor
                        >> optDeriving

  def data := inductive_like "data "
  def codata := inductive_like "codata "

  @[command_parser]
  def declaration : Parser
    := leading_parser declModifiers false >> (data <|> codata)
end

/-!
  ## Elaboration
-/
open Elab.Term (TermElabM)

def CtorView.declReplacePrefix (pref new_pref : Name) (ctor: CtorView) : CtorView :=
  { ctor with
      declName := ctor.declName.replacePrefix pref new_pref
  }


open Parser.Command (declId)
/-- Return a tuple of `declName, declId, shortDeclName` -/
private def addSuffixToDeclId {m} [Monad m] [MonadResolveName m] (declId : Syntax) (suffix : String) :
    m (Name × (TSyntax ``declId) × Name) := do
  let (id, _) := Elab.expandDeclIdCore declId
  let declName := Name.mkStr id suffix
  let declId := mkNode ``declId #[mkIdent declName, mkNullNode]

  let curNamespace ← getCurrNamespace
  let declName := curNamespace ++ declName

  let shortDeclName := Name.mkSimple suffix
  return (declName, declId, shortDeclName)

private def addSuffixToDeclIdent {m} [Monad m] [MonadResolveName m] (declId : Syntax) (suffix : String) :
    m Ident := do
  let (_, uncurriedDeclId, _) ← addSuffixToDeclId declId suffix
  pure ⟨uncurriedDeclId.raw[0]⟩

open private elabInductiveViews from Lean.Elab.MutualInductive in
open private elabCtors from Lean.Elab.Inductive in
private def elabInductiveView (vars : Array Expr) (view : InductiveView) : TermElabM Unit := do
  let view := {
    view
    elabCtors := fun rs r params => do
      let ctors ← elabCtors (rs.map (·.indFVar)) params r
      return { ctors }
  }
  let _ ← elabInductiveViews vars #[view]

open Parser in
/-- Collect argument types from a non-dependent arrow chain. -/
private partial def ctorArgTypes (ty : Syntax) : Array Syntax :=
  match ty with
  | Syntax.node _ ``Term.arrow #[arg, _arrow, tail] =>
      #[arg] ++ ctorArgTypes tail
  | _ =>
      #[]

private def ctorLiveArgNames (args : CtorArgs) : Array Name :=
  args.per_type.foldl (init := #[]) fun acc perType => acc ++ perType
/--
  Defines the "head" type of a polynomial functor

  That is, it defines a type with exactly as many constructor as the input type, but such that
  all constructors only keep the *dead* arguments (arguments not in functor positions).
-/
def mkHeadT (view : InductiveView) (ctorArgs : Array CtorArgs) : CommandElabM Name := do
  let (declName, declId, shortDeclName) ← addSuffixToDeclId view.declId "HeadT"
  withQPFTraceNode m!"defining `{declName}`" (tag := "mkHeadT") <| do
  -- If the original declId was `MyType`, we want to register the head type under `MyType.HeadT`



  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  -- The head type is the same as the original type, but with all constructor arguments removed
  -- When HeadT has dead parameters, constructors need explicit result types
  let deadBinderIdents := Macro.getBinderIdents view.binders.getArgs false
  let headTResult :=
    if deadBinderIdents.isEmpty then
      none  -- No parameters, no explicit type needed
    else
      -- With dead parameters, constructors must have result type: HeadT dead_params
      let headTIdent := mkIdent shortDeclName
      some $ Syntax.mkApp headTIdent deadBinderIdents

  let ctors ← (view.ctors.zip ctorArgs).mapM fun (ctor, args) => do
    let declName := ctor.declName.replacePrefix view.declName declName
    let liveArgs := ctorLiveArgNames args
    let argTypes := ctor.type?.map ctorArgTypes |>.getD #[]
    let deadArgTypes :=
      (argTypes.zip args.args).foldl (init := #[]) fun acc (ty, arg) =>
        if liveArgs.contains arg then acc else acc.push ty
    let ctorType? ←
      if deadArgTypes.isEmpty then
        pure headTResult
      else
        match headTResult with
        | none => pure none
        | some res =>
            let mut result : Term := ⟨res⟩
            for argTy in deadArgTypes.reverse do
              let argTyTerm : Term := ⟨argTy⟩
              result ← `($argTyTerm → $result)
            pure (some result.raw)
    pure { ctor with
      modifiers, declName,
      binders := mkNullNode,
      type? := ctorType?
      : CtorView
    }

  -- CRITICAL FIX: HeadT should take dead parameters as regular parameters
  -- The input view already has binders set to dead parameters only (from mkShape)
  -- We keep those dead parameters for HeadT

  -- Universe polymorphic HeadT: preserve levelNames from the original view
  let resultLevel := computeResultUniverse view.levelNames
  let headTType ← runTermElabM fun _ => do
    delab (mkSort (Level.succ resultLevel))

  -- IMPORTANT: HeadT is NOT an indexed family
  let view := { view with
    ctors, declId, declName, shortDeclName, modifiers,
    binders         := view.binders,  -- Keep dead parameters from Shape
    type?           := some headTType, -- Explicit universe
    levelNames      := view.levelNames
  }

  withQPFTraceNode "elabInductiveViews" <|
    runTermElabM (elabInductiveView · view)
  pure declName

open Parser Parser.Term Parser.Command in
/--
  Defines the "child" family of type vectors for an `n`-ary polynomial functor

  That is, it defines a type `ChildT : HeadT → TypeVec n` such that number of inhabitants of
  `ChildT a i` corresponds to the times that constructor `a` takes an argument of the `i`-th type
  argument
-/
def mkChildT (view : InductiveView) (r : Replace) (headTName : Name) (ctorArgs : Array CtorArgs)
    : CommandElabM Name := do
  -- If the original declId was `MyType`, we want to register the child type under `MyType.ChildT`
  let (declName, declId, _shortDeclName) ← addSuffixToDeclId view.declId "ChildT"
  withQPFTraceNode m!"defining `{declName}`" (tag := "mkChildT") <| do

  let resultLevel := computeResultUniverse view.levelNames
  let target_type ←
    runTermElabM fun _ => do
      let tv := mkApp (mkConst ``TypeVec [resultLevel]) (mkNatLit r.arity)
      delab tv

  let matchAlts ← (view.ctors.zip ctorArgs).mapM fun (ctor, args) => do
    let head := Lean.mkIdent (ctor.declName.replacePrefix view.declName headTName)
    let liveArgs := ctorLiveArgNames args
    let deadArgs := args.args.filter fun arg => !(liveArgs.contains arg)
    let deadIds := deadArgs.map mkIdent

    let counts := countVarOccurences r ctor.type?
    let counts := counts.map fun n =>
                    Syntax.mkApp (mkIdent ``PFin2) #[quote n]

    if deadIds.isEmpty then
      `(matchAltExpr| | $head => (!![ $counts,* ]))
    else
      `(matchAltExpr| | $head $deadIds:ident* => (!![ $counts,* ]))

  let h ← Elab.Term.mkFreshBinderName
  let hIdent := mkIdent h
  let headT := mkIdent headTName
  let deadBinderIdents := Macro.getBinderIdents view.binders.getArgs false
  let deadBinders : TSyntaxArray ``bracketedBinder :=
    view.binders.getArgs.map TSyntax.mk
  let matchTerm ← `(match $hIdent:ident with
    $matchAlts:matchAlt*
  )

  if deadBinderIdents.isEmpty then
    elabCommandAndTrace <|← `(
      def $declId : $headT → $target_type :=
        fun $hIdent:ident => $matchTerm
    )
  else
    elabCommandAndTrace <|← `(
      def $declId $deadBinders:bracketedBinder* : $headT $deadBinderIdents* → $target_type :=
        fun $hIdent:ident => $matchTerm
    )

  pure declName



open Parser.Term in
/--
  Show that the `Shape` type is a qpf, through an isomorphism with the `Shape.P` pfunctor

  CRITICAL FIX: Now handles dead parameters properly by threading them through all definitions
-/
def mkQpf (shapeView : InductiveView) (ctorArgs : Array CtorArgs) (headT P : Ident) (arity : Nat)
    (deadBinders : TSyntaxArray ``Parser.Term.bracketedBinder)
    (deadBinderIdents : Array Term) : CommandElabM Unit := do
  withQPFTraceNode m!"deriving instance of `MvQPF {shapeView.shortDeclName}`"
    (tag := "mkQPF") <| do

  let (shapeN, _) := Elab.expandDeclIdCore shapeView.declId
  let eqv := mkIdent $ Name.mkStr shapeN "equiv"
  let functor := mkIdent $ Name.mkStr shapeN "functor"
  let q := mkIdent $ Name.mkStr shapeN "qpf"
  let shape := mkIdent shapeN

  let ctors := shapeView.ctors.zip ctorArgs

  /-
    `box` maps objects from the curried form, to the internal uncurried form.
    See below, or [.ofPolynomial] for the signature

    Example, using a simple list type
    ```lean4
     fun x => match x with
    | MyList.Shape.nil a b => ⟨MyList.Shape.HeadT.nil, fun i => match i with
        | 0 => Fin2.elim0 (C:=fun _ => _)
        | 1 => fun j => match j with
                | (.ofNat' 0) => b
        | 2 => fun j => match j with
                | (.ofNat' 0) => a
    ⟩
    | MyList.Shape.cons a as => ⟨MyList.Shape.HeadT.cons, fun i j => match i with
        | 0 => match j with
                | .fz => as
        | 1 => Fin2.elim0 (C:=fun _ => _) j
        | 2 => match j with
                | .fz => a
    ```
  -/

  let boxBody ← ctors.mapM fun (ctor, args) => do
    let argsId  := args.args.map mkIdent
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ ctor.declName.replacePrefix shapeView.declName headT.getId
    let liveArgs := ctorLiveArgNames args
    let deadArgs := args.args.filter fun arg => !(liveArgs.contains arg)
    let headTerm : Term ←
      if deadArgs.isEmpty then
        `($headAlt)
      else
        let deadIds := deadArgs.map mkIdent
        `($headAlt $deadIds:ident*)

    `(matchAltExpr| | $alt:ident $argsId:ident* => ⟨$headTerm, fun i => match i with
        $(
          ←args.per_type.enum.mapM fun (i, args) => do
            let i := arity - 1 - i
            let body ← if args.size == 0 then
                          -- `(fun j => Fin2.elim0 (C:=fun _ => _) j)
                          `(PFin2.elim0)
                        else
                          let alts ← args.enum.mapM fun (j, arg) =>
                              let arg := mkIdent arg
                              `(matchAltExpr| | $(PFin2.quoteOfNat j) => $arg)
                          `(
                            fun j => match j with
                              $alts:matchAlt*
                          )
            `(matchAltExpr| | $(Fin2.quoteOfNat i) => $body)
        ):matchAlt*
    ⟩)
  let box ← `(
    fun x => match x with
      $boxBody:matchAlt*
  )

  /-
    `unbox` does the opposite of `box`; it maps from uncurried to curried

    fun ⟨head, child⟩ => match head with
    | MyList.Shape.HeadT.nil  => MyList.Shape.nil (child 2 .fz) (child 1 .fz)
    | MyList.Shape.HeadT.cons => MyList.Shape.cons (child 2 .fz) (child 0 .fz)
  -/

  /- the `child` variable in the example above -/
  let unbox_child := mkIdent <|<- Elab.Term.mkFreshBinderName;
  let unboxBody ← ctors.mapM fun (ctor, args) => do
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ ctor.declName.replacePrefix shapeView.declName headT.getId
    let liveArgs := ctorLiveArgNames args
    let deadArgs := args.args.filter fun arg => !(liveArgs.contains arg)
    let deadIds := deadArgs.map mkIdent

    let args : Array Term ← args.args.mapM fun arg => do
      if liveArgs.contains arg then
        -- find the pair `(i, j)` such that the argument is the `j`-th occurence of the `i`-th type
        let (i, j) := (args.per_type.enum.map fun (i, t) =>
          -- the order of types is reversed, since `TypeVec`s count right-to-left
          let i := arity - 1 - i
          ((t.idxOf? arg).map fun j => (i, j)).toList
        ).toList.flatten[0]!
        `($unbox_child $(Fin2.quoteOfNat i) $(PFin2.quoteOfNat j))
      else
        pure (mkIdent arg)

    let body := Syntax.mkApp alt args

    if deadIds.isEmpty then
      `(matchAltExpr| | $headAlt:ident => $body)
    else
      `(matchAltExpr| | $headAlt:ident $deadIds:ident* => $body)

  let unbox ← `(
    fun ⟨head, $unbox_child⟩ => match head with
        $unboxBody:matchAlt*
  )

  -- CRITICAL FIX: Thread dead parameters through equiv, functor, qpf definitions
  let header := m!"showing that {shapeView.declName} is equivalent to a polynomial functor …"

  if deadBinderIdents.isEmpty then
    -- No dead parameters - use original code
    elabCommandAndTrace (header := header) <|← `(
      def $eqv:ident {Γ} : (@TypeFun.ofCurried $(quote arity) $shape) Γ ≃ ($P).Obj Γ where
        toFun     := $box
        invFun    := $unbox
        left_inv  := by
          simp only [Function.LeftInverse]
          intro x
          cases x
          <;> rfl
        right_inv := by
          simp only [Function.RightInverse, Function.LeftInverse]
          intro x
          rcases x with ⟨head, child⟩;
          cases head
          <;> simp
          <;> apply congrArg
          <;> (funext i; fin_cases i)
          <;> (funext (j : PFin2 _); fin_cases j)
          <;> rfl
    )
    elabCommandAndTrace (header := "defining {functor}") <|← `(
      instance $functor:ident : MvFunctor (@TypeFun.ofCurried $(quote arity) $shape) where
        map f x   := ($eqv).invFun <| ($P).map f <| ($eqv).toFun <| x
    )
    elabCommandAndTrace (header := "defining {q}") <|← `(
      instance $q:ident : MvQPF (@TypeFun.ofCurried $(quote arity) $shape) :=
        .ofEquiv (fun _ => $eqv)
    )
  else
    -- With dead parameters - parameterize all definitions
    elabCommandAndTrace (header := header) <|← `(
      def $eqv:ident $deadBinders:bracketedBinder* {Γ} : (@TypeFun.ofCurried $(quote arity) ($shape $deadBinderIdents*)) Γ ≃ (($P $deadBinderIdents*)).Obj Γ where
        toFun     := $box
        invFun    := $unbox
        left_inv  := by
          simp only [Function.LeftInverse]
          intro x
          cases x
          <;> rfl
        right_inv := by
          simp only [Function.RightInverse, Function.LeftInverse]
          intro x
          rcases x with ⟨head, child⟩;
          cases head
          <;> simp
          <;> apply congrArg
          <;> (funext i; fin_cases i)
          <;> (funext (j : PFin2 _); fin_cases j)
          <;> rfl
    )
    elabCommandAndTrace (header := "defining {functor}") <|← `(
      instance $functor:ident $deadBinders:bracketedBinder* : MvFunctor (@TypeFun.ofCurried $(quote arity) ($shape $deadBinderIdents*)) where
        map f x   := ($eqv $deadBinderIdents*).invFun <| ($P $deadBinderIdents*).map f <| ($eqv $deadBinderIdents*).toFun <| x
    )
    elabCommandAndTrace (header := "defining {q}") <|← `(
      instance $q:ident $deadBinders:bracketedBinder* : MvQPF (@TypeFun.ofCurried $(quote arity) ($shape $deadBinderIdents*)) :=
        .ofEquiv (fun _ => $eqv $deadBinderIdents*)
    )

/-! ## mkShape -/

structure MkShapeResult where
  (r : Replace)
  (shape : Name)
  (shapeApplied : Option Name)
  (P : Name)
  (effects : CommandElabM Unit)

open Parser Parser.Term in
def mkShape (view : DataView) : TermElabM MkShapeResult := do
  -- If the original declId was `MyType`, we want to register the shape type under `MyType.Shape`
  let (declName, declId, shortDeclName) ← addSuffixToDeclId view.declId "Shape"

  withQPFTraceNode m!"defining `{declName}`" (tag := "mkShape") <| do


  -- Extract the "shape" functors constructors
  let shapeIdent  := mkIdent shortDeclName
  let ((ctors, ctorArgs), r) ← Replace.shapeOfCtors view shapeIdent
  let ctors := ctors.map (CtorView.declReplacePrefix view.declName declName)

  trace[QPF] "r.getBinders = {←r.getBinders}"
  trace[QPF] "r.vars = {r.vars}"
  trace[QPF] "r.expr = {r.expr}"
  trace[QPF] "r.newParameters.size = {r.newParameters.size}"
  trace[QPF] "r.arity = {r.arity}"
  trace[QPF] "view.deadBinders = {view.deadBinders}"
  trace[QPF] "view.liveBinders = {view.liveBinders}"
  trace[QPF] "view.liveBinders.size = {view.liveBinders.size}"

  -- Assemble it back together, into the shape inductive type
  let liveBinders ← r.getBinders
  let deadBinders := view.deadBinders

  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }

  -- Use a regular inductive, and generate a wrapper for dead parameters
  -- Shape binders are: dead params (if any), followed by all live parameters (from replacement)
  let binders :=
    if deadBinders.isEmpty then
      view.binders.setArgs #[liveBinders.raw]
    else
      view.binders.setArgs (deadBinders.raw.push liveBinders.raw)

  -- Universe polymorphic Shape: preserve levelNames from the original view
  let shapeView : InductiveView := { view with
    ctors, declId, declName, shortDeclName, modifiers, binders,
    type? := none,
    levelNames      := view.levelNames
    computedFields  := #[]
    isClass := false
    allowIndices := false
    allowSortPolymorphism := false
    docString? := none
    : InductiveView
  }

  withQPFTraceNode "shape view …" <| do
    trace[QPF] m!"{shapeView}"
  let PName := Name.mkStr declName "P"
  -- Optional wrapper to fix dead parameters and expose a CurriedTypeFun
  let shapeAppliedName :=
    if view.deadBinders.isEmpty then
      none
    else
      some (Name.mkStr declName "Applied")
  return ⟨r, declName, shapeAppliedName, PName, do
    withQPFTraceNode "mkShape effects" <| do

    runTermElabM (elabInductiveView · shapeView)

    -- HeadT and ChildT should ONLY have dead parameters, not live parameters
    -- Create a view with only dead binders for HeadT/ChildT
    let deadOnlyBinders := shapeView.binders.setArgs deadBinders.raw
    let viewDeadOnly := { shapeView with binders := deadOnlyBinders }

    let headTName ← mkHeadT viewDeadOnly ctorArgs
    let childTName ← mkChildT viewDeadOnly r headTName ctorArgs

    let headTId := mkIdent headTName
    let childTId := mkIdent childTName

    -- P should be parameterized by dead variables only
    let deadBinderIdents := Macro.getBinderIdents viewDeadOnly.binders.getArgs false
    let pfType ←
      runTermElabM fun _ => do
        let resultLevel := computeResultUniverse shapeView.levelNames
        let tp := mkApp (mkConst ``MvPFunctor [resultLevel]) (mkNatLit r.arity)
        delab tp

    -- Universe polymorphic P: include universe parameters from the original view
    -- P is now parameterized by dead variables
    let deadBinders : TSyntaxArray ``Parser.Term.bracketedBinder :=
      viewDeadOnly.binders.getArgs.map TSyntax.mk
    let PId := mkIdent PName
    let PDeclId := mkNode ``Command.declId #[PId, mkNullNode]

    if deadBinderIdents.isEmpty then
      elabCommandAndTrace <|← `(
        def $PDeclId:declId : $pfType :=
          (@MvPFunctor.mk (n := $(quote r.arity)) $headTId $childTId)
      )
    else
      elabCommandAndTrace <|← `(
        def $PDeclId:declId $deadBinders:bracketedBinder* : $pfType :=
          (@MvPFunctor.mk (n := $(quote r.arity)) ($headTId $deadBinderIdents*) ($childTId $deadBinderIdents*))
      )

    -- Wrapper for dead parameters: Shape.Applied : CurriedTypeFun arity
    if let some shapeApplied := shapeAppliedName then
      let shapeAppliedId := mkIdent shapeApplied
      let shapeId := mkIdent declName
      let liveBinderIdents := r.getBinderIdents
      let liveBinderTerms := Macro.getBinderIdents #[liveBinders.raw] false
      let body := Syntax.mkApp shapeId (deadBinderIdents ++ liveBinderTerms)
      let body ← liveBinderIdents.reverse.foldlM (init := (body : Term)) fun acc ident => do
        `((fun ($ident : Type _) => $acc))
      elabCommandAndTrace <|← `(
        def $shapeAppliedId:ident $view.deadBinders:bracketedBinder* :
            CurriedTypeFun $(quote r.arity) :=
          $body
      )

    -- Use r.arity (live parameters only), not r.expr.size (all parameters)
    mkQpf shapeView ctorArgs headTId PId r.arity view.deadBinders deadBinderIdents

    -- Bridge instance for Shape.Applied so the composition pipeline can find MvQPF
    if let some shapeApplied := shapeAppliedName then
      let shapeAppliedId := mkIdent shapeApplied
      let shapeId := mkIdent declName
      let appliedQpfName := Name.mkStr shapeApplied "qpf"
      let appliedQpfId := mkIdent appliedQpfName
      elabCommandAndTrace <|← `(
        instance $appliedQpfId:ident $view.deadBinders:bracketedBinder* :
            MvQPF (@TypeFun.ofCurried $(quote r.arity) ($shapeAppliedId $deadBinderIdents*)) := by
          simpa using (by infer_instance :
            MvQPF (@TypeFun.ofCurried $(quote r.arity) ($shapeId $deadBinderIdents*)))
      )
  ⟩

/--
  Take either the fixpoint or cofixpoint of `base` to produce an `Internal` uncurried QPF,
  and define the desired type as the curried version of `Internal`
-/
def mkType (view : DataView) (base : Term × Term) : CommandElabM Unit :=
  withQPFTraceNode m!"defining (co)datatype {view.declId}" (tag := "mkType") <| do

  let uncurriedIdent ← addSuffixToDeclIdent view.declId "Uncurried"
  let baseIdExt ← addSuffixToDeclIdent view.declId "Base"
  let baseIdent ← addSuffixToDeclIdent baseIdExt "Uncurried"
  let baseQPFIdent ← addSuffixToDeclIdent baseIdent "instQPF"

  let deadBinderNamedArgs ← view.deadBinderNames.mapM fun n =>
        `(namedArgument| ($n:ident := $n:term))
  let uncurriedApplied ← `($uncurriedIdent:ident $deadBinderNamedArgs:namedArgument*)
  let baseApplied ← `($baseIdent:ident $deadBinderNamedArgs:namedArgument*)

  let arity := view.liveBinders.size
  let fix_or_cofix := DataCommand.fixOrCofix view.command

  let ⟨base, q⟩ := base
  elabCommandAndTrace
    (header := m!"elaborating uncurried base functor {baseIdent} …") <|← `(
      abbrev $baseIdent:ident $view.deadBinders:bracketedBinder* :
          TypeFun $(quote <| arity + 1) :=
        $base
  )

  elabCommandAndTrace
    (header := m!"elaborating *curried* base functor {baseIdExt} …") <|← `(
      abbrev $baseIdExt $view.deadBinders:bracketedBinder* :=
        TypeFun.curried $baseApplied
  )

  elabCommandAndTrace
    (header := m!"elaborating qpf instance for {baseIdent} …") <|← `(
      instance $baseQPFIdent:ident : MvQPF ($baseApplied) := $q
  )

  elabCommandAndTrace
    (header := m!"elaborating uncurried (co)fixpoint {uncurriedIdent} …") <|← `(
      abbrev $uncurriedIdent:ident $view.deadBinders:bracketedBinder* :
          TypeFun $(quote arity) :=
        $fix_or_cofix $base
  )

  elabCommandAndTrace
    (header := m!"elaborating *curried* (co)fixpoint {view.declId} …")  <|← `(
      abbrev $(view.declId) $view.deadBinders:bracketedBinder* :=
        TypeFun.curried $uncurriedApplied
  )

open Macro Comp in
/--
  Top-level elaboration for both `data` and `codata` declarations
-/
@[command_elab declaration]
def elabData : CommandElab := fun stx =>
  withQPFTraceNode "elabData" (tag := "elabData") (collapsed := false) <| do

  let modifiers ← elabModifiers ⟨stx[0]⟩
  let decl := stx[1]

  let view ← dataSyntaxToView modifiers decl
  let view ← preProcessCtors view -- Transforms binders into simple lambda types

  let (nonRecView, ⟨r, shape, shapeApplied, _P, eff⟩) ← runTermElabM fun _ => do
    let (nonRecView, _rho) ← makeNonRecursive view;
    pure (nonRecView, ←mkShape nonRecView)

  /- Execute the `ComandElabM` side-effects prescribed by `mkShape` -/
  let _ ← eff

  /- Composition pipeline -/
  -- Build the target application:
  -- - If we have dead params: Shape.Applied dead_params live_params
  -- - If no dead params: Shape live_params (regular inductive)
  let target ←
    if view.deadBinderNames.isEmpty then
      -- No dead params: just apply live parameters
      `($(mkIdent shape):ident $r.expr:term*)
    else
      -- Have dead params: apply dead params first, then live params
      let deadParamTerms ← view.deadBinderNames.mapM fun n => `($n:ident)
      let shapeBase := mkIdent <| shapeApplied.getD shape
      let shapeWithDeadParams ← deadParamTerms.foldlM
        (fun acc param => `($acc $param))
        shapeBase
      r.expr.foldlM
        (fun acc param => `($acc $param))
        shapeWithDeadParams

  let base ← elabQpfCompositionBody {
    liveBinders := nonRecView.liveBinders,
    deadBinders := nonRecView.deadBinders,
    type?   := none,
    target  := target
  }

  mkType view base
  mkConstructors view shape r

  if let .Data := view.command then
    try genRecursors view
    catch e =>
      trace[QPF] m!"Failed to generate recursors.\
        \n\n{e.toMessageData}"


end Data.Command
