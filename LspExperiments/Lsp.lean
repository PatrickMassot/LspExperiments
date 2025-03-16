import Lean

open Lean Server Lsp FileWorker RequestM

/-- Is this the `SyntaxNodeKind` of a tactic syntax? Currently a very crude heuristic. -/
def Lean.SyntaxNodeKind.isTactic (kind : SyntaxNodeKind) : Bool :=
  Name.isPrefixOf `Lean.Parser.Tactic kind

/-- In the given syntax stack, find the first item satisfying the condition `cond`
and run `code` on it. Return `none` if no such item exists.  -/
def Lean.Syntax.Stack.find? (stack : Syntax.Stack) (cond : Lean.Syntax → Bool) {m : Type → Type} [Monad m] {α : Type}
    (code : Lean.Syntax → m (Option α)) : m (Option α) := do
  for (stx, _) in stack do
    if cond stx then
      return ← code stx
  return none

/-- `mkRpxAtMethod cond run` is a server rpc method that searches for a
`Syntax` satisfying `cond` among the parents of the `Syntax` at current cursor position,
and then run the `run` function on that syntax and the current document filemap. -/
def mkRpcAtMethod {α : Type} [RpcEncodable α] [Inhabited α]
    (cond : Lean.Syntax → Bool) (run : Syntax → FileMap → Option α) (params : TextDocumentPositionParams) :
    RequestM (RequestTask <| Option α) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  let hoverPos := filemap.lspPosToUtf8Pos params.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos) (notFoundX := pure none) fun snap => do
  let some stack := snap.stx.findStack? (·.getRange?.any (·.contains hoverPos)) | return none
  stack.find? cond fun stx ↦ return run stx filemap


/-- `mkRpcRangeAtMethod cond` is a the server rpc method that
searches for a `Syntax` satisfying `cond` among the parents of the `Syntax` at
current cursor position, and return the range of this syntax.
-/
def mkRpcRangeAtMethod (cond : Lean.Syntax → Bool) :
    TextDocumentPositionParams → RequestM (RequestTask (Option (Option Range))) :=
  mkRpcAtMethod cond fun stx map ↦ return stx.getRange?.map fun rg ↦ rg.toLspRange map

/-- Returns the range of the syntax containing the current cursor position. -/
@[server_rpc_method]
def rpcSyntaxAt := mkRpcRangeAtMethod (fun _ ↦ true)

/-- Debuging function for the next function attempt. -/
@[server_rpc_method]
def rpcSyntaxStackAround (params : Range) :
    RequestM (RequestTask (Option (Option String))) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  let startPos := filemap.lspPosToUtf8Pos params.start
  let endPos := filemap.lspPosToUtf8Pos params.end
  withWaitFindSnap doc (fun s => s.endPos > endPos) (notFoundX := pure none) fun snap => do
  let some stack := snap.stx.findStack? (·.getRange?.any (·.contains endPos)) | return none
  let mut res := s!"Params:\nStart: {params.start}\nEns: {params.end}"
  for (stx, i) in stack do
    let some rg := stx.getRange? | continue
    res := s!"\n\n{res}\n\nIndex {i}\n{stx.getKind}\n{stx}\n{repr <| rg.toLspRange filemap}"
  return some res

/-- Wrong attempt at returning the range of the parent syntax. -/
@[server_rpc_method]
def rpcSyntaxAround (params : Range) :
    RequestM (RequestTask (Option (Option Range))) := do
  let doc ← readDoc
  let filemap := doc.meta.text
  let startPos := filemap.lspPosToUtf8Pos params.start
  let endPos := filemap.lspPosToUtf8Pos params.end
  withWaitFindSnap doc (fun s => s.endPos > endPos) (notFoundX := pure none) fun snap => do
  let some stack := snap.stx.findStack? (·.getRange?.any (·.contains endPos)) | return none
  for (stx, _) in stack do
    let some rg := stx.getRange? | continue
    let lrg := rg.toLspRange filemap
    if lrg.start < params.start || lrg.end > params.end then
      return lrg
  return none

/-- Returns the range of the declaration containing the current cursor position. -/
@[server_rpc_method]
def rpcDeclarationRangeAt := mkRpcRangeAtMethod (·.getKind = `Lean.Parser.Command.declaration)

/-- Returns the range of the tactic containing the current cursor position. -/
@[server_rpc_method]
def rpcTacticRangeAt := mkRpcRangeAtMethod (·.getKind.isTactic)

/-- Returns the range of the tactic sequence containing the current cursor position. -/
@[server_rpc_method]
def rpcTacticSeqRangeAt := mkRpcRangeAtMethod (·.getKind = `Lean.Parser.Tactic.tacticSeq)


/-- Returns the range of the binder containing the current cursor position, and the kind
of this binder. -/
@[server_rpc_method]
def rpcBinderRangeAt :=
  mkRpcAtMethod (·.getKind ∈ [`Lean.Parser.Term.explicitBinder,`Lean.Parser.Term.implicitBinder]) fun stx map ↦ return stx.getRange?.map fun rg ↦ (stx.getKind, rg.toLspRange map)


deriving instance Repr for Lsp.Position
deriving instance Repr for Lsp.Range

/-- Server rpc methode returning the syntax stack at the current cursor position.
For debugging purposes. -/
@[server_rpc_method]
def syntaxStack  (p : TextDocumentPositionParams ) :
    RequestM (RequestTask <| Option String) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos) (notFoundX := pure "No snapshot found") fun snap => do
  let some stack := snap.stx.findStack? (·.getRange?.any (·.contains hoverPos)) | return s!"No syntax stack found from snap syntax\n{snap.stx}"
  let mut res := ""
  for (stx, _) in stack do
    let some rg := stx.getRange? | continue
    res := s!"{res}\n\n{stx.getKind}\n{stx}\n{repr <| rg.toLspRange text}"
  return some res

