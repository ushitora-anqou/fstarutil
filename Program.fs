// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp

open System
open System.IO
open System.Diagnostics
open FStar.Parser
open FStar.Range
open CommandLine

(*
type callgraph =
    { funnames: list<string>
      uses: Map<string, string list> }

let rec createCGDecl (cg: callgraph) (decl: AST.decl) =
    match decl.d with
    | AST.TopLevelLet (_, l) ->
        List.fold (fun cg (pat: AST.pattern, tm: AST.term) ->
            match pat.pat with
            | AST.PatVar (id, _) -> createCGTerm (FStar.Ident.string_of_id id) cg tm
            | _ -> cg) cg l

and createCGTerm (toplevel: string) (cg: callgraph) (tm: AST.term) =
    match tm.tm with
    | AST.Op (_, l) -> List.fold (fun cg tm -> createCGTerm toplevel cg tm) cg l
    | AST.Var id ->
        let id = FStar.Ident.string_of_lid id

        { cg with
              uses =
                  Map.change toplevel (function
                      | None -> Some([ id ])
                      | Some l -> Some(id :: l)) cg.uses }
    | AST.Construct (id, l) -> List.fold (fun cg (tm, _) -> createCGTerm toplevel cg tm) cg l
    | AST.Abs (_, tm) -> createCGTerm toplevel cg tm
    | AST.App (lhs, rhs, _) ->
        let cg = createCGTerm toplevel cg lhs
        createCGTerm toplevel cg rhs
    | AST.Let (_, l, tm) ->
        let cg =
            List.fold (fun cg (_, (_, tm)) -> createCGTerm toplevel cg tm) cg l

        createCGTerm toplevel cg tm
    | AST.LetOpen (_, tm) -> createCGTerm toplevel cg tm
    | AST.Seq (lhs, rhs) ->
        let cg = createCGTerm toplevel cg lhs
        createCGTerm toplevel cg rhs
    | AST.Bind (_, lhs, rhs) ->
        let cg = createCGTerm toplevel cg lhs
        createCGTerm toplevel cg rhs
    | AST.If (cond, thn, els) ->
        let cg = createCGTerm toplevel cg cond
        let cg = createCGTerm toplevel cg thn
        createCGTerm toplevel cg els
    | AST.Match (cond, branches) ->
        let cg = createCGTerm toplevel cg cond

        List.fold (fun cg branch ->
            match branch with
            | (_, Some lhs, rhs) ->
                let cg = createCGTerm toplevel cg lhs
                createCGTerm toplevel cg rhs
            | (_, None, rhs) -> createCGTerm toplevel cg rhs) cg branches
    | _ -> cg
*)

[<Verb("callgraph", HelpText = "Print callgraph.")>]
type CallgraphCLI = { dummy: bool }

[<Verb("rewrite-z3rlimit", HelpText = "Add file contents to the index.")>]
type RewriteZ3rlimitCLI =
    { [<Option("min", HelpText = "Use minimum possible z3rlimit.")>]
      min: bool
      [<Option('x', HelpText = "Use possible z3rlimit multiple of arg.")>]
      mult: int option
      [<Option(HelpText = "Prints all messages to standard output.")>]
      verbose: bool
      [<Value(0, MetaName = "filename", HelpText = "File path to read.")>]
      fileName: string }


[<EntryPoint>]
let main args =
    try
        let result =
            Parser.Default.ParseArguments<CallgraphCLI, RewriteZ3rlimitCLI> args

        match result with
        | :? (CommandLine.Parsed<obj>) as command ->
            match command.Value with
            | :? CallgraphCLI as opts -> 0
            | :? RewriteZ3rlimitCLI as opts ->
                let calcMethod = RewriteZ3rlimit.Multiple 20

                let calcMethod =
                    if opts.min then
                        RewriteZ3rlimit.Min
                    else
                        match opts.mult with
                        | Some n -> RewriteZ3rlimit.Multiple n
                        | None -> calcMethod

                RewriteZ3rlimit.doRewrite ({ calcMethod = calcMethod }) opts.fileName
                0

        | :? (CommandLine.NotParsed<obj>) as command ->
            match Seq.item 0 command.Errors with
            | :? VersionRequestedError
            | :? HelpRequestedError -> 0
            | _ -> failwith "Invalid command-line arguments"
    with err ->
        eprintfn "%A" err
        1