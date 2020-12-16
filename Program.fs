// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp

open System
open System.IO
open System.Diagnostics
open FStar.Parser
open FStar.Range

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

let filterMap f l =
    let rec aux res =
        function
        | [] -> res
        | x :: xs ->
            match f x with
            | None -> aux res xs
            | Some v -> aux (v :: res) xs

    aux [] l

type Z3rlimitUse =
    { pushOpt: string list
      initialZ3rlimit: int
      z3rlimitIdx: int
      pushOptRange: FStar.Range.range
      affectedIds: string list }

let rec collectZ3rlimitUses (decls: AST.decl list) modName res =
    match decls with
    | [] -> res
    | decl :: rest ->
        match decl.d with
        | AST.TopLevelModule id -> collectZ3rlimitUses rest (FStar.Ident.string_of_lid id) res
        | AST.Pragma pr ->
            match pr with
            | AST.PushOptions opt ->
                match opt with
                | None -> failwith "yo"
                | Some src ->
                    let opts =
                        src.Split ' '
                        |> List.ofArray
                        |> List.map (fun s -> s.Trim())

                    match List.tryFindIndex (fun s -> s = "--z3rlimit") opts with
                    | None -> collectZ3rlimitUses rest modName res
                    | Some i ->
                        let range = decl.drange
                        let rlimit = int <| List.nth opts (i + 1)

                        let ids =
                            match rest with
                            | { d = AST.Val (id, _) } :: _ -> Some [ FStar.Ident.string_of_id id ]
                            | { d = AST.TopLevelLet (_, l) } :: _ ->
                                Some
                                <| filterMap (fun (p: AST.pattern, _) ->
                                    match p.pat with
                                    | AST.PatApp ({ pat = AST.PatVar (id, _) }, _) -> Some(FStar.Ident.string_of_id id)
                                    | _ -> None) l
                            | _ -> None

                        match ids with
                        | None
                        | Some [] -> collectZ3rlimitUses rest modName res
                        | Some ids ->
                            let newEntry =
                                { pushOpt = opts
                                  initialZ3rlimit = rlimit
                                  z3rlimitIdx = i + 1
                                  pushOptRange = range
                                  affectedIds = List.map (fun id -> sprintf "%s.%s" modName id) ids }

                            collectZ3rlimitUses rest modName (newEntry :: res)
            | _ -> collectZ3rlimitUses rest modName res
        | _ -> collectZ3rlimitUses rest modName res

(*
let collectPushOptionsZ3rlimit (decl: AST.decl) =
    match decl.d with
    | AST.Pragma pr ->
        match pr with
        | AST.PushOptions opt ->
            match opt with
            | Some src ->
                let opts =
                    src.Split ' '
                    |> List.ofArray
                    |> List.map (fun s -> s.Trim())

                match List.tryFindIndex (fun s -> s = "--z3rlimit") opts with
                | Some i ->
                    let range = decl.drange
                    let rlimit = int <| List.nth opts (i + 1)
                    Some(opts, i + 1, rlimit, range)
                | None -> None
            | None -> None
        | _ -> None
    | _ -> None
*)

// (rlimitBg, rlimitEnd]
let rec searchBestZ3rlimit u rlimitBg rlimitEnd =
    let fileName = FStar.Range.file_of_range u.pushOptRange

    let wd =
        Path.GetDirectoryName(Path.GetFullPath(fileName))

    let rewriteZ3rlimit newRlimit =
        let newOptions =
            u.pushOpt
            |> List.mapi (fun i opt -> if i = u.z3rlimitIdx then string newRlimit else opt)
            |> Array.ofList
            |> String.concat " "

        let newLine =
            sprintf "#push-options \"%s\"" newOptions

        let lineno =
            (u.pushOptRange |> start_of_range |> line_of_pos)
            - 1

        eprintfn "### Rewriting %s(%d)" fileName lineno
        eprintfn "### \t\"%s\" => \"%s\"" (String.concat " " u.pushOpt) newOptions

        let lines =
            File.ReadAllLines(fileName)
            |> Array.mapi (fun i line -> if i = lineno then newLine else line)

        use file = new StreamWriter(fileName)
        Array.iter (fun (l: string) -> file.WriteLine(l)) lines

    let runFStar admitExcept =
        let pi =
            new ProcessStartInfo(FileName = "fstar.exe", WorkingDirectory = wd)

        pi.ArgumentList.Add("--z3refresh")
        pi.ArgumentList.Add("--query_stats")
        pi.ArgumentList.Add("--admit_except")
        pi.ArgumentList.Add(admitExcept)
        pi.ArgumentList.Add(Path.GetFileName(fileName))

        use fstar = Process.Start(pi)
        eprintfn "### Running F* for %s" admitExcept
        fstar.WaitForExit()
        fstar.ExitCode

    if rlimitEnd - rlimitBg <= 1 then
        rewriteZ3rlimit rlimitEnd
    else
        let newRlimit = rlimitBg + (rlimitEnd - rlimitBg) / 2
        rewriteZ3rlimit newRlimit

        let ok =
            List.forall (fun id -> runFStar id = 0) u.affectedIds

        if ok then
            eprintfn "### \tOK"
            searchBestZ3rlimit u rlimitBg newRlimit
        else
            eprintfn "### \tNG"
            searchBestZ3rlimit u newRlimit rlimitEnd

[<EntryPoint>]
let main argv =
    try
        let filename = argv.[0]
        let ast, _ = FStar.Parser.Driver.parse_file filename

        match ast with
        | AST.Interface _ -> failwith "yep"
        | AST.Module (id, lst) ->
            collectZ3rlimitUses lst "" []
            |> List.iter (fun u -> searchBestZ3rlimit u (-1) u.initialZ3rlimit)
    with err -> printfn "%A" err

    0 // return an integer exit code