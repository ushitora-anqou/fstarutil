module RewriteZ3rlimit

open System
open System.IO
open System.Diagnostics
open FStar.Parser
open FStar.Range

type CalcMethodOfBestZ3rlimit =
    | Min
    | Multiple of int

let calcBestZ3rlimit mthd min =
    match mthd with
    | Min -> min
    | Multiple n -> (min / n + 1) * n

type Options =
    { calcMethod: CalcMethodOfBestZ3rlimit }

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

// (rlimitBg, rlimitEnd]
let rec searchBestZ3rlimit u calcBest rlimitBg rlimitEnd =
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

    if rlimitEnd - rlimitBg <= 1
       || calcBest (rlimitBg + 1) = calcBest rlimitEnd then
        let best = calcBest rlimitEnd
        eprintfn "### Best rlimit is %d" best
        rewriteZ3rlimit (calcBest rlimitEnd)
    else
        let newRlimit = rlimitBg + (rlimitEnd - rlimitBg) / 2
        rewriteZ3rlimit newRlimit

        let ok =
            List.forall (fun id -> runFStar id = 0) u.affectedIds

        if ok then
            eprintfn "### \tOK"
            searchBestZ3rlimit u calcBest rlimitBg newRlimit
        else
            eprintfn "### \tNG"
            searchBestZ3rlimit u calcBest newRlimit rlimitEnd

let doRewrite (opts: Options) filename =
    let ast, _ = FStar.Parser.Driver.parse_file filename

    match ast with
    | AST.Interface _ -> failwith "Unexpected AST.Interface"
    | AST.Module (_, decls) ->
        let uses = collectZ3rlimitUses decls "" []
        let calcBest = calcBestZ3rlimit opts.calcMethod
        List.iter (fun u -> searchBestZ3rlimit u calcBest (-1) u.initialZ3rlimit) uses
