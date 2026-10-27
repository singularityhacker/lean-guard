import Lean.Data.Json
import Guard.Core
import Guard.Parse

/-!
# The Claude Code hook (trusted, IO)

Reads one `PreToolUse` event on stdin, turns it into an `Action`, runs
`step` against the session's saved state, and answers:

* `allow` → print nothing, so Claude Code's own permission rules still
  apply. The guard can only ever *restrict*.
* `ask` / `deny` → a `permissionDecision` JSON object.

Any error is raised to `main`, which exits with code 2 (block).
-/

namespace Guard.Hook

open Lean (Json ToJson FromJson toJson fromJson?)

/-! ## Paths, with symlinks resolved -/

/-- Resolve against `cwd`, then canonicalize the longest existing prefix
    with `realpath`, so a symlink inside the workspace that points outside
    resolves to where it really goes. Refuses dangling symlinks, which a
    write would follow to a target we cannot see. -/
def resolveReal (cwd : Path) (raw : String) : IO Path := do
  let lex := resolve cwd raw
  for k in (List.range (lex.length + 1)).reverse do
    let pre : Path := lex.take k
    if let .ok real ← (IO.FS.realPath pre.render).toBaseIO then
      let real : Path := resolve [] real.toString
      if h : k < lex.length then
        let next : Path := real ++ [lex[k]]
        if (← (System.FilePath.symlinkMetadata next.render).toBaseIO) matches .ok _ then
          throw (IO.userError s!"{next.render} exists but cannot be resolved (dangling symlink?)")
      return real ++ lex.drop k
  return lex

/-! ## Raw tool call → `Action` -/

private def str? (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

private def need (j : Json) (k : String) : IO String :=
  match str? j k with
  | some v => pure v
  | none => throw (IO.userError s!"missing `{k}`")

def toActionCore (cwd : Path) (tool : String) (input : Json) : IO Action := do
  match tool with
  | "Read" => return .read (← resolveReal cwd (← need input "file_path"))
  | "Write" | "Edit" | "MultiEdit" => return .write (← resolveReal cwd (← need input "file_path"))
  | "NotebookEdit" => return .write (← resolveReal cwd (← need input "notebook_path"))
  | "Grep" | "LS" => return .read (← resolveReal cwd ((str? input "path").getD "."))
  | "Glob" =>
    let base ← resolveReal cwd ((str? input "path").getD ".")
    match Parse.globBase (← need input "pattern") with
    | some lit => return .read (← resolveReal base lit)
    | none => return .malformed tool "`..` after a wildcard in the glob pattern"
  | "Bash" =>
    match Parse.tokenize (← need input "command") with
    | .error why => return .malformed tool why
    | .ok argv =>
      let paths ← (Parse.pathCandidates argv.tail).mapM (resolveReal cwd)
      return .exec cwd argv paths
  | "WebFetch" =>
    match Parse.hostOf (← need input "url") with
    | some host => return .fetch host
    | none => return .malformed tool "not an http(s) URL"
  | other => return .tool other

/-- Never throws: anything unexpected becomes `malformed`, which the
    theorems guarantee is never allowed. -/
def toAction (cwd : Path) (tool : String) (input : Json) : IO Action := do
  try toActionCore cwd tool input
  catch e => return .malformed tool (toString e)

/-! ## Policy file -/

def policyKeys : List String :=
  ["workspace", "readRoots", "allowedPrograms", "egressPrograms", "egressGitSubcommands",
   "opaquePrograms", "allowEgressExec", "allowedHosts", "allowedTools", "localTools",
   "denyPaths", "denyPrograms", "denyTools", "denyHosts", "secretNames", "secretPrefixes",
   "secretSuffixes", "budget"]

/-- Load a policy. Relative paths are relative to the policy file. Unknown
    keys are an error: a typo in a security policy must not be ignored. -/
def loadPolicy (file : System.FilePath) : IO Policy := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let .obj kvs := j | throw (IO.userError "policy must be a JSON object")
  for (k, _) in kvs.toArray do
    unless policyKeys.contains k do throw (IO.userError s!"unknown policy key `{k}`")
  let dir ← IO.FS.realPath (file.parent.getD ".")
  let dirP := resolve [] dir.toString
  let get {α} [FromJson α] (k : String) (dflt : α) : IO α :=
    match j.getObjVal? k with
    | .error _ => pure dflt
    | .ok v => IO.ofExcept ((fromJson? v : Except String α).mapError (s!"policy `{k}`: " ++ ·))
  let paths (k : String) : IO (List Path) := do (← get k ([] : List String)).mapM (resolveReal dirP)
  let ws ← resolveReal dirP (← IO.ofExcept (j.getObjValAs? String "workspace"))
  let d : Policy := { workspace := ws }
  return { d with
    readRoots := ← paths "readRoots"
    allowedPrograms := ← get "allowedPrograms" d.allowedPrograms
    egressPrograms := ← get "egressPrograms" d.egressPrograms
    egressGitSubcommands := ← get "egressGitSubcommands" d.egressGitSubcommands
    opaquePrograms := ← get "opaquePrograms" d.opaquePrograms
    allowEgressExec := ← get "allowEgressExec" d.allowEgressExec
    allowedHosts := (← get "allowedHosts" d.allowedHosts).map (·.toLower)
    allowedTools := ← get "allowedTools" d.allowedTools
    localTools := ← get "localTools" d.localTools
    denyPaths := ← paths "denyPaths"
    denyPrograms := ← get "denyPrograms" d.denyPrograms
    denyTools := ← get "denyTools" d.denyTools
    denyHosts := (← get "denyHosts" d.denyHosts).map (·.toLower)
    secretNames := ← get "secretNames" d.secretNames
    secretPrefixes := ← get "secretPrefixes" d.secretPrefixes
    secretSuffixes := ← get "secretSuffixes" d.secretSuffixes
    budget := ← get "budget" d.budget }

/-! ## Session state -/

def stateToJson (s : State) : Json := Json.mkObj [("tainted", toJson s.tainted), ("used", toJson s.used)]

def stateOfJson (j : Json) : Except String State := do
  return { tainted := ← j.getObjValAs? Bool "tainted", used := ← j.getObjValAs? Nat "used" }

/-- Session ids become file names, so only allow a safe alphabet. -/
def safeSessionId (s : String) : IO String := do
  if s.isEmpty || s.length > 128 || !s.toList.all (fun c => c.isAlphanum || c == '-' || c == '_') then
    throw (IO.userError "unexpected session_id")
  return s

def actionSummary : Action → Json
  | .read p => Json.mkObj [("read", p.render)]
  | .write p => Json.mkObj [("write", p.render)]
  | .exec cwd argv _ => Json.mkObj [("exec", toJson argv), ("cwd", cwd.render)]
  | .fetch h => Json.mkObj [("fetch", h)]
  | .tool n => Json.mkObj [("tool", n)]
  | .malformed t why => Json.mkObj [("malformed", t), ("why", why)]

def decisionJson : Decision → Json
  | .allow => Json.mkObj [("decision", "allow")]
  | .ask r => Json.mkObj [("decision", "ask"), ("reason", r)]
  | .deny r => Json.mkObj [("decision", "deny"), ("reason", r)]

/-! ## One hook call -/

structure Config where
  policy   : System.FilePath
  stateDir : System.FilePath

/-- Handle one `PreToolUse` event; returns what to print on stdout. -/
def handle (cfg : Config) (input : String) : IO String := do
  let ev ← IO.ofExcept (Json.parse input)
  let session ← safeSessionId (← IO.ofExcept (ev.getObjValAs? String "session_id"))
  let tool ← IO.ofExcept (ev.getObjValAs? String "tool_name")
  let toolInput := (ev.getObjVal? "tool_input").toOption.getD (Json.mkObj [])
  let policy ← loadPolicy cfg.policy
  let cwd ← resolveReal [] (← IO.ofExcept (ev.getObjValAs? String "cwd"))
  let action ← toAction cwd tool toolInput
  IO.FS.createDirAll cfg.stateDir
  let lock ← IO.FS.Handle.mk (cfg.stateDir / s!"{session}.lock") .append
  -- Parallel tool calls run their hooks concurrently; serialize per session
  -- so a taint can't be lost to a read-modify-write race.
  lock.lock
  try
    let stateFile := cfg.stateDir / s!"{session}.json"
    let state ← if ← stateFile.pathExists then
        IO.ofExcept (stateOfJson (← IO.ofExcept (Json.parse (← IO.FS.readFile stateFile))))
      else pure {}
    let (d, state') := step policy state action
    IO.FS.writeFile stateFile (stateToJson state').compress
    let logLine := Json.mkObj [("tool", tool), ("action", actionSummary action),
      ("result", decisionJson d), ("tainted", toJson state'.tainted), ("used", toJson state'.used)]
    let log ← IO.FS.Handle.mk (cfg.stateDir / s!"{session}.log.jsonl") .append
    log.putStrLn logLine.compress
    return match d with
      | .allow => ""
      | .ask r => (hookOutput "ask" r).compress
      | .deny r => (hookOutput "deny" r).compress
  finally
    lock.unlock
where
  hookOutput (decision reason : String) : Json :=
    Json.mkObj [("hookSpecificOutput", Json.mkObj [
      ("hookEventName", "PreToolUse"),
      ("permissionDecision", decision),
      ("permissionDecisionReason", s!"lean-guard: {reason}")])]

end Guard.Hook
