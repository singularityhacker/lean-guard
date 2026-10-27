import Guard.Path

/-!
# The reference monitor

Everything in this file is pure. `decide` is the whole policy; `step` adds
the session state (secret taint + action budget); `run` folds `step` over a
trace. `Guard.Theorems` proves properties of exactly these definitions.
-/

namespace Guard

/-- What an agent wants to do, after the trusted parser (`Guard.Hook`) has
    turned a raw tool call into something we can reason about. -/
inductive Action where
  /-- Read a file or search a directory (Read / Glob / Grep). -/
  | read  (path : Path)
  /-- Create or modify a file (Write / Edit / MultiEdit / NotebookEdit). -/
  | write (path : Path)
  /-- Run a program. `paths` are the resolved forms of every argument, so a
      path the command could touch is in this list. -/
  | exec  (cwd : Path) (argv : List String) (paths : List Path)
  /-- Fetch a URL from this host (WebFetch). -/
  | fetch (host : String)
  /-- Any other tool, by name (MCP tools, WebSearch, Agent, ...). -/
  | tool  (name : String)
  /-- A call the parser could not understand, e.g. a shell pipeline. -/
  | malformed (tool : String) (why : String)
  deriving Repr, DecidableEq

inductive Decision where
  | allow
  /-- Hand the call to the human. -/
  | ask  (reason : String)
  | deny (reason : String)
  deriving Repr, DecidableEq

def Decision.isAllow : Decision → Bool
  | .allow => true
  | _ => false

/-- The call goes ahead, either on its own or after a human approves it. -/
def Decision.permits : Decision → Bool
  | .deny _ => false
  | _ => true

structure Policy where
  workspace       : Path
  /-- Extra places that may be read without asking. -/
  readRoots       : List Path := []
  /-- Programs that may run without asking, by bare name (resolved via PATH). -/
  allowedPrograms : List String := []
  /-- Programs that talk to the network. -/
  egressPrograms  : List String :=
    ["curl", "wget", "nc", "ncat", "netcat", "ssh", "scp", "sftp", "rsync", "ftp", "telnet"]
  /-- `git` subcommands that talk to the network. -/
  egressGitSubcommands : List String := ["push", "fetch", "pull", "clone", "ls-remote", "submodule"]
  /-- Programs that can do anything (interpreters, wrappers); treated as egress. -/
  opaquePrograms  : List String :=
    ["sh", "bash", "zsh", "fish", "env", "xargs", "python", "python3", "node", "deno", "bun",
     "ruby", "perl", "php", "lua", "osascript", "open", "make", "npx", "uv", "uvx"]
  /-- Run egress programs without asking (still blocked once tainted). -/
  allowEgressExec : Bool := false
  allowedHosts    : List String := []
  /-- Other tools that may be used without asking. Anything else is denied. -/
  allowedTools    : List String := []
  /-- Other tools known not to send data off the machine. Every other tool is
      assumed to be able to. -/
  localTools      : List String := []
  denyPaths       : List Path := []
  denyPrograms    : List String := []
  denyTools       : List String := []
  denyHosts       : List String := []
  secretNames     : List String :=
    [".env", ".envrc", ".netrc", ".npmrc", ".pypirc", "id_rsa", "id_ecdsa", "id_ed25519",
     "credentials", "secrets.json", "secrets.yaml", "secrets.yml"]
  secretPrefixes  : List String := [".env."]
  secretSuffixes  : List String := [".pem", ".key", ".p12", ".pfx", ".keystore"]
  /-- Maximum number of calls allowed without a human in the loop, per session. -/
  budget          : Nat := 200
  deriving Repr

structure State where
  /-- A secret has been (or may have been) read in this session. -/
  tainted : Bool := false
  /-- Calls allowed so far. -/
  used    : Nat := 0
  deriving Repr, DecidableEq

/-- The last `/`-separated part of a string. -/
def basename (s : String) : String := ((s.splitOn "/").getLast?).getD s

namespace Policy

def isSecretName (p : Policy) (name : String) : Bool :=
  p.secretNames.contains name ||
  p.secretPrefixes.any (name.startsWith ·) ||
  p.secretSuffixes.any (name.endsWith ·)

def canRead (p : Policy) (path : Path) : Bool :=
  p.workspace.within path || p.readRoots.any (·.within path)

def isEgressCommand (p : Policy) : List String → Bool
  | [] => false
  | prog :: args =>
    let name := basename prog
    p.egressPrograms.contains name || p.opaquePrograms.contains name ||
    (name == "git" && args.any p.egressGitSubcommands.contains)

/-- Why a deny rule applies, if one does. -/
def deniedBy (p : Policy) : Action → Option String
  | .read path | .write path =>
    if p.denyPaths.any (·.within path) then some s!"{path.render} is a protected path" else none
  | .exec _ argv paths =>
    match argv with
    | prog :: _ =>
      if p.denyPrograms.contains (basename prog) then some s!"program {prog} is denied"
      else if paths.any (fun q => p.denyPaths.any (·.within q)) then
        some "command references a protected path"
      else none
    | [] => none
  | .fetch host => if p.denyHosts.contains host then some s!"host {host} is denied" else none
  | .tool name => if p.denyTools.contains name then some s!"tool {name} is denied" else none
  | .malformed .. => none

/-- The decision for an action on its own, before session state. -/
def baseDecision (p : Policy) : Action → Decision
  | .read path =>
    if p.canRead path then .allow else .ask s!"read outside the workspace: {path.render}"
  | .write path =>
    if p.workspace.within path then .allow
    else .deny s!"write outside the workspace: {path.render}"
  | .exec cwd argv paths =>
    match argv with
    | [] => .deny "empty command"
    | prog :: _ =>
      if prog.contains '/' then .ask s!"program given by path: {prog}"
      else if !(p.allowedPrograms.contains prog) then .ask s!"program not on the allow-list: {prog}"
      else if !(p.workspace.within cwd && paths.all p.workspace.within) then
        .ask "command references paths outside the workspace"
      else if p.isEgressCommand argv && !p.allowEgressExec then
        .ask s!"command may use the network: {prog}"
      else .allow
  | .fetch host =>
    if p.allowedHosts.contains host then .allow else .ask s!"host not on the allow-list: {host}"
  | .tool name =>
    if p.allowedTools.contains name then .allow else .deny s!"tool not on the allow-list: {name}"
  | .malformed tool why => .ask s!"{tool}: {why}"

end Policy

namespace Action

/-- The action might read a secret. -/
def touchesSecret (p : Policy) : Action → Bool
  | .read path => p.isSecretName (path.getLast?.getD "")
  | .exec _ argv _ => argv.any (fun a => p.isSecretName (basename a))
  | .malformed .. => true
  | _ => false

/-- The action might send data off the machine. -/
def isEgress (p : Policy) : Action → Bool
  | .fetch _ => true
  | .exec _ argv _ => p.isEgressCommand argv
  | .tool name => !(p.localTools.contains name)
  | .malformed .. => true
  | _ => false

end Action

/-- The policy. Deny rules first, then the taint rule, then the per-action
    decision, and finally the budget, which only limits `allow`. -/
def decide (p : Policy) (s : State) (a : Action) : Decision :=
  match p.deniedBy a with
  | some r => .deny r
  | none =>
    if s.tainted && a.isEgress p then
      .deny "a secret was read earlier in this session; network access is blocked"
    else
      match p.baseDecision a with
      | .allow => if s.used < p.budget then .allow else .deny "action budget exhausted"
      | d => d

/-- Decide, then update the session. Taint is set by anything that goes
    ahead (including a human-approved `ask`), because the guard cannot see
    what the human chose. -/
def step (p : Policy) (s : State) (a : Action) : Decision × State :=
  let d := decide p s a
  (d, { tainted := s.tainted || (d.permits && a.touchesSecret p)
        used    := if d.isAllow then s.used + 1 else s.used })

/-- Run a whole trace, returning every decision and the final state. -/
def run (p : Policy) : State → List Action → List Decision × State
  | s, [] => ([], s)
  | s, a :: as =>
    let (ds, s') := run p (step p s a).2 as
    ((step p s a).1 :: ds, s')

def final (p : Policy) (s : State) (as : List Action) : State := (run p s as).2

def allowedCount : List Decision → Nat
  | [] => 0
  | d :: ds => (if d.isAllow then 1 else 0) + allowedCount ds

end Guard
