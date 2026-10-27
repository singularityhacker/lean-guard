import Guard.Hook

open Guard

def usage : String :=
  "usage: lean-guard --policy FILE [--state DIR] [--check]\n\
   Reads one Claude Code PreToolUse event on stdin.\n\
   --check   load the policy, print it, and exit"

/-- Exit codes: 0 = answered (possibly with a deny), 2 = error, which
    Claude Code treats as a block. Never fails open. -/
def main (args : List String) : IO UInt32 := do
  try
    let rec parse (policy : Option String) (state : Option String) (check : Bool) :
        List String → IO (Option String × Option String × Bool)
      | "--policy" :: f :: rest => parse (some f) state check rest
      | "--state" :: d :: rest => parse policy (some d) check rest
      | "--check" :: rest => parse policy state true rest
      | [] => pure (policy, state, check)
      | a :: _ => throw (IO.userError s!"unknown argument `{a}`\n{usage}")
    let (policy, state, check) ← parse none none false args
    let some policy := policy | throw (IO.userError usage)
    if check then
      IO.println (repr (← Hook.loadPolicy policy))
      return 0
    let stateDir ← match state with
      | some d => pure (d : System.FilePath)
      | none =>
        let some home ← IO.getEnv "HOME" | throw (IO.userError "HOME is not set")
        pure ((home : System.FilePath) / ".local" / "state" / "lean-guard")
    let input ← (← IO.getStdin).readToEnd
    IO.print (← Hook.handle { policy, stateDir } input)
    return 0
  catch e =>
    IO.eprintln s!"lean-guard: {e} (blocking this call)"
    return 2
