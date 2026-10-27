# lean-guard

A policy layer for coding agents, written and **proved** in Lean 4.

Every tool call Claude Code makes goes through a Claude Code `PreToolUse`
hook to a native Lean binary. The binary decides **allow** (defer to Claude
Code's normal permissions), **ask** (hand the call to a human) or **deny**,
and keeps per-session state. The decision function comes with machine-checked
proofs. It complements a VM or container: the VM limits what *can* happen,
and the guard decides what *should*.

```
Claude Code ──PreToolUse JSON──► lean-guard ──► parse → Action        (trusted, Guard/Hook.lean)
                                              decide / step          (proved,  Guard/Core.lean)
                                              ◄── "" | ask | deny
```

## What is proved

All theorems are in [`Guard/Theorems.lean`](Guard/Theorems.lean). They hold for
**every** policy, state and action, not just test cases. `tests/Axioms.lean`
checks that none of them uses `sorry`.

| Theorem | Guarantee |
|---|---|
| `deny_wins` | If a deny rule matches, the answer is `deny`, never `ask` or `allow`. |
| `unlisted_tool_not_allowed`, `unlisted_program_not_allowed`, `malformed_not_allowed` | Default deny: anything not on an allow-list, or anything the parser can't understand, never runs without a human. |
| `write_contained`, `exec_contained`, `read_contained` | Allowed writes, and allowed commands with every path they mention, are inside the workspace by component prefix (`/ws-evil` is not inside `/ws`). |
| `resolve_clean` | Path normalization leaves no `.`, `..` or empty components. |
| `no_exfiltration` | In any session, once an action that may read a secret goes ahead, every later action that may send data off the machine is **denied**, whatever happened before or in between. |
| `budget_respected` | Across any trace, at most `budget` calls are allowed without a human. |

## What is trusted (not proved)

The proofs cover the decision. The code that turns raw tool calls into
`Action`s is trusted and kept deliberately strict:

- **Shell commands** (`Guard/Parse.lean`): only plain words and simple
  quotes are accepted. Pipes, `;`, `&&`, `$(…)`, redirects, globs, `~` and
  env prefixes become `malformed`, which goes to the human. The guarantee is
  about the *shape* of allowed commands, not that a program is harmless.
  That's why interpreters (`python`, `node`, `sh`, …) count as possible
  network egress and are not allow-listed in the demo policy.
- **Paths** (`Guard/Hook.lean`): resolved with `realpath`, so symlinks out of
  the workspace are caught, and dangling symlinks are refused. A file can
  still change between the check and the use (TOCTOU).
- **Secret detection** is by file name (`.env`, `*.pem`, `id_rsa`, …). A
  secret under an innocent name won't taint the session.
- **"Ask" taints conservatively.** The guard can't see whether the human
  approved an `ask`, so a `permits` decision on anything that might touch a
  secret (including any unparseable command) taints the session.
- **Coverage**: only tool calls that go through the hook are seen. Keep the VM.

## Fail-closed

Claude Code treats a hook that crashes or times out as *non-blocking*. To
avoid failing open:

- `main` catches every error and exits `2`, which blocks the call.
- The hook command ends in `|| exit 2`, so even a missing binary blocks.
- The hook sets `"onFailure": "block"`.
- `allow` prints nothing, which leaves Claude Code's own permission rules in
  force. The guard can only restrict, never grant.
- Unknown policy keys are an error, so a typo can't silently weaken a rule.

## Usage

```sh
lake build                 # builds the binary and checks every proof
./tests/run.sh             # proof audit + 48 end-to-end cases against the binary

cd demo-workspace && claude   # every tool call now goes through the guard
```

- Policy: [`policies/demo.json`](policies/demo.json). It lives outside the
  workspace, which, like `.claude/`, is a deny path, so the agent can't edit
  it or turn off the hook. Relative paths are relative to the policy file.
  Run `lean-guard --policy FILE --check` to see the parsed policy.
- State and an audit log are written per session to
  `~/.local/state/lean-guard/<session>.{json,log.jsonl}`. A new session
  starts untainted.

## Layout

```
Guard/Path.lean      paths as components, normalization (+ proof)
Guard/Core.lean      Action, Policy, decide, step, run          ← the reference monitor
Guard/Theorems.lean  the guarantees
Guard/Parse.lean     shell tokenizer, URL host, glob base        (trusted)
Guard/Hook.lean      JSON ↔ Action, realpath, policy, state, IO  (trusted)
Main.lean            CLI, fail-closed exit codes
policies/demo.json   demo policy
demo-workspace/      a toy project with a FAKE .env and the hook wired in
tests/               end-to-end script + axiom audit
```
