/-!
# Parsing helpers (trusted, pure)

Not covered by the theorems. These are kept small and strict, and they
refuse anything they don't understand rather than guessing.
-/

namespace Guard.Parse

/-- Characters that make an unquoted shell word mean more than its text:
    command separators, pipes, redirects, substitution, globs, history,
    home expansion, comments, escapes. -/
def unquotedUnsafe : List Char :=
  [';', '|', '&', '$', '`', '<', '>', '(', ')', '{', '}', '!', '\\', '*', '?', '[', ']',
   '~', '#', '^']

/-- Characters still active inside double quotes. -/
def doubleQuotedUnsafe : List Char := ['$', '`', '\\', '!']

private def flush (words : List String) (cur : List Char) (inWord : Bool) : List String :=
  if inWord then String.ofList cur.reverse :: words else words

private def go : List Char → List String → List Char → Bool → Option Char →
    Except String (List String)
  | [], words, cur, inWord, none => .ok (flush words cur inWord).reverse
  | [], _, _, _, some _ => .error "unterminated quote"
  | c :: cs, words, cur, inWord, some '\'' =>
    if c == '\'' then go cs words cur inWord none else go cs words (c :: cur) inWord (some '\'')
  | c :: cs, words, cur, inWord, some q =>
    if c == q then go cs words cur inWord none
    else if doubleQuotedUnsafe.contains c then .error s!"shell syntax `{c}` inside quotes"
    else go cs words (c :: cur) inWord (some q)
  | c :: cs, words, cur, inWord, none =>
    if c == ' ' || c == '\t' then go cs (flush words cur inWord) [] false none
    else if c == '\n' || c == '\r' then .error "multi-line command"
    else if c == '\'' || c == '"' then go cs words cur true (some c)
    else if unquotedUnsafe.contains c then .error s!"shell syntax `{c}`"
    else go cs words (c :: cur) true none

/-- Split a shell command into words, or refuse with a reason. Only plain
    words and simple quoting are accepted; anything that would make the
    shell do more than run one program with literal arguments is refused. -/
def tokenize (cmd : String) : Except String (List String) := do
  let words ← go cmd.toList [] [] false none
  match words with
  | [] => .error "empty command"
  | w :: _ =>
    -- `FOO=bar cmd` sets an environment variable; zsh expands `=cmd`.
    if w.contains '=' then .error "leading environment assignment" else .ok words

/-- Every string in a command's arguments that could name a file: the word
    itself, the value of `--opt=value`, and the tail of a joined short option
    like `-o/path`. Over-approximates on purpose. -/
def pathCandidates (args : List String) : List String :=
  args.flatMap fun a =>
    let eq := match a.splitOn "=" with
      | _ :: rest@(_ :: _) => ["=".intercalate rest]
      | _ => []
    let joined := if a.startsWith "-" && !a.startsWith "--" && a.length > 2
      then [String.ofList (a.toList.drop 2)] else []
    a :: eq ++ joined

/-- The host of an `http(s)` URL, lower-cased, without userinfo or port. -/
def hostOf (url : String) : Option String :=
  match url.splitOn "://" with
  | [scheme, rest] =>
    if scheme.toLower != "http" && scheme.toLower != "https" then none else
    let authority := rest.toList.takeWhile (fun c => c != '/' && c != '?' && c != '#')
    let afterAt := match (String.ofList authority).splitOn "@" |>.getLast? with
      | some s => s | none => ""
    let host := (String.ofList (afterAt.toList.takeWhile (· != ':'))).toLower
    if host.isEmpty then none else some host
  | _ => none

/-- The literal leading part of a glob pattern (up to the first component
    with a wildcard), or `none` if a `..` appears after a wildcard. -/
def globBase (pattern : String) : Option String :=
  let parts := pattern.splitOn "/"
  let isWild (s : String) := s.toList.any (fun c => c == '*' || c == '?' || c == '[' || c == '{')
  let lit := parts.takeWhile (!isWild ·)
  let rest := parts.drop lit.length
  if rest.contains ".." then none
  else
    let base := "/".intercalate lit
    some (if base.isEmpty && pattern.startsWith "/" then "/" else if base.isEmpty then "." else base)

end Guard.Parse
