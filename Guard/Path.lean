/-!
# Paths

The core never sees raw path strings. A `Path` is an absolute path held as
its list of components, so `/Users/me/ws` is `["Users", "me", "ws"]`.

Containment is a *component* prefix check, so the sibling-prefix trick
(`/Users/me/ws-evil` "starting with" `/Users/me/ws`) is not even expressible.
-/

namespace Guard

/-- An absolute path as its components. `[]` is `/`. -/
abbrev Path := List String

def Path.render (p : Path) : String := "/" ++ "/".intercalate p

/-- `p` lies at or below `root`. -/
def Path.within (root p : Path) : Bool := root.isPrefixOf p

/-- A component that survives normalization: not empty, `.`, or `..`. -/
def Clean (c : String) : Prop := c ≠ "" ∧ c ≠ "." ∧ c ≠ ".."

/-- One normalization step over a *reversed* component stack. `..` pops;
    at the root it stays at the root, as the OS does. -/
def normStep (stack : List String) (c : String) : List String :=
  if c == "" || c == "." then stack
  else if c == ".." then stack.drop 1
  else c :: stack

/-- Resolve `raw` against `cwd` and normalize lexically (no filesystem
    access; symlinks are handled by the trusted resolver in `Guard.Hook`). -/
def resolve (cwd : Path) (raw : String) : Path :=
  let base := if raw.startsWith "/" then [] else cwd
  ((raw.splitOn "/").foldl normStep base.reverse).reverse

theorem normStep_clean {stack : List String} {c : String}
    (h : ∀ x ∈ stack, Clean x) : ∀ x ∈ normStep stack c, Clean x := by
  intro x hx
  unfold normStep at hx
  by_cases h1 : (c == "" || c == ".") = true
  · simp only [h1, ite_true] at hx; exact h x hx
  · by_cases h2 : (c == "..") = true
    · simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at hx
      exact h x (List.mem_of_mem_drop hx)
    · simp only [h1, h2, ite_false, Bool.false_eq_true] at hx
      cases hx with
      | head =>
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h1
        simp only [beq_iff_eq] at h2
        exact ⟨h1.1, h1.2, h2⟩
      | tail _ hx => exact h x hx

theorem foldl_normStep_clean (parts : List String) :
    ∀ stack : List String, (∀ x ∈ stack, Clean x) →
      ∀ x ∈ parts.foldl normStep stack, Clean x := by
  induction parts with
  | nil => intro stack h; simpa using h
  | cons c cs ih => intro stack h; exact ih _ (normStep_clean h)

/-- **Normalization is sound**: starting from a clean working directory, a
    resolved path never contains an empty, `.` or `..` component, so no
    traversal survives into the containment check. -/
theorem resolve_clean (cwd : Path) (raw : String) (h : ∀ x ∈ cwd, Clean x) :
    ∀ x ∈ resolve cwd raw, Clean x := by
  intro x hx
  unfold resolve at hx
  rw [List.mem_reverse] at hx
  refine foldl_normStep_clean _ _ ?_ x hx
  intro y hy
  rw [List.mem_reverse] at hy
  split at hy
  · simp at hy
  · exact h y hy

end Guard
