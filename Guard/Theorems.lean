import Guard.Core

/-!
# What the guard guarantees

Every theorem here is about `decide` / `step` / `run` exactly as they run in
the `lean-guard` binary. They hold for **every** policy, state and action;
none of them is a test of particular inputs.

What they do *not* cover is the trusted boundary: turning Claude Code's raw
JSON into an `Action` (`Guard.Hook`). See `README.md`.
-/

namespace Guard

/-- Everything an `allow` implies, in one place. -/
theorem decide_allow {p : Policy} {s : State} {a : Action} (h : decide p s a = .allow) :
    p.deniedBy a = none ∧ (s.tainted && a.isEgress p) = false ∧
    p.baseDecision a = .allow ∧ s.used < p.budget := by
  unfold decide at h
  cases hd : p.deniedBy a with
  | some r => simp [hd] at h
  | none =>
    simp only [hd] at h
    by_cases ht : (s.tainted && a.isEgress p) = true
    · simp [ht] at h
    · simp only [ht, Bool.false_eq_true, ite_false] at h
      cases hb : p.baseDecision a with
      | allow =>
        simp only [hb] at h
        by_cases hu : s.used < p.budget
        · exact ⟨rfl, by simpa using ht, rfl, hu⟩
        · simp [hu] at h
      | ask r => simp [hb] at h
      | deny r => simp [hb] at h

/-! ## 1 · Deny rules always win -/

/-- If any deny rule matches, the answer is `deny`. Not `ask`: no allow-list
    entry, budget, or human approval can override a deny rule. -/
theorem deny_wins {p : Policy} {s : State} {a : Action} {r : String}
    (h : p.deniedBy a = some r) : decide p s a = .deny r := by
  simp [decide, h]

/-! ## 2 · Default deny -/

/-- A tool that is not on the allow-list is never allowed. -/
theorem unlisted_tool_not_allowed {p : Policy} {s : State} {name : String}
    (h : name ∉ p.allowedTools) : decide p s (.tool name) ≠ .allow := by
  intro ha
  have := (decide_allow ha).2.2.1
  simp [Policy.baseDecision, h] at this

/-- A program that is not on the allow-list never runs without a human. -/
theorem unlisted_program_not_allowed {p : Policy} {s : State} {cwd : Path}
    {prog : String} {args : List String} {paths : List Path}
    (h : prog ∉ p.allowedPrograms) : decide p s (.exec cwd (prog :: args) paths) ≠ .allow := by
  intro ha
  have := (decide_allow ha).2.2.1
  simp only [Policy.baseDecision] at this
  split at this <;> simp_all

/-- A call the parser could not understand (pipes, `$(…)`, redirects, …) is
    never allowed on its own. -/
theorem malformed_not_allowed {p : Policy} {s : State} {tool why : String} :
    decide p s (.malformed tool why) ≠ .allow := by
  intro ha
  have := (decide_allow ha).2.2.1
  simp [Policy.baseDecision] at this

/-! ## 3 · Workspace containment -/

/-- An allowed write lands inside the workspace, by component prefix, so
    `/ws-evil` is not inside `/ws`. -/
theorem write_contained {p : Policy} {s : State} {path : Path}
    (h : decide p s (.write path) = .allow) : p.workspace <+: path := by
  have hb := (decide_allow h).2.2.1
  simp only [Policy.baseDecision] at hb
  split at hb
  · rename_i hw; exact List.isPrefixOf_iff_prefix.mp hw
  · cases hb

/-- An allowed command runs inside the workspace, and every path it mentions
    is inside the workspace too. -/
theorem exec_contained {p : Policy} {s : State} {cwd : Path} {argv : List String}
    {paths : List Path} (h : decide p s (.exec cwd argv paths) = .allow) :
    p.workspace <+: cwd ∧ ∀ q ∈ paths, p.workspace <+: q := by
  have hb := (decide_allow h).2.2.1
  simp only [Policy.baseDecision] at hb
  split at hb
  · cases hb
  · repeat' (split at hb; · cases hb)
    rename_i hin _
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, List.all_eq_false,
      Bool.not_eq_true, not_or, not_exists, not_and, Bool.not_eq_false] at hin
    exact ⟨List.isPrefixOf_iff_prefix.mp hin.1,
      fun q hq => List.isPrefixOf_iff_prefix.mp (hin.2 q hq)⟩

/-- An allowed read is inside the workspace or one of the read roots. -/
theorem read_contained {p : Policy} {s : State} {path : Path}
    (h : decide p s (.read path) = .allow) :
    p.workspace <+: path ∨ ∃ r ∈ p.readRoots, r <+: path := by
  have hb := (decide_allow h).2.2.1
  simp only [Policy.baseDecision] at hb
  split at hb
  · rename_i hr
    simp only [Policy.canRead, Bool.or_eq_true, List.any_eq_true] at hr
    rcases hr with hw | ⟨r, hr, hw⟩
    · exact .inl (List.isPrefixOf_iff_prefix.mp hw)
    · exact .inr ⟨r, hr, List.isPrefixOf_iff_prefix.mp hw⟩
  · cases hb

/-! ## 4 · No exfiltration after reading a secret -/

theorem step_keeps_taint {p : Policy} {s : State} {a : Action} (h : s.tainted = true) :
    (step p s a).2.tainted = true := by
  simp [step, h]

theorem final_keeps_taint {p : Policy} (as : List Action) :
    ∀ s : State, s.tainted = true → (final p s as).tainted = true := by
  induction as with
  | nil => intro s h; simpa [final, run] using h
  | cons a as ih => intro s h; exact ih _ (step_keeps_taint h)

/-- Once tainted, every egress action is denied outright. Not `ask`: the
    human is not offered the chance to approve it either. -/
theorem egress_denied_when_tainted {p : Policy} {s : State} {a : Action}
    (ht : s.tainted = true) (he : a.isEgress p = true) : ∃ r, decide p s a = .deny r := by
  unfold decide
  cases hd : p.deniedBy a with
  | some r => exact ⟨r, rfl⟩
  | none => simp [ht, he]

/-- How `run` lays out its decisions: the decision for `a` is made in the
    state left by everything before it. -/
theorem run_split {p : Policy} (xs : List Action) (a : Action) (ys : List Action) :
    ∀ s : State, (run p s (xs ++ a :: ys)).1 =
      (run p s xs).1 ++ decide p (final p s xs) a :: (run p (step p (final p s xs) a).2 ys).1 := by
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih => intro s; simp [run, final, ih]

/-- **No exfiltration.** In any session, whatever happened before (`pre`)
    and in between (`mid`): once an action that may read a secret goes ahead,
    every later action that may send data off the machine is denied. -/
theorem no_exfiltration {p : Policy} {s : State} (pre mid : List Action) (a b : Action)
    (hsecret : a.touchesSecret p = true)
    (hwent : (decide p (final p s pre) a).permits = true)
    (hegress : b.isEgress p = true) :
    ∃ r, decide p (final p (step p (final p s pre) a).2 mid) b = .deny r := by
  apply egress_denied_when_tainted _ hegress
  apply final_keeps_taint
  simp [step, hsecret, hwent]

/-! ## 5 · The action budget holds over any trace -/

theorem step_fst (p : Policy) (s : State) (a : Action) : (step p s a).1 = decide p s a := rfl

theorem step_used (p : Policy) (s : State) (a : Action) :
    (step p s a).2.used = s.used + (if (decide p s a).isAllow then 1 else 0) := by
  simp only [step]; split <;> simp

theorem allow_within_budget {p : Policy} {s : State} {a : Action}
    (h : (decide p s a).isAllow = true) : s.used < p.budget := by
  cases hd : decide p s a with
  | allow => exact (decide_allow hd).2.2.2
  | ask r => simp [hd, Decision.isAllow] at h
  | deny r => simp [hd, Decision.isAllow] at h

theorem budget_invariant (p : Policy) (as : List Action) :
    ∀ s : State, s.used ≤ p.budget →
      allowedCount (run p s as).1 + s.used = (final p s as).used ∧
      (final p s as).used ≤ p.budget := by
  induction as with
  | nil => intro s h; simp [run, final, allowedCount, h]
  | cons a as ih =>
    intro s h
    have hstep := step_used p s a
    have hle : (step p s a).2.used ≤ p.budget := by
      by_cases hA : (decide p s a).isAllow = true
      · have := allow_within_budget hA; simp [hA] at hstep; omega
      · simp [hA] at hstep; omega
    obtain ⟨h1, h2⟩ := ih _ hle
    simp only [final, run, allowedCount, step_fst] at h1 h2 ⊢
    refine ⟨?_, h2⟩
    by_cases hA : (decide p s a).isAllow = true <;> simp [hA] at hstep ⊢ <;> omega

/-- **Budget.** Starting a fresh session, no trace of any length gets more
    than `budget` calls allowed without a human. -/
theorem budget_respected (p : Policy) (as : List Action) :
    allowedCount (run p {} as).1 ≤ p.budget := by
  have := budget_invariant p as {} (Nat.zero_le _)
  simp at this
  omega

end Guard
