import Guard.Theorems
-- Every guarantee should depend only on Lean's standard axioms (no `sorryAx`).
#print axioms Guard.resolve_clean
#print axioms Guard.deny_wins
#print axioms Guard.unlisted_tool_not_allowed
#print axioms Guard.unlisted_program_not_allowed
#print axioms Guard.malformed_not_allowed
#print axioms Guard.write_contained
#print axioms Guard.exec_contained
#print axioms Guard.read_contained
#print axioms Guard.egress_denied_when_tainted
#print axioms Guard.no_exfiltration
#print axioms Guard.run_split
#print axioms Guard.budget_respected
