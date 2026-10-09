/-
Copyright (c) 2025. All rights reserved.

# Properness is strictly stronger than solvability: the split embedding problem

An embedding problem with abelian kernel always has a *plain* solution as soon as the extension
splits, but a solution need not be *proper*: the canonical section of `π` misses the kernel.

This is the formal content of the classical fact (Ikeda, Hoechsmann) that the vanishing of the
obstruction class — the existence of a lift, equivalently the pulled back extension class being a
coboundary — describes *plain* solutions only, whereas the paper needs *proper* solutions
(Proposition 11, Theorem 15).  The extra input needed to upgrade a plain solution to a proper one
is exactly the Grunwald–Wang input `Work.Properness.Setup.ScholzGrunwaldWangInput`
(see `Submission/Work/Properness/ScholzGrunwaldWang.lean`).

## Main declarations

* `Work.Properness.hasLift_not_imp_hasProperLift` — an explicit abstract embedding problem with
  `HasLift` but not `HasProperLift` (the trivial setting `H = Q = 1`, `E = ℤ/2`);
* `Work.Properness.section_lift_not_isProper` — the general mechanism: for a *split* embedding
  problem (`σ` a section of `π`) the canonical lift `σ ∘ ρ` is never proper when `A ≠ 1`.
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.trivialSetup_hasLift
import Submission.Work.Properness.trivialSetup_no_properLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

open scoped Classical

set_option autoImplicit true

noncomputable section

universe u v w

/-- **Solvability does not imply proper solvability.**  The abstract embedding problem
`1 → ℤ/2 → ℤ/2 → 1 → 1` (i.e. `Work.Properness.trivialSetup`) has a lift but no surjective lift.

This is the formal statement that condition (b) — a lift exists, equivalently the pulled back
obstruction class is a coboundary — does **not** imply condition (c)/(a) — a *surjective* lift,
i.e. a proper solution of the embedding problem.  The paper's pass from a plain to a proper
solution is the content of Proposition 11 (Grunwald–Wang). -/
theorem hasLift_not_imp_hasProperLift :
    Work.Properness.trivialSetup.HasLift ∧
      ¬ Work.Properness.trivialSetup.HasProperLift :=
  ⟨trivialSetup_hasLift, trivialSetup_no_properLift⟩

end

end Work.Properness
