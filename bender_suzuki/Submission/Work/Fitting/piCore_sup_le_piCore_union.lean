import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_π(G) ⊔ O_σ(G) ≤ O_{π ∪ σ}(G)`

The `π`-core is monotone in `π`, so each of `O_π(G)` and `O_σ(G)` is contained in
`O_{π ∪ σ}(G)`, where `π ∪ σ` is the predicate `fun p => π p ∨ σ p`.  Taking the supremum
of the two inclusions gives the stated inequality.

No finiteness is really needed for the argument (only the definition of `piCore` as a
supremum of a set of normal subgroups); the statement carries `[Finite G]` for compatibility
with its intended uses.
-/

namespace Work.Fitting

theorem piCore_sup_le_piCore_union (π σ : ℕ → Prop) (G : Type*) [Group G] [Finite G] :
    Work.Fitting.piCore π G ⊔ Work.Fitting.piCore σ G ≤ Work.Fitting.piCore (fun p => π p ∨ σ p) G := by
  refine sup_le ?_ ?_
  · exact piCore_mono (fun p hp => Or.inl hp)
  · exact piCore_mono (fun p hp => Or.inr hp)

end Work.Fitting
