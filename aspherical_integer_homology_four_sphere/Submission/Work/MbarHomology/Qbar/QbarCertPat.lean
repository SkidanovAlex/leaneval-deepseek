/-
# The pattern-level arithmetic check for the sparse certificates of `Q̄`

The 888 emptiness patterns of `Submission.Work.MbarHomology.Qbar.QbarCertData` are checked here:
for each pattern `p`, the two coefficients `certMu1`, `certMu2` on `certC1 p`, `certC2 p` and the
nonnegative combination `lamValOf p`, `lamIdxOf p` satisfy the Farkas identities.  This is the
first hypothesis of `Work.MbarHomology.Qbar.QbarPD_hemp_of_pattern`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCertDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option autoImplicit false

namespace Work.MbarHomology

open scoped BigOperators

/-- The pattern-level Farkas identities, for all `888` patterns. -/
abbrev HpatAll : Prop :=
  ∀ p : Fin 888,
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t))

theorem hpatAll : HpatAll := by decide

end Work.MbarHomology
