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

theorem hpatAll_c0 : ∀ p : Fin 888, 0 ≤ p.val → p.val < 111 → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll_c1 : ∀ p : Fin 888, 111 ≤ p.val → p.val < 222 → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll_c2 : ∀ p : Fin 888, 222 ≤ p.val → p.val < 333 → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll_c3 : ∀ p : Fin 888, 333 ≤ p.val → p.val < 444 → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll_c4 : ∀ p : Fin 888, 444 ≤ p.val → p.val < 555 → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll_c5 : ∀ p : Fin 888, 555 ≤ p.val → p.val < 666 → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll_c6 : ∀ p : Fin 888, 666 ≤ p.val → p.val < 777 → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll_c7 : ∀ p : Fin 888, 777 ≤ p.val → 
    (∀ t : Fin 3, 0 ≤ lamValOf (p : ℕ) t) ∧
    (∀ j' : Fin 4,
      certMu1 (p : ℕ) * qNrm (certC1 (p : ℕ)) j' + certMu2 (p : ℕ) * qNrm (certC2 (p : ℕ)) j'
      = ∑ t : Fin 3, lamValOf (p : ℕ) t * qNrm (lamIdxOf (p : ℕ) t) j') ∧
    (0 < certMu1 (p : ℕ) * qRhs (certC1 (p : ℕ)) + certMu2 (p : ℕ) * qRhs (certC2 (p : ℕ))
        - ∑ t : Fin 3, lamValOf (p : ℕ) t * qRhs (lamIdxOf (p : ℕ) t)) := by decide +kernel

theorem hpatAll : HpatAll := by
  intro p
  by_cases h0 : p.val < 111
  · exact hpatAll_c0 p (by omega) h0
  by_cases h1 : p.val < 222
  · exact hpatAll_c1 p (by omega) h1
  by_cases h2 : p.val < 333
  · exact hpatAll_c2 p (by omega) h2
  by_cases h3 : p.val < 444
  · exact hpatAll_c3 p (by omega) h3
  by_cases h4 : p.val < 555
  · exact hpatAll_c4 p (by omega) h4
  by_cases h5 : p.val < 666
  · exact hpatAll_c5 p (by omega) h5
  by_cases h6 : p.val < 777
  · exact hpatAll_c6 p (by omega) h6
  exact hpatAll_c7 p (by omega)

end Work.MbarHomology
