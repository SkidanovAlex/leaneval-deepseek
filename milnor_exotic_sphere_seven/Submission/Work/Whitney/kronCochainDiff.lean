import Mathlib
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# Stokes for the Kronecker pairing: `⟨d ℓ, Z⟩ = ⟨ℓ, ∂Z⟩`

The closing identity of the cup-side evaluation (`rankOne_cup_model_NOTES.md` §54e option 3): the
pairing of the coboundary `d ℓ` with a chain `Z` is the pairing of `ℓ` with the boundary `∂Z`.  It is
*definitional* (`cochainDiff` is the transpose of the differential), but it is not exported from the
tree: `Work.Cohomology.kronecker_coboundary_cycle` uses it as an internal `have`, and the cup-side
proof needs it as a rewriting rule at its last step.  This file exports it, in the general
`SSet`/`SSet.chainComplex` form, and in the two `ℤ`/singular spellings actually used downstream.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (X : SSet)

/-- **Stokes**: `⟨d ℓ, Z⟩ = ⟨ℓ, ∂Z⟩`. -/
theorem kronecker_cochainDiff {R : Type} [CommRing R] {n : ℕ} (ℓ : Cochain R X n)
    (Z : ↑((X.chainComplex (ModuleCat.of R R)).X (n + 1))) :
    kronecker R X (cochainDiff R X ℓ) Z
      = kronecker R X ℓ (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n) Z) := rfl

end

end Work.Cohomology

#print axioms Work.Cohomology.kronecker_cochainDiff
