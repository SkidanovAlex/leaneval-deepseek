import Mathlib
import Submission.Work.DSSER.Basic
import Submission.Work.DSSER.moduleFinite_serRing
import Submission.Work.DSSER.isAdicComplete_of_finite

universe u

namespace Work.DSSER

/-- `R' = R[Z]/(Z_i^p - z_i)` is `𝔪`-adically complete over `R`: combine `isAdicComplete_of_finite`
with `moduleFinite_serRing` and `IsLocalRing.maximalIdeal_le_jacobson`. -/
theorem isAdicComplete_maximalIdeal_serRing (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (p : ℕ) (hp : 0 < p)
    {d : ℕ} (z : Fin d → R) :
    IsAdicComplete (IsLocalRing.maximalIdeal R) (Work.DSSER.serRing R p z) := by
  -- `R'` is a finite `R`-module (`Z_i^p = z_i` makes every variable integral over `R`).
  have hfin : Module.Finite R (serRing R p z) := moduleFinite_serRing R p hp z
  -- The maximal ideal is contained in the Jacobson radical of `R`.
  have hI : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) :=
    IsLocalRing.maximalIdeal_le_jacobson ⊥
  -- Hence a finite module over the `𝔪`-adically complete Noetherian ring `R` is `𝔪`-adically complete.
  exact isAdicComplete_of_finite (IsLocalRing.maximalIdeal R) hI

end Work.DSSER
