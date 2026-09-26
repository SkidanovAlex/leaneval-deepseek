import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# The disc parametrisation of a `DiscRegion` retracts its range onto the unit disc

A `Work.SurgeryInvariance.DiscRegion P` is an embedded closed disc of the surface `P.carrier`,
given by a parametrisation `e : closedBall 0 1 → ℝ³` which is continuous injective and sends the
open disc into the surface.  The parametrisation is therefore a homeomorphism onto its range, and
its inverse — a continuous map from the range back to the closed unit disc — is the retraction
required below.  (Continuity of the inverse is automatic: `e` is a continuous injective map from
the compact disc `closedBall 0 1` to the Hausdorff space `ℝ³`, so it is a closed embedding.)
-/

namespace Work.Drive.EpsForm

/-- **The inverse parametrisation of a `DiscRegion`.**  Since `D.e` is an injective continuous map
from the compact disc to `ℝ³`, it is a homeomorphism onto its range; the inverse homeomorphism,
read as a continuous map, is a continuous retraction of the range of `D.e` onto the closed unit
disc, which is a left inverse of `D.e`. -/
theorem exists_continuous_retraction_DiscRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    ∃ Φ : C(↥(Set.range D.e), Metric.closedBall (0 : ℂ) 1),
      ∀ x : ↥(Set.range D.e), D.e (Φ x) = (x : LeanEval.KnotTheory.PardonDistortion.R3) := by
  -- The parametrisation, as a homeomorphism onto its range.
  let H : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥(Set.range D.e) :=
    (D.e.continuous.isClosedEmbedding D.inj).toIsEmbedding.toHomeomorph
  refine ⟨{ toFun := H.symm, continuous_toFun := H.symm.continuous }, ?_⟩
  intro x
  -- `H` evaluates as `D.e` by definition, so `H (H.symm x) = x` is exactly what is needed.
  have h1 : ((H (H.symm x) : ↥(Set.range D.e)) : LeanEval.KnotTheory.PardonDistortion.R3)
      = (x : LeanEval.KnotTheory.PardonDistortion.R3) :=
    congrArg Subtype.val (H.apply_symm_apply x)
  rw [show ((H (H.symm x) : ↥(Set.range D.e)) : LeanEval.KnotTheory.PardonDistortion.R3)
      = D.e (H.symm x) from rfl] at h1
  exact h1

end Work.Drive.EpsForm
