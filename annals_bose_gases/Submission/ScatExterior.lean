import ChallengeDeps
import Submission.ExteriorClassify
import Submission.ScatHarmonic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exterior form of a scattering solution (Layer 3)

A radial scattering solution `w` of a potential `v` supported in `ball 0 R`
is weakly harmonic outside the support of `v`
(`ScatHarmonic.scattering_harmonic_exterior`), locally integrable and
decaying (`IsScatteringSolution.lhs_integrable`, `.lim`); by the exterior
classification (`ExteriorClassify.exterior_harmonic_classification`) it is
therefore `w x = c / ‖x‖` a.e. for `‖x‖ ≥ R` for some constant `c`.

The value of `c` (the scattering length `a v` for the chosen solution) is
identified by the Gauss/shell identity in a later module; this module only
records the *form* of the exterior behaviour.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A radial scattering solution of a potential supported in `ball 0 R` is
`c/‖x‖` a.e. on the exterior `{x | R ≤ ‖x‖}`, for some constant `c`. -/
theorem scattering_solution_exterior_form {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ∃ c : ℝ, ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w x = c / ‖x‖ := by
  refine exterior_harmonic_classification (w := w) (R := R) hR hrad ?_ ?_ ?_
  · exact hw.lhs_integrable
  · intro φ hφ hcomp hφsupp
    exact scattering_harmonic_exterior hv_supp hw hφ hcomp hφsupp
  · exact hw.lim

end Submission.BoseGases
