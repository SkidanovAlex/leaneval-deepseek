/-
Copyright: work module for the Elgindi finite-time singularity project.

# The fundamental theorem of calculus along a radial slice of `∂_z^j F`

The `pzIter`-analogue of `Work.FTS.EllipticEst.DzIter_slice_FTC_open`: for `F` which is `C^∞`
on the open quadrant `Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen F`) and an
interior angle `θ ∈ (0, π/2)`, the radial slice `r ↦ ∂_z^j F(r,θ)` of the `j`-th plain
`z`-derivative is `C^∞` on `(0,∞)` (`SmoothOpen.pzIter`, `SmoothOpen.curry_z`), with
derivative `r ↦ ∂_z^{j+1} F(r,θ)` (`SmoothOpen.hasDerivAt_slice_pzIter`).  Consequently, for
`0 < s ≤ z`,

  `∂_z^j F(z,θ) - ∂_z^j F(s,θ) = ∫ r in s..z, ∂_z^{j+1} F(r,θ)`.

The proof is a direct application of `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

theorem pzIter_slice_FTC_open {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (j : ℕ) {s z θ : ℝ} (hs : 0 < s) (hsz : s ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pzIter j F z θ - Work.Spaces.pzIter j F s θ
      = ∫ r in s..z, Work.Spaces.pzIter (j + 1) F r θ := by
  -- the derivative along the slice is continuous on the interval, hence interval integrable
  have hcont' : ContinuousOn (fun r : ℝ => Work.Spaces.pzIter (j + 1) F r θ)
      (Set.uIcc s z) := by
    rw [Set.uIcc_of_le hsz]
    exact ((hF.pzIter j).pz.curry_z hθ).continuousOn.mono
      (fun r hr => lt_of_lt_of_le hs hr.1)
  -- the slice is differentiable at every point of the interval, with derivative the next partial
  have hderiv : ∀ r ∈ Set.uIcc s z,
      HasDerivAt (fun r : ℝ => Work.Spaces.pzIter j F r θ)
        (Work.Spaces.pzIter (j + 1) F r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hsz] at hr
    exact hF.hasDerivAt_slice_pzIter j hθ (lt_of_lt_of_le hs hr.1)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont'.intervalIntegrable).symm

end Work.FTS.EllipticEst
