/-
Copyright: work module for the Elgindi finite-time singularity project.

# The fundamental theorem of calculus along a radial slice of `D_z^j F`

For `F : ℝ → ℝ → ℝ` which is `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen F`), every iterate `D_z^j F` is again `C^∞` on `Q0`
(`SmoothOpen.DzIter`), so for an interior angle `θ ∈ (0, π/2)` its radial slice
`r ↦ DzIter j F r θ` is `C^∞` on `(0,∞)`, with derivative
`r ↦ pz (DzIter j F) r θ = deriv (fun r' => DzIter j F r' θ) r`
(`SmoothOpen.hasDerivAt_slice_DzIter`).  Consequently, for `0 < s ≤ z`,

  `DzIter j F z θ - DzIter j F s θ = ∫ r in s..z, pz (DzIter j F) r θ`

— the fundamental theorem of calculus on the radial slice, with the interval integral of
Mathlib (`∫ r in s..z, …`), which is the form needed when the slice is differentiated in
`z` under an integral sign (the `EllipticEstimates` chapter of Elgindi's paper).

The proof is a direct application of `intervalIntegral.integral_eq_sub_of_hasDerivAt`:
the integrand is continuous on the compact interval `[s,z]` — both `DzIter j F` and
`pz (DzIter j F)` are `C^∞` on `Q0`, hence their slices are continuous on `Ioi 0 ⊇ [s,z]`
because `s > 0` — whence interval integrable.
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

theorem DzIter_slice_FTC_open {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (j : ℕ) {s z θ : ℝ} (hs : 0 < s) (hsz : s ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.DzIter j F z θ - Work.Spaces.DzIter j F s θ
      = ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ := by
  -- the derivative along the slice is continuous on the interval, hence interval integrable
  have hcont' : ContinuousOn (fun r : ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
      (Set.uIcc s z) := by
    rw [Set.uIcc_of_le hsz]
    exact ((hF.DzIter j).pz.curry_z hθ).continuousOn.mono
      (fun r hr => lt_of_lt_of_le hs hr.1)
  -- the slice is differentiable at every interior point of the interval, with derivative `pz`
  have hderiv : ∀ r ∈ Set.uIcc s z,
      HasDerivAt (fun r : ℝ => Work.Spaces.DzIter j F r θ)
        (Work.Spaces.pz (Work.Spaces.DzIter j F) r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hsz] at hr
    exact hF.hasDerivAt_slice_DzIter j hθ (lt_of_lt_of_le hs hr.1)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont'.intervalIntegrable).symm

end Work.FTS.EllipticEst
