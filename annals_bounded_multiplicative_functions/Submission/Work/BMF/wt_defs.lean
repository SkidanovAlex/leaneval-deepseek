import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The smooth trapezoidal weight used in `completion_of_sums`

`φ` is a nonnegative `C^∞` bump of mass `1` supported in `[-1/2, 1/2]` (a `ContDiffBump`).
`φ_B(x) = B⁻¹ φ(x/B)` is its rescaling of width `B`, `gH B` is an antiderivative, and
`Wt B a c t = gH B (t-a) - gH B (t-c) ≈ 1_[a,c]`.
-/

open Polynomial Finset Real Complex MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Work.BMF

/-- A `C^∞` bump around `0` with support in the ball of radius `1/2`. -/
noncomputable def cbump : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The normalised bump: nonnegative, smooth, of mass `1`, supported in `[-1/2,1/2]`. -/
noncomputable def phi : ℝ → ℝ := cbump.normed volume

/-- Rescaled bump of width `B` and unit mass. -/
noncomputable def phiB (B x : ℝ) : ℝ := (1 / B) * phi (x / B)

/-- An antiderivative of `phiB B`. -/
noncomputable def gH (B x : ℝ) : ℝ := ∫ s in (0)..x, phiB B s

/-- The trapezoidal weight. -/
noncomputable def Wf (B a c : ℝ) : ℝ → ℝ := fun t => gH B (t - a) - gH B (t - c)

/-- The trapezoidal weight, as a complex-valued function (for the Fourier transform). -/
noncomputable def Wt (B a c : ℝ) : ℝ → ℂ := fun t => (Wf B a c t : ℂ)

/-- The (pointwise) Fourier transform on `ℝ`, as a plain function. -/
noncomputable def FT (f : ℝ → ℂ) : ℝ → ℂ := 𝓕 f

/-- The `L¹`-norm of `deriv φ`; it controls the second derivative of the weight. -/
noncomputable def Kphi : ℝ := ∫ x, |deriv phi x|

end Work.BMF
