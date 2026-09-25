/-
# Auxiliary definitions for the first-order differentiability of the Beurling transform

`beurlingV g z = -(1/π) ∫ w, w⁻² • (g (z+w) - χ w • g z)` is an integral whose integrand
depends on the parameter `z` in two places, `g (z+w)` and `g z`.  We isolate

* `beurlingIntegrand g z w = w⁻² • (g (z+w) - χ w • g z)`  (the integrand), and
* `beurlingDeriv g z w = w⁻² • (fderiv ℝ g (z+w) - χ w • fderiv ℝ g z)`  (its formal
  `z`-derivative, a continuous real-linear map `ℂ →L[ℝ] E`),

together with the explicit integrable majorant `beurlingBound α K L M R z` used to dominate
`beurlingDeriv g x w` uniformly for `x` in the unit ball around `z`.
-/
import Mathlib
import Submission.Work.Beltrami.beurlingV
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

noncomputable section

namespace Work.Beltrami

open MeasureTheory

/-- The integrand of the translated (convolution) form of the Beurling transform:
`w ↦ w⁻² • (g (z + w) - χ w • g z)`, where `χ = bumpC` is the fixed cutoff. -/
def beurlingIntegrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℂ → E)
    (z w : ℂ) : E :=
  ((w ^ 2)⁻¹ : ℂ) • (g (z + w) - (bumpC w : ℂ) • g z)

/-- The formal `z`-derivative of `beurlingIntegrand g`: differentiating
`w⁻² • (g (z+w) - χ w • g z)` in `z` gives `w⁻² • (Dg (z+w) - χ w • Dg z)`, a continuous
real-linear map `ℂ →L[ℝ] E`. -/
def beurlingDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℂ → E)
    (z w : ℂ) : ℂ →L[ℝ] E :=
  ((w ^ 2)⁻¹ : ℂ) • (fderiv ℝ g (z + w) - (bumpC w : ℂ) • fderiv ℝ g z)

/-- An integrable majorant for `‖beurlingDeriv g x w‖` and `‖beurlingIntegrand g x w‖`,
uniform for `x` in the unit ball around `z`:
`|K| ‖w‖^{α-2}` near `0` (where `χ = 1`), `|L| ‖w‖⁻¹` near `0` for the non-differentiated
integrand, and the constant `8 (|L| + |M| + 1)` on the annulus `1/2 ≤ ‖w‖ ≤ max 1 (R + ‖z‖ + 2)`,
beyond which both quantities vanish (the cutoff and the support of `g` kill them). -/
def beurlingBound (α K L M R : ℝ) (z w : ℂ) : ℝ :=
  |K| * (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (α - 2)) w
  + |L| * (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (-1 : ℝ)) w
  + 8 * (|L| + |M| + 1)
      * (Metric.closedBall (0 : ℂ) (max 1 (R + ‖z‖ + 2))).indicator (fun _ : ℂ => (1 : ℝ)) w

end Work.Beltrami
