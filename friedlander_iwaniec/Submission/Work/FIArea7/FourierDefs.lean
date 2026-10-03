import Mathlib
import Submission.Work.FIArea7.SepK

/-!
# Building blocks for the `L¹` bound of the separating function (*FI* Lemma 26.1)

* `cRho s = ∫ u, cos (2πus) · ρ(u)` — the cosine Fourier transform of the flat-topped density
  `sepRho` (`∫ ρ = 1`, `∫ |ρ'| = 16/15`);
* `boxK lam` — the indicator function of the interval `[-lam, lam]`.

The smooth trapezoid `sepK lam eps` is the convolution of `boxK lam` with the dilated density
`ρ(·/eps)`, and this is how the Fourier transform of `sepK` is computed.
-/

namespace Work.FIArea7

open MeasureTheory intervalIntegral Real Complex Filter
open scoped Topology FourierTransform

noncomputable section

/-- The cosine transform of the flat-topped density `sepRho`:
`cRho s = ∫ u, cos (2 * π * u * s) * sepRho u`. -/
noncomputable def cRho (s : ℝ) : ℝ := ∫ u : ℝ, Real.cos (2 * Real.pi * u * s) * sepRho u

/-- The indicator function of the interval `[-lam, lam]`. -/
noncomputable def boxK (lam : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc (-lam) lam) (fun _ => (1 : ℝ))

end

end Work.FIArea7
