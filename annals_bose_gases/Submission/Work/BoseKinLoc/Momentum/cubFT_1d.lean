import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseKinLoc.Momentum.cubFT_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The 1D factors of the unit-cube Fourier transform

This module fixes the one-dimensional quantities into which the unit-cube Fourier symbol
`cubFT` (and its exterior decay bounds, `Work.BoseKinLoc.Momentum.cubFT_exterior_bounds`)
factor.  With `acube 1 = [-1/2,1/2]³` one has

    `cubFT q = ∏ i, hFT (q i)`,   `hFT t = ∫_{-1/2}^{1/2} cos (t s) ds`,

and the coordinate derivatives are

    `fderiv ℝ cubFT q (kcStdBasis i) = -(mFT (q i)) * ∏ j ≠ i, hFT (q j)`,

with `mFT t = ∫_{-1/2}^{1/2} s sin (t s) ds`.

The elementary 1D estimates (proved elsewhere, using the explicit antiderivatives
`∫ cos (t s) ds = 2 sin (t/2)/t` and `∫ s sin (t s) ds = (2 sin (t/2) - t cos (t/2))/t²`) are

    `|hFT t| ≤ 1`,  `|t * hFT t| ≤ 2`,  `|mFT t| ≤ 1/2`,  `|t * mFT t| ≤ 2`,

so that `(hFT t)² ≤ Fdom t` and `(mFT t)² ≤ Gdom t` off the single point `t = 0`, where
`Fdom t = min 1 (4/t²)` and `Gdom t = min (1/2) (4/t²)` are the (integrable, explicit) dominating
functions used to bound the exterior integrals.  They are declared here so that the several
independent estimates about them can be stated and proved separately.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

set_option autoImplicit false

/-- `hFT t = ∫_{-1/2}^{1/2} cos (t s) ds`: the one-dimensional factor of `cubFT`. -/
def hFT (t : ℝ) : ℝ := ∫ s in Set.Icc (-(1/2)) (1/2), Real.cos (t * s)

/-- `mFT t = ∫_{-1/2}^{1/2} s sin (t s) ds`: the sine moment in the 1D factor, i.e.
`- d/dt (hFT t)`. -/
def mFT (t : ℝ) : ℝ := ∫ s in Set.Icc (-(1/2)) (1/2), s * Real.sin (t * s)

/-- The complex 1D factor `chFT t = ∫_{-1/2}^{1/2} e^{i t s} ds`. -/
def chFT (t : ℝ) : ℂ :=
  ∫ s in Set.Icc (-(1/2)) (1/2), Complex.exp (Complex.I * ((t * s : ℝ) : ℂ))

/-- The dominating function `Fdom t = min 1 (4/t²)` for `(hFT t)²`. -/
def Fdom (t : ℝ) : ℝ := min 1 (4 / t ^ 2)

/-- The dominating function `Gdom t = min (1/2) (4/t²)` for `(mFT t)²`. -/
def Gdom (t : ℝ) : ℝ := min (1/2) (4 / t ^ 2)

lemma Fdom_nonneg (t : ℝ) : 0 ≤ Fdom t := le_min (by norm_num) (by positivity)

lemma Gdom_nonneg (t : ℝ) : 0 ≤ Gdom t := le_min (by norm_num) (by positivity)

lemma Fdom_le_one (t : ℝ) : Fdom t ≤ 1 := min_le_left _ _

lemma Gdom_le_half (t : ℝ) : Gdom t ≤ 1 / 2 := min_le_left _ _

/-- The Euclidean norm square as a coordinate sum (L² norm on `EuclideanSpace ℝ (Fin 3)`). -/
lemma euclidean_norm_sq (q : EuclideanSpace ℝ (Fin 3)) : ‖q‖ ^ 2 = ∑ i, (q i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.inner_apply, sq]

/-- `hFT 0 = 1`. -/
lemma hFT_zero : hFT 0 = 1 := by
  have h1 : (fun s : ℝ => Real.cos ((0 : ℝ) * s)) = fun _ => (1 : ℝ) := by
    funext s; simp
  rw [hFT, h1, setIntegral_const]
  show (volume (Set.Icc (-(1/2)) (1/2))).toReal • (1 : ℝ) = 1
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2 - -(1 / 2))]
  norm_num

/-- `mFT 0 = 0`. -/
lemma mFT_zero : mFT 0 = 0 := by
  have h1 : (fun s : ℝ => s * Real.sin ((0 : ℝ) * s)) = fun _ => (0 : ℝ) := by
    funext s; simp
  rw [mFT, h1, integral_zero]

end Work.BoseKinLoc.Momentum
