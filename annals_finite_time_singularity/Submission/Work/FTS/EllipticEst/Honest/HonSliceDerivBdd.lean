import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv
import Submission.Work.FTS.EllipticEst.Honest.csIntegralSqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory

/-- On `(0, π/2)` we have `0 < sin (2θ) ≤ 1`, hence `sin (2θ) ^ (-η) ≥ 1` for every
`η ≥ 0`. -/
theorem one_le_sin_two_rpow_eta0 {η : ℝ} (hη0 : 0 ≤ η) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ (Real.sin (2 * θ)) ^ (-η) := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hz : -η ≤ 0 := by linarith
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1 hz
  simpa [Real.rpow_zero] using h

/-- A function `g` that is continuous on the open interval `(0, π/2)` and whose square,
weighted by the (non-singular, `≥ 1`) factor `sin (2θ) ^ (-η)`, is integrable there, is
itself integrable there: `|g| ≤ g² + 1` and the interval has finite length. -/
theorem integrableOn_of_sq_mul_sin_two_rpow {η : ℝ} (hη0 : 0 ≤ η) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsaesm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  simp only [MeasureTheory.IntegrableOn] at hint ⊢
  -- `g²` is integrable, because `g² ≤ g² · sin (2θ) ^ (-η)` on the interval.
  have hsq_int : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine hint.mono' (hsaesm.pow 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-η) := one_le_sin_two_rpow_eta0 hη0 hθ
    have hsq : 0 ≤ (g θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq]
    simpa using mul_le_mul_of_nonneg_left h1 hsq
  -- `|g| ≤ g² + 1` with `g² + 1` integrable on the finite interval.
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 + 1)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsq_int.add (MeasureTheory.integrable_const (1 : ℝ))
  refine hmaj.mono' hsaesm ?_
  filter_upwards with θ
  have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|g θ| - 1 / 2), sq_abs (g θ), abs_nonneg (g θ)]
  simpa only [Real.norm_eq_abs] using h1

theorem HonSliceDerivBdd (η : ℝ) (hη0 : 0 ≤ η) : ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C := by
  intro f hf hint
  -- `deriv f` is `C¹` and `deriv (deriv f)` is continuous on the open interval.
  have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : ContDiffOn ℝ 0 (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont : ContinuousOn (fun θ => deriv (deriv f) θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h2.continuousOn
  -- the weight is `≥ 1`, so the hypothesis gives honest integrability of `deriv (deriv f)`.
  have hInt : MeasureTheory.IntegrableOn (deriv (deriv f))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_of_sq_mul_sin_two_rpow hη0 hcont hint
  -- and `deriv f` is differentiable on the interval with derivative `deriv (deriv f)`.
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x hx =>
    ((h1.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  exact bdd_of_integrableOn_deriv (by linarith [Real.pi_pos]) hderiv hInt

end Work.FTS.EllipticEst.Honest
