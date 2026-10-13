import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.Honest.HonSliceAbsLe
import Submission.Work.FTS.H2.STBasic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

theorem sliceBoundsOfTraceFts {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) := by
  -- The weight `sin (2θ)^{-η}` is `≥ 1` on the open interval, so the hypothesis is stronger
  -- than the plain square-integrability of `f''`: `f'` (and `f`) are bounded.
  obtain ⟨C, hC0, hC⟩ := Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hf h2
  have hbd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C := fun θ hθ => (hC θ hθ).2
  -- The two endpoint limits turn the Lipschitz bound on `f` into the decay
  -- `|f θ| ≤ C·min θ (π/2 - θ)`.
  obtain ⟨hleft, hright⟩ := Work.FTS.EllipticEst.Honest.HonSliceAbsLe C hC0 f hf h0 hπ hbd
  refine ⟨C, hC0, ?_, hbd⟩
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_Iθ hθI
  -- `min θ (π/2 - θ) ≤ (π/4)·sin (2θ)`, from `sin (2θ) ≥ (4/π)·min θ (π/2 - θ)`.
  have hmin : min θ (Real.pi / 2 - θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
    have h := Work.FTS.H2.sin_two_ge_min θ hθI
    have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ Real.pi / 4 by positivity)
    have he : (Real.pi / 4) * ((4 / Real.pi) * min θ (Real.pi / 2 - θ))
        = min θ (Real.pi / 2 - θ) := by
      field_simp
    linarith [h', he.symm.le]
  calc |f θ| ≤ min (C * θ) (C * (Real.pi / 2 - θ)) := le_min (hleft θ hθ) (hright θ hθ)
    _ = C * min θ (Real.pi / 2 - θ) :=
        (mul_min_of_nonneg θ (Real.pi / 2 - θ) hC0).symm
    _ ≤ C * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hmin hC0
    _ = (C * (Real.pi / 4)) * Real.sin (2 * θ) := by ring
    _ ≤ C * Real.sin (2 * θ) := by
        apply mul_le_mul_of_nonneg_right _ hsin
        nlinarith [hC0, Real.pi_lt_four]

end Work.FTS.EllipticEst.TT
