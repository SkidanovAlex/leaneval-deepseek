import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory Set

/-- **The first derivative is integrable in the light weight's dual.**

If `∫_{Iθ} (∂_θ f)² sin(2θ)^a < ∞` with `0 < a < 1`, then `∂_θ f` itself is integrable on
`Ioo 0 (π/2)` — and hence on every subinterval contained in it.

The point is the pointwise AM–GM inequality
`|∂_θf| = |∂_θf · sin(2θ)^{a/2}| · sin(2θ)^{-a/2} ≤ ½ (∂_θf)² sin(2θ)^a + ½ sin(2θ)^{-a}`
together with the `rpow`-integrability of `sin(2θ)^{-a}` on `Iθ` (`Work.Spaces.sin_two_rpow`),
which holds exactly because `a < 1`. -/
theorem lightDerivIntegrable (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a) (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    (∀ a' b' : ℝ, Set.Ioo a' b' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ) (Set.Ioo a' b')) := by
  -- The dual weight `sin(2θ)^{-a}` is integrable; this is where `a < 1` is used.
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact Set.Ioo_subset_Icc_self
  have hB : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-a))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Work.Spaces.sin_two_rpow (-a) (by linarith) (by linarith)).1.mono_set hsub
  -- The dominating integrable function.
  have hsum : MeasureTheory.Integrable
      (fun θ : ℝ => (1 / 2) * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a)
        + (1 / 2) * (Real.sin (2 * θ)) ^ (-a))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have h1 : MeasureTheory.Integrable
        (fun θ : ℝ => (1 / 2) * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hint.const_mul (1 / 2)
    have h2 : MeasureTheory.Integrable
        (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ)) ^ (-a))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hB.const_mul (1 / 2)
    exact h1.add h2
  have hmain : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' hsum ((measurable_deriv f).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs]
    have ht : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsq1 : ((Real.sin (2 * θ)) ^ (a / 2)) ^ 2 = (Real.sin (2 * θ)) ^ a := by
      rw [sq, ← Real.rpow_add ht]; congr 1; ring
    have hsq2 : ((Real.sin (2 * θ)) ^ (-(a / 2))) ^ 2 = (Real.sin (2 * θ)) ^ (-a) := by
      rw [sq, ← Real.rpow_add ht]; congr 1; ring
    have hprod : (Real.sin (2 * θ)) ^ (a / 2) * (Real.sin (2 * θ)) ^ (-(a / 2)) = 1 := by
      rw [← Real.rpow_add ht, show a / 2 + -(a / 2) = 0 by ring, Real.rpow_zero]
    have hmul : (|deriv f θ| * (Real.sin (2 * θ)) ^ (a / 2))
        * ((Real.sin (2 * θ)) ^ (-(a / 2))) = |deriv f θ| := by
      rw [mul_assoc, hprod, mul_one]
    have hA2 : (|deriv f θ| * (Real.sin (2 * θ)) ^ (a / 2)) ^ 2
        = (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a := by
      rw [mul_pow, sq_abs, hsq1]
    have h := two_mul_le_add_sq (|deriv f θ| * (Real.sin (2 * θ)) ^ (a / 2))
      ((Real.sin (2 * θ)) ^ (-(a / 2)))
    rw [mul_assoc, hmul, hA2, hsq2] at h
    linarith
  exact ⟨hmain, fun a' b' hs => hmain.mono_set hs⟩

end Work.FTS.EllipticEst.TT
