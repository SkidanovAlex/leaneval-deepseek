/-
Copyright: work module for the Elgindi finite-time singularity project.

# The wild angular integration by parts with the weight `sin(2θ)^p`

For `p < 1` and `g` of class `C²` on the open interval `(0, π/2)`, with the four weighted
integrability hypotheses on `Iθ = [0, π/2]`

  `(g')² sin^p`, `g² sin^p`, `g g'' sin^p`, `g² cot²(2θ) sin^p`

and with the boundary flux

  `F(θ) = sin(2θ)^p (g g' - p cot(2θ) g²) = g g' sin(2θ)^p - p cos(2θ) sin(2θ)^{p-1} g²`

vanishing (in the sense of one-sided limits) at `θ → 0⁺` and `θ → (π/2)⁻`, we have

  `∫_{Iθ} (g')² sin^p = - ∫_{Iθ} g g'' sin^p - 2p ∫_{Iθ} g² sin^p
      - 2p(1-p) ∫_{Iθ} g² cot²(2θ) sin^p`.

The proof is the fundamental theorem of calculus applied to the primitive `F` on `(0, π/2)`:
its derivative (computed in `Prop.angIbpPrimDeriv`) is exactly the four-term integrand, and
the two one-sided limits of `F` vanish (rewritten in `Prop.angIbpPrimBoundary` from the two
Tendsto hypotheses `hf0`/`hf1`).  Hence `∫_{0}^{π/2} F' = 0`; splitting this integral into
its four pieces and rewriting the interval integrals as integrals over `Iθ` gives the claim.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Prop.angIbpPrimDeriv
import Submission.Work.FTS.EllipticEst.Prop.angIbpPrimBoundary

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

-- The exponent hypothesis `p < 1` is part of the statement but is not needed by the proof
-- (the boundary conditions are hypotheses, so the identity is a formal consequence of them).
set_option linter.unusedVariables false in

theorem angIbpWild {p : ℝ} (hp : p < 1) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hI : MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ)
    (hP : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ)
    (hJ : MeasureTheory.IntegrableOn (fun θ => g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ)
    (hC : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ)
    (hf0 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ p * (g θ * deriv g θ
      - p * Real.cot (2 * θ) * (g θ) ^ 2)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hf1 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ p * (g θ * deriv g θ
      - p * Real.cot (2 * θ) * (g θ) ^ 2)) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
      = - (∫ θ in Work.Spaces.Iθ, g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p)
        - 2 * p * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
        - 2 * p * (1 - p) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  -- Set integrals over `Iθ = [0, π/2]` are interval integrals over `0..π/2`.
  have hconv : ∀ u : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, u θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), u θ := by
    intro u
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  -- The four weighted integrands are interval integrable on `0..π/2`.
  have hintA : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
      volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr (hI.mono_set Set.Ioc_subset_Icc_self)
  have hintB : IntervalIntegrable (fun θ : ℝ => g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p)
      volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr (hJ.mono_set Set.Ioc_subset_Icc_self)
  have hintC : IntervalIntegrable (fun θ : ℝ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
      volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr (hP.mono_set Set.Ioc_subset_Icc_self)
  have hintD : IntervalIntegrable (fun θ : ℝ => (g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ p) volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr (hC.mono_set Set.Ioc_subset_Icc_self)
  -- ... so is their combination, the derivative of the primitive.
  have hcomb : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p
      + g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p
      + 2 * p * ((g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
      + 2 * p * (1 - p) * ((g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p))
      volume (0 : ℝ) (Real.pi / 2) :=
    ((hintA.add hintB).add (hintC.const_mul (2 * p))).add (hintD.const_mul (2 * p * (1 - p)))
  -- The pointwise derivative of the primitive on the open interval.
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => g t * deriv g t * (Real.sin (2 * t)) ^ p
        - p * Real.cos (2 * t) * (Real.sin (2 * t)) ^ (p - 1) * (g t) ^ 2)
      ((deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p
        + g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p
        + 2 * p * ((g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
        + 2 * p * (1 - p) * ((g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p)) θ := by
    intro θ hθ
    have h := angIbpPrimDeriv p g hg hθ
    simpa only using h
  -- The two one-sided limits of the primitive vanish.
  obtain ⟨hb0, hb1⟩ := angIbpPrimBoundary p g
  -- Fundamental theorem of calculus.
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), ((deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p
      + g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p
      + 2 * p * ((g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
      + 2 * p * (1 - p) * ((g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p))) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hcomb
      (hb0 hf0) (hb1 hf1)
    simpa using h
  -- The same statement over the set `Iθ`.
  have hFTCI : (∫ θ in Work.Spaces.Iθ, ((deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p
      + g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p
      + 2 * p * ((g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
      + 2 * p * (1 - p) * ((g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p))) = 0 := by
    rw [hconv]; exact hFTC
  -- Split the combined integral into its four pieces.
  have hsplitI : (∫ θ in Work.Spaces.Iθ, ((deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p
      + g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p
      + 2 * p * ((g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
      + 2 * p * (1 - p) * ((g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p)))
      = (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
        + (∫ θ in Work.Spaces.Iθ, g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p)
        + 2 * p * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
        + 2 * p * (1 - p) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p) := by
    rw [hconv (fun θ => ((deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p
          + g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p
          + 2 * p * ((g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
          + 2 * p * (1 - p) * ((g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p))),
        hconv (fun θ => (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p),
        hconv (fun θ => g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p),
        hconv (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ p),
        hconv (fun θ => (g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p)]
    rw [intervalIntegral.integral_add ((hintA.add hintB).add (hintC.const_mul (2 * p)))
          (hintD.const_mul (2 * p * (1 - p))),
        intervalIntegral.integral_add (hintA.add hintB) (hintC.const_mul (2 * p)),
        intervalIntegral.integral_add hintA hintB,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  linarith [hFTCI, hsplitI]

end Work.FTS.EllipticEst.Prop
