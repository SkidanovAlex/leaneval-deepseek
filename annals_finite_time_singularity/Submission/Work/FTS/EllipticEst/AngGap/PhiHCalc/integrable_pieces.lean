import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.FTS.EllipticEst.AngGap.HardySetup
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngGap.PhiHCalc

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Interval-integrability of the three pieces of the Hardy integrand.**

With `h` of class `C²` on `[0, π/2]`, `|h θ| ≤ C sin 2θ`, `|angG h θ| ≤ C (sin 2θ)³`, and
`angG h` differentiable with derivative `h θ sin 2θ` on `(0, π/2)` (so that
`angV h = angG h / sin 2θ` is continuous there), the functions

* `θ ↦ (h θ)²`,
* `θ ↦ (angV h θ)²`,
* `angFt h = θ ↦ (h θ - 6 cot(2θ) angV h θ)²`

are all interval-integrable on `0..π/2`.  Each of them is continuous on `(0, π/2)` and
bounded there (`|h θ| ≤ C sin 2θ ≤ C`, `|V θ| ≤ C sin²2θ ≤ C`, and
`|6 cot(2θ) V θ| ≤ 6 C sin 2θ ≤ 6C`, so `|h - 6 cot 2θ V| ≤ 7C`), and `(0, π/2)` has finite
measure; alternatively `h²` is even continuous on the closed interval.  This is what
allows the integral of `angF h = (h² - 12 V²) - angFt h` to be split. -/
theorem integrable_pieces (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    IntervalIntegrable (fun θ => (h θ) ^ 2) MeasureTheory.volume 0 (Real.pi / 2)
      ∧ IntervalIntegrable (fun θ => (Work.FTS.EllipticEst.AngGap.angV h θ) ^ 2)
          MeasureTheory.volume 0 (Real.pi / 2)
      ∧ IntervalIntegrable (Work.FTS.EllipticEst.AngGap.angFt h)
          MeasureTheory.volume 0 (Real.pi / 2) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  -- Elementary consequences of the two bounds on `h` and `angG h`.
  have hbddC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h θ| ≤ C := by
    intro θ hθ
    have hmem : 2 * θ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsnn : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc hmem
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    calc |h θ| ≤ C * Real.sin (2 * θ) := hbdd θ (hsub hθ)
      _ ≤ C * 1 := by nlinarith
      _ = C := by ring
  have hVbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |angV h θ| ≤ C := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hV1 : |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
      have hG := hCg θ (hsub hθ)
      rw [angV, abs_div, abs_of_pos hs, div_le_iff₀ hs]
      calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := hG
        _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring
    have hmem : 2 * θ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsnn : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc hmem
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by nlinarith
    nlinarith [hV1, hC]
  have hFtbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |angFt h θ| ≤ (7 * C) ^ 2 := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hmem : 2 * θ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hA : |h θ| ≤ C := hbddC θ hθ
    have hV1 : |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
      have hG := hCg θ (hsub hθ)
      rw [angV, abs_div, abs_of_pos hs, div_le_iff₀ hs]
      calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := hG
        _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring
    have hcot := abs_cot_two_le hθ
    have hcotV : |Real.cot (2 * θ) * angV h θ| ≤ C * Real.sin (2 * θ) := by
      rw [abs_mul]
      calc |Real.cot (2 * θ)| * |angV h θ|
            ≤ (1 / Real.sin (2 * θ)) * (C * (Real.sin (2 * θ)) ^ 2) :=
            mul_le_mul hcot hV1 (abs_nonneg _) (by positivity)
        _ = C * Real.sin (2 * θ) := by field_simp
    have hB : |6 * Real.cot (2 * θ) * angV h θ| ≤ 6 * C := by
      have h6 : |(6 : ℝ)| = 6 := by norm_num
      rw [show (6 : ℝ) * Real.cot (2 * θ) * angV h θ
            = 6 * (Real.cot (2 * θ) * angV h θ) by ring, abs_mul, h6]
      calc 6 * |Real.cot (2 * θ) * angV h θ| ≤ 6 * (C * Real.sin (2 * θ)) := by
            linarith [hcotV]
        _ = 6 * C * Real.sin (2 * θ) := by ring
        _ ≤ 6 * C * 1 := mul_le_mul_of_nonneg_left hs1 (by linarith)
        _ = 6 * C := by ring
    have hX : |h θ - 6 * Real.cot (2 * θ) * angV h θ| ≤ 7 * C := by
      have hsub' := abs_sub_le (h θ) 0 (6 * Real.cot (2 * θ) * angV h θ)
      simp only [sub_zero, zero_sub, abs_neg] at hsub'
      calc |h θ - 6 * Real.cot (2 * θ) * angV h θ|
            ≤ |h θ| + |6 * Real.cot (2 * θ) * angV h θ| := hsub'
        _ ≤ C + 6 * C := add_le_add hA hB
        _ = 7 * C := by ring
    rw [angFt, abs_of_nonneg (sq_nonneg _)]
    calc (h θ - 6 * Real.cot (2 * θ) * angV h θ) ^ 2
          = |h θ - 6 * Real.cot (2 * θ) * angV h θ| ^ 2 := by rw [sq_abs]
      _ ≤ (7 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hX 2
  -- Continuity on the open interval.
  have hcontG : ContinuousOn (angG h) (Set.Ioo 0 (Real.pi / 2)) :=
    fun θ hθ => (hg θ hθ).continuousAt.continuousWithinAt
  have hcontsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontV : ContinuousOn (angV h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContinuousOn (fun θ => angG h θ / Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2))
    exact hcontG.div hcontsin (fun θ hθ => ne_of_gt (sin_two_pos hθ))
  have hcontcot : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    fun θ hθ => (hasDerivAt_cot_two θ hθ).continuousAt.continuousWithinAt
  have hcontFt : ContinuousOn (angFt h) (Set.Ioo 0 (Real.pi / 2)) := by
    have hprod : ContinuousOn (fun θ : ℝ => 6 * Real.cot (2 * θ) * angV h θ)
        (Set.Ioo 0 (Real.pi / 2)) := (continuousOn_const.mul hcontcot).mul hcontV
    show ContinuousOn (fun θ => (h θ - 6 * Real.cot (2 * θ) * angV h θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2))
    exact ((hh.continuousOn.mono hsub).sub hprod).pow 2
  refine ⟨?_, ?_, ?_⟩
  · exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (g := fun θ => (h θ) ^ 2) hpi.le ((hh.continuousOn.mono hsub).pow 2) (C ^ 2)
      (fun θ hθ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (h θ)) (hbddC θ hθ) 2)
  · exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (g := fun θ => angV h θ ^ 2) hpi.le (hcontV.pow 2) (C ^ 2)
      (fun θ hθ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (angV h θ)) (hVbdd θ hθ) 2)
  · exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (g := angFt h) hpi.le hcontFt ((7 * C) ^ 2) hFtbdd

end Work.FTS.EllipticEst.AngGap.PhiHCalc
