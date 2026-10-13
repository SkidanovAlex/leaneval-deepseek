/-
# `eFam_residual_integrable` — the residual of the finite mode truncation is `L²(Iθ, cos θ dθ)`

Given a slice `θ ↦ F z θ` which is a.e. strongly measurable and whose weighted square
`θ ↦ F z θ ^ 2 * cos θ` is integrable on `Iθ`, the residual of the truncation of `F z` at the
first `N + 1` Dirichlet modes `eFam m` (with coefficients `cmode m F z`),

  `θ ↦ (F z θ - ∑_{m ≤ N} cmode m F z · eFam m θ) ^ 2 * cos θ`,

is again integrable on `Iθ`.

This is immediate from the pointwise inequality `(a - b)² ≤ 2a² + 2b²` together with the
boundedness of the finite mode sum (a finite sum of continuous functions, on the compact
interval `Iθ`) and Mathlib's domination criterion `Integrable.mono'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option linter.style.haveILetI false

/-- The truncated mode sum `θ ↦ ∑_{m ≤ N} c_m · eFam m θ` is continuous. -/
lemma continuous_modeSum (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) :
    Continuous (fun θ : ℝ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m F z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  refine continuous_finsetSum _ (fun m _ => ?_)
  exact continuous_const.mul (continuous_eFam m)

theorem eFam_residual_integrable (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (F z θ - ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.cmode m F z *
          Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ := by
  let S : ℝ → ℝ := fun θ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m F z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ
  have hScont : Continuous S := continuous_modeSum F z N
  change MeasureTheory.IntegrableOn
    (fun θ => (F z θ - S θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := isFiniteMeasure_Iθ
  have hK : IsCompact Work.Spaces.Iθ := isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := S) hScont.continuousOn
  have hMabs : ∀ θ ∈ Work.Spaces.Iθ, |S θ| ≤ M := fun θ hθ => by
    simpa only [Real.norm_eq_abs] using hM θ hθ
  have hMnonneg : 0 ≤ M := by
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by positivity⟩
    exact le_trans (abs_nonneg (S 0)) (hMabs 0 h0)
  refine MeasureTheory.Integrable.mono'
    (g := fun θ => 2 * (F z θ ^ 2 * Real.cos θ) + 2 * M ^ 2) ?_ ?_ ?_
  · exact (hz.const_mul 2).add (integrable_const (2 * M ^ 2))
  · exact ((hmeas.sub hScont.aestronglyMeasurable).pow 2).mul
      Real.continuous_cos.aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
    filter_upwards with θ hθ
    have hcos0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hSabs : |S θ| ≤ M := hMabs θ hθ
    have hSsq : S θ ^ 2 ≤ M ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hMnonneg]
      exact hSabs
    have hkey : (F z θ - S θ) ^ 2 ≤ 2 * F z θ ^ 2 + 2 * S θ ^ 2 := by
      nlinarith [sq_nonneg (F z θ + S θ)]
    rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs, abs_of_nonneg hcos0]
    have h2 : (F z θ - S θ) ^ 2 * Real.cos θ
        ≤ (2 * F z θ ^ 2 + 2 * S θ ^ 2) * Real.cos θ :=
      mul_le_mul_of_nonneg_right hkey hcos0
    have h3 : (2 * F z θ ^ 2 + 2 * S θ ^ 2) * Real.cos θ
        = 2 * (F z θ ^ 2 * Real.cos θ) + 2 * (S θ ^ 2 * Real.cos θ) := by ring
    have h4 : 2 * (S θ ^ 2 * Real.cos θ) ≤ 2 * M ^ 2 := by
      nlinarith [hSsq, hcos0, hcos1, sq_nonneg (S θ)]
    linarith

end Work.EllipticEst.ModalSolution
