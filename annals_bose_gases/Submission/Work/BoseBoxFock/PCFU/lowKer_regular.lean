import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dictBricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.lowKer_regular`

The position-space kernel `Κ(z) = (2π)^{-3}∫_p f(‖p‖/κ)cos⟪p,z⟫` of the low-momentum
multiplier `f(‖p‖/κ)` (FS's `f_L(√−Δ)`, see `PCFU/dictBricks.lean`) is continuous in `z`
and bounded on `ℝ³`.

Both facts are elementary, from the two structural properties of FS's cutoff `f`
(`Work.BoseBoxFix.LowCut`): `f` is antitone with `f = 1` on `(-∞,1]` and `f = 0` on `[2,∞)`,
so `0 ≤ f ≤ 1` and `f` vanishes on `‖p‖ ≥ 2κ` — the integrand is supported in the ball
`‖p‖ < 2κ`, of finite measure.  Continuity is dominated convergence in `z` with majorant
`1` on that ball; boundedness is `|∫| ≤ ∫|·| ≤ ∫ 1 = vol(ball)`.
-/

noncomputable section
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- FS's cutoff is nonnegative: it is `1` on `(-∞,1]` and `0` on `[2,∞)`, and antitone. -/
private lemma lowCut_f_nonneg (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : 0 ≤ fc.f s := by
  rcases le_or_gt s 2 with h | h
  · have := fc.anti h
    rwa [fc.zero 2 le_rfl] at this
  · rw [fc.zero s h.le]

/-- FS's cutoff is at most `1`. -/
private lemma lowCut_f_le_one (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : fc.f s ≤ 1 := by
  rcases le_or_gt s 1 with h | h
  · rw [fc.one s h]
  · have := fc.anti h.le
    rwa [fc.one 1 le_rfl] at this

/-- **`lowKer` is continuous and bounded.**  The integrand `f(‖p‖/κ)cos⟪p,z⟫` is dominated by
`1_{‖p‖ < 2κ}` (as `f(‖p‖/κ) = 0` for `‖p‖ ≥ 2κ` and `|f| ≤ 1` everywhere), which is
integrable; hence `z ↦ ∫_p ...` is continuous, and its sup is at most the volume of the ball
`‖p‖ < 2κ`. -/
theorem lowKer_regular (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    Continuous (Work.BoseBoxFock.PCFU.lowKer fc κ) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
        |Work.BoseBoxFock.PCFU.lowKer fc κ z| ≤ C := by
  have h2κ : (0 : ℝ) < 2 * κ := by linarith
  set s : Set E3 := Metric.ball 0 (2 * κ) with hs
  have hfin : (volume : Measure E3) s ≠ ⊤ := by
    have h1 : IsCompact (Metric.closedBall (0 : E3) (2 * κ)) := isCompact_closedBall 0 (2 * κ)
    have h2 : (volume : Measure E3) (Metric.closedBall (0 : E3) (2 * κ)) < ⊤ := h1.measure_lt_top
    have h3 : s ⊆ Metric.closedBall (0 : E3) (2 * κ) := by
      rw [hs]; exact Metric.ball_subset_closedBall
    exact ne_top_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono h3) h2)
  have honeint : Integrable (fun _ : E3 => (1 : ℝ)) (volume.restrict s) :=
    MeasureTheory.integrableOn_const hfin (by simp)
  have hcz : ∀ z, Continuous fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z) := fun z =>
    (fc.smooth.continuous.comp (continuous_norm.div_const κ)).mul
      (Real.continuous_cos.comp (continuous_id.inner continuous_const))
  have hzp : ∀ p, Continuous fun z : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z) := fun p =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))
  have hpt : ∀ (p z : E3), |fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)| ≤ (1 : ℝ) := by
    intro p z
    rw [abs_mul]
    have h1 : |fc.f (‖p‖ / κ)| ≤ 1 := by
      rw [abs_of_nonneg (lowCut_f_nonneg fc _)]; exact lowCut_f_le_one fc _
    calc |fc.f (‖p‖ / κ)| * |Real.cos (inner ℝ p z)| ≤ 1 * 1 :=
          mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have hle : ∀ (p z : E3), ‖fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)‖ ≤ (1 : ℝ) := by
    intro p z; rw [Real.norm_eq_abs]; exact hpt p z
  -- the kernel is the Fourier-type integral over the ball `‖p‖ < 2κ`
  have hker : ∀ z : E3, Work.BoseBoxFock.PCFU.lowKer fc κ z
      = ((2 * Real.pi) ^ 3)⁻¹
          * ∫ p in s, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z) := by
    intro z
    simp only [Work.BoseBoxFock.PCFU.lowKer]
    congr 1
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro p hp
    have hp2 : 2 * κ ≤ ‖p‖ := by
      have : ¬ (‖p‖ < 2 * κ) := by
        intro hlt
        exact hp (by rw [hs, Metric.mem_ball, dist_zero_right]; exact hlt)
      linarith
    have h2 : (2 : ℝ) ≤ ‖p‖ / κ := by
      rw [le_div_iff₀ hκ]; linarith
    rw [fc.zero (‖p‖ / κ) h2, zero_mul]
  -- continuity of the integral in `z`, by dominated convergence on the finite ball
  have hcontInt : Continuous
      (fun z : E3 => ∫ p in s, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)) := by
    show Continuous
      (fun z : E3 => ∫ p, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z) ∂(volume.restrict s))
    exact MeasureTheory.continuous_of_dominated (μ := volume.restrict s)
      (F := fun z p => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)) (bound := fun _ => (1 : ℝ))
      (fun z => (hcz z).aestronglyMeasurable)
      (fun z => Filter.Eventually.of_forall fun p => hle p z)
      honeint
      (Filter.Eventually.of_forall fun p => hzp p)
  -- the uniform bound
  have hbdInt : ∀ z : E3,
      |∫ p in s, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)| ≤ (volume s).toReal := by
    intro z
    have h1 : |∫ p in s, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)|
        ≤ ∫ p in s, |fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)| := by
      show |∫ p, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z) ∂(volume.restrict s)|
        ≤ ∫ p, |fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)| ∂(volume.restrict s)
      simpa using MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict s) (fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z))
    have h2 : ∫ p in s, |fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)| ≤ ∫ p in s, (1 : ℝ) := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun p => abs_nonneg _
      · exact honeint
      · exact Filter.Eventually.of_forall fun p => hpt p z
    have h3 : ∫ p in s, (1 : ℝ) = (volume s).toReal := by
      rw [MeasureTheory.setIntegral_const, Measure.real_def]; ring
    linarith
  have hcpos : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  constructor
  · have heq : Work.BoseBoxFock.PCFU.lowKer fc κ
        = fun z : E3 => ((2 * Real.pi) ^ 3)⁻¹
            * ∫ p in s, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z) :=
      funext hker
    rw [heq]
    exact hcontInt.const_mul _
  · refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (volume s).toReal, ?_, ?_⟩
    · exact mul_nonneg (le_of_lt hcpos) ENNReal.toReal_nonneg
    · intro z
      rw [hker z, abs_mul, abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_left (hbdInt z) (le_of_lt hcpos)

end Work.BoseBoxFock.PCFU
