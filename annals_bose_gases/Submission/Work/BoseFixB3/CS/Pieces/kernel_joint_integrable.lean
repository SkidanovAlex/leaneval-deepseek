import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.kernel_joint_integrable`

The joint (in `(p,z)`) integrand of the low-momentum kernel

`(p,z) ↦ e^{i⟪p,x⟫} f(‖p‖/κ) e^{-i⟪p,z⟫} · 1_s ψ(z)`

is `L¹(ℝ³ × ℝ³)`.  Two facts make this true:

* the `p`-factor `f(‖p‖/κ)` is supported in the ball `B(0,2κ)` and the `z`-factor
  `1_sψ` is supported in `s`, so the integrand is supported in the finite-measure set
  `B(0,2κ) ×ˢ s`;
* on that set the integrand is bounded by `C` (`‖exp(iθ)‖ = 1`, `‖f‖ ≤ 1` and
  `|ψ| ≤ C` on `s`).

Both are the standard `Integrable.mono'`-with-a-supported-bound argument; the only
point needing care is that the `f`-values all lie in `[0,1]`, which follows from
antitonicity of `fc.f` together with `f = 1` below `1` and `f = 0` above `2`.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Filter Metric
open scoped Real Topology

noncomputable section

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-- `fc.f` is nonnegative: it vanishes above `2` and is non-increasing. -/
private lemma lowCut_nonneg (fc : Work.BoseBoxFix.LowCut) (t : ℝ) : 0 ≤ fc.f t := by
  by_cases h : t ≤ 2
  · have := fc.anti h
    rwa [fc.zero 2 le_rfl] at this
  · rw [fc.zero t (le_of_lt (not_le.mp h))]

/-- `fc.f` is at most `1`: it equals `1` below `1` and is non-increasing. -/
private lemma lowCut_le_one (fc : Work.BoseBoxFix.LowCut) (t : ℝ) : fc.f t ≤ 1 := by
  by_cases h : 1 ≤ t
  · have := fc.anti h
    rwa [fc.one 1 le_rfl] at this
  · rw [fc.one t (le_of_lt (not_le.mp h))]

/-- Norm of a real number viewed in `ℂ`. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- The cut-off function of `fc` takes values in `[0,1]`. -/
private lemma abs_lowCut_le_one (fc : Work.BoseBoxFix.LowCut) (t : ℝ) : |fc.f t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [lowCut_nonneg fc t], lowCut_le_one fc t⟩

/-- `‖e^{-iy}‖ = 1` for real `y`. -/
private lemma norm_exp_neg_I_mul_ofReal (y : ℝ) : ‖Complex.exp (-(Complex.I * (y : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (-(Complex.I * (y : ℂ))).re = 0 := by
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [h, Real.exp_zero]

theorem kernel_joint_integrable {fc : Work.BoseBoxFix.LowCut} {κ C : ℝ}
    (hκ : 0 < κ) {s : Set (EuclideanSpace ℝ (Fin 3))} (hs : MeasurableSet s)
    (hsf : MeasureTheory.volume s < ⊤)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψm : MeasureTheory.AEStronglyMeasurable ψ MeasureTheory.volume)
    (hψb : ∀ z ∈ s, |ψ z| ≤ C) (hC : 0 ≤ C) (x : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (Function.uncurry fun p z : EuclideanSpace ℝ (Fin 3) =>
        (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) * (((s.indicator ψ z : ℝ) : ℂ)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  -- the set on which the integrand lives: `B(0,2κ) × s`
  have hTfin : (MeasureTheory.volume.prod MeasureTheory.volume)
      (Metric.closedBall (0 : 𝔼) (2 * κ) ×ˢ s) < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (isCompact_closedBall 0 (2 * κ)).measure_lt_top hsf
  have hTmeas : MeasurableSet (Metric.closedBall (0 : 𝔼) (2 * κ) ×ˢ s) :=
    Metric.isClosed_closedBall.measurableSet.prod hs
  -- pointwise bound on `z ↦ 1_sψ(z)`
  have hψb' : ∀ z : 𝔼, ‖(((s.indicator ψ z : ℝ) : ℂ))‖ ≤ C := by
    intro z
    rw [norm_ofReal_complex]
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz]
      exact hψb z hz
    · rw [Set.indicator_of_notMem hz, abs_zero]
      exact hC
  -- uniform bound on the integrand
  have hbound : ∀ q : 𝔼 × 𝔼,
      ‖(Complex.exp (Complex.I * (inner ℝ q.1 x : ℂ)) * ((fc.f (‖q.1‖ / κ) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))) *
        (((s.indicator ψ q.2 : ℝ) : ℂ))‖ ≤ C := by
    intro q
    have hb : ‖(((fc.f (‖q.1‖ / κ) : ℝ) : ℂ))‖ ≤ 1 := by
      rw [norm_ofReal_complex]
      exact abs_lowCut_le_one fc _
    have hi : ‖(((s.indicator ψ q.2 : ℝ) : ℂ))‖ ≤ C := hψb' q.2
    simp only [Complex.norm_mul, Complex.norm_exp_I_mul_ofReal, norm_exp_neg_I_mul_ofReal]
    nlinarith [norm_nonneg (((fc.f (‖q.1‖ / κ) : ℝ) : ℂ)),
      norm_nonneg (((s.indicator ψ q.2 : ℝ) : ℂ))]
  -- vanishing of the integrand off `B(0,2κ) × s`
  have hzero : ∀ q : 𝔼 × 𝔼,
      q ∉ Metric.closedBall (0 : 𝔼) (2 * κ) ×ˢ s →
      (Complex.exp (Complex.I * (inner ℝ q.1 x : ℂ)) * ((fc.f (‖q.1‖ / κ) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))) *
        (((s.indicator ψ q.2 : ℝ) : ℂ)) = 0 := by
    intro q hq
    have hmem : q.1 ∉ Metric.closedBall (0 : 𝔼) (2 * κ) ∨ q.2 ∉ s := by
      by_contra h
      obtain ⟨h1, h2⟩ : q.1 ∈ Metric.closedBall (0 : 𝔼) (2 * κ) ∧ q.2 ∈ s := by
        simpa only [not_or, not_not] using h
      exact hq ⟨h1, h2⟩
    rcases hmem with h | h
    · have hlt : 2 * κ < ‖q.1‖ := by
        by_contra hc
        exact h (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact not_lt.mp hc))
      have hge : 2 ≤ ‖q.1‖ / κ := by
        rw [le_div_iff₀ hκ]
        exact le_of_lt hlt
      simp [fc.zero (‖q.1‖ / κ) hge]
    · have hind : (s.indicator ψ q.2 : ℝ) = 0 := Set.indicator_of_notMem h ψ
      simp [hind]
  -- the dominating function is integrable
  have hInt : MeasureTheory.Integrable
      (fun q : 𝔼 × 𝔼 =>
        (Complex.exp (Complex.I * (inner ℝ q.1 x : ℂ)) * ((fc.f (‖q.1‖ / κ) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))) *
        (((s.indicator ψ q.2 : ℝ) : ℂ)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.Integrable.mono'
      (g := (Metric.closedBall (0 : 𝔼) (2 * κ) ×ˢ s).indicator fun _ => C) ?_ ?_ ?_
    · rw [MeasureTheory.integrable_indicator_iff hTmeas]
      exact MeasureTheory.IntegrableOn.of_bound hTfin aestronglyMeasurable_const C
        (Eventually.of_forall fun q => by rw [Real.norm_of_nonneg hC])
    · have hI : MeasureTheory.AEStronglyMeasurable
          (fun q : 𝔼 × 𝔼 => (((s.indicator ψ q.2 : ℝ) : ℂ)))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          ((hψm.indicator hs).comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd)
      have hA : MeasureTheory.AEStronglyMeasurable
          (fun q : 𝔼 × 𝔼 => Complex.exp (Complex.I * (inner ℝ q.1 x : ℂ)))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_fst.prodMk continuous_const))))).aestronglyMeasurable
      have hB : MeasureTheory.AEStronglyMeasurable
          (fun q : 𝔼 × 𝔼 => ((fc.f (‖q.1‖ / κ) : ℝ) : ℂ))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        (Complex.continuous_ofReal.comp (fc.smooth.continuous.comp
          ((continuous_norm.comp continuous_fst).div_const κ))).aestronglyMeasurable
      have hD : MeasureTheory.AEStronglyMeasurable
          (fun q : 𝔼 × 𝔼 => Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ))))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        (Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_inner)))).aestronglyMeasurable
      exact ((hA.mul hB).mul hD).mul hI
    · refine Eventually.of_forall fun q => ?_
      by_cases hq : q ∈ Metric.closedBall (0 : 𝔼) (2 * κ) ×ˢ s
      · rw [Set.indicator_of_mem hq]
        exact hbound q
      · rw [Set.indicator_of_notMem hq, hzero q hq]
        simpa using hC
  exact hInt

end

end Work.BoseFixB3.CS.Pieces
