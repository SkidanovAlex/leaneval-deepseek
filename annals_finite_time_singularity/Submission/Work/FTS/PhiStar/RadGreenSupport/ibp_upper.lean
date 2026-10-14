import Mathlib
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.ConstructionInstance.bkm_congr_of_eqOn_Ico =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem bkm_congr_of_eqOn_Ico
    {u v : Work.LWP.R3 → ℝ → Work.LWP.R3} {T : ℝ}
    (h : ∀ x t, t ∈ Set.Ico 0 T → u x t = v x t) :
    ∀ t ∈ Set.Ico 0 T, Work.LWP.bkm u t = Work.LWP.bkm v t := by
  intro t ht
  simp only [Work.LWP.bkm]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsT : s ∈ Set.Ico 0 T := by
    rw [Set.uIcc_of_le ht.1] at hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hfun : (u · s) = (v · s) := funext (fun x => h x s hsT)
  show (⨆ x, ‖FiniteTimeSingularity.vorticity (u · s) x‖)
      = ⨆ x, ‖FiniteTimeSingularity.vorticity (v · s) x‖
  rw [hfun]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.bkm_le_of_vortLInf_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open MeasureTheory Set

/-- The `bkm` integral is the interval integral of the `L∞`-norm of the vorticity. -/
theorem bkm_eq_intervalIntegral_vortLInf (u : Work.LWP.R3 → ℝ → Work.LWP.R3) (t : ℝ) :
    Work.LWP.bkm u t = ∫ s in 0..t, Work.LWP.vortLInf u s := rfl

/-- **BKM growth control.**  If the `L∞`-norm of the vorticity is bounded by `K` on `[0,T)`,
then the Beale--Kato--Majda quantity at any time `t ∈ [0,T)` is at most `K * T`. -/
theorem bkm_le_of_vortLInf_bound
    {u : Work.LWP.R3 → ℝ → Work.LWP.R3} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hint : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) MeasureTheory.volume 0 t)
    (hbd : ∀ s ∈ Set.Ico 0 T, Work.LWP.vortLInf u s ≤ K) :
    ∀ t ∈ Set.Ico 0 T, Work.LWP.bkm u t ≤ K * T := by
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  rw [bkm_eq_intervalIntegral_vortLInf]
  calc ∫ s in 0..t, Work.LWP.vortLInf u s
      ≤ ∫ s in 0..t, K := by
        refine intervalIntegral.integral_mono_on ht0 (hint t ⟨ht0, htT⟩)
          intervalIntegrable_const ?_
        intro x hx
        exact hbd x ⟨hx.1, lt_of_le_of_lt hx.2 htT⟩
    _ = K * t := by
        rw [intervalIntegral.integral_const]
        simp [smul_eq_mul, mul_comm]
    _ ≤ K * T := mul_le_mul_of_nonneg_left (le_of_lt htT) hK

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.cube_div_le_27 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

/-- **The `27 = (3δ/δ)³` bound.**  For `0 < δ` and `0 ≤ s ≤ δ`,
`(2δ + s)³/(2δ - s)³ ≤ 27`, because `2δ + s ≤ 3δ` and `2δ - s ≥ δ > 0`. -/
theorem cube_div_le_27 {δ s : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hsδ : s ≤ δ) :
    (2 * δ + s) ^ 3 / (2 * δ - s) ^ 3 ≤ 27 := by
  have hpos : 0 < 2 * δ - s := by linarith
  have hcube : 0 < (2 * δ - s) ^ 3 := by positivity
  rw [div_le_iff₀ hcube]
  nlinarith [sq_nonneg (2 * δ - s), sq_nonneg (2 * δ + s), sq_nonneg (s - δ),
    sq_nonneg (2 * δ + s - 3 * (2 * δ - s))]

end Work.CoreResiduals.BiotSavart.Bundle
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.cube_div_mono_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

/-- **Monotonicity of `t ↦ (ρ+t)³/(ρ-t)³` on `[0,ρ)`.**  If `0 ≤ R' < ρ` and `‖x‖ ≤ R'` then
`(ρ + ‖x‖)³/(ρ - ‖x‖)³ ≤ (ρ + R')³/(ρ - R')³`: the numerator grows and the (positive)
denominator shrinks as `t` increases. -/
theorem cube_div_mono_le {ρ R' : ℝ} (hR' : 0 ≤ R') (hρ : R' < ρ) {x : Work.LWP.R3}
    (hx : ‖x‖ ≤ R') :
    (ρ + ‖x‖) ^ 3 / (ρ - ‖x‖) ^ 3 ≤ (ρ + R') ^ 3 / (ρ - R') ^ 3 := by
  have ht : 0 ≤ ‖x‖ := norm_nonneg x
  have hρpos : 0 < ρ := lt_of_le_of_lt hR' hρ
  have hb : 0 < ρ - ‖x‖ := by linarith
  have hd : 0 < ρ - R' := by linarith
  have hnum : 0 ≤ ρ + ‖x‖ := by linarith
  have hg : (ρ + ‖x‖) / (ρ - ‖x‖) ≤ (ρ + R') / (ρ - R') := by
    rw [div_le_div_iff₀ hb hd]
    nlinarith
  rw [← div_pow, ← div_pow]
  exact pow_le_pow_left₀ (div_nonneg hnum (le_of_lt hb)) hg 3

end Work.CoreResiduals.BiotSavart.Bundle
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.setIntegral_ball_diff_ball_comp_sub_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Set

namespace Work.CoreResiduals.BiotSavart.Bundle

/-- **Change of variables for the reflection `a ↦ x - a` of `ℝ³`.**

The map `a ↦ x - a` is an isometry of `ℝ³` (negation followed by a translation), hence measure
preserving; it sends the ball `B(0,ρ)` onto `B(x,ρ)` and the ball `B(y,R)` onto `B(x - y,R)`, and
images of differences are differences of images.  Hence the set integral over the "difference of
two balls" region transforms accordingly. -/
theorem setIntegral_ball_diff_ball_comp_sub_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Work.LWP.R3 → E) (ρ R : ℝ) (x y : Work.LWP.R3) :
    (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R), f (x - a))
      = ∫ b in (Metric.ball x ρ) \ (Metric.ball (x - y) R), f b := by
  -- The reflection `T a = x - a` is measure preserving and a measurable embedding.
  have hT : MeasureTheory.MeasurePreserving (fun a : Work.LWP.R3 => x - a) volume volume := by
    have h3 : MeasureTheory.MeasurePreserving (fun a : Work.LWP.R3 => x + -a) volume volume :=
      (measurePreserving_add_left volume x).comp (LinearIsometryEquiv.neg ℝ).measurePreserving
    exact h3
  have hTemb : MeasurableEmbedding (fun a : Work.LWP.R3 => x - a) := by
    have := Homeomorph.measurableEmbedding (Homeomorph.subLeft x)
    simpa using this
  -- Membership of the image points in the two balls.
  have hmem1 : ∀ a : Work.LWP.R3,
      x - a ∈ Metric.ball x ρ ↔ a ∈ Metric.ball (0 : Work.LWP.R3) ρ := by
    intro a
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show x - a - x = -a by abel, norm_neg, sub_zero]
  have hmem2 : ∀ a : Work.LWP.R3,
      x - a ∈ Metric.ball (x - y) R ↔ a ∈ Metric.ball y R := by
    intro a
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show x - a - (x - y) = -(a - y) by abel, norm_neg]
  -- The reflection maps the difference of balls onto the reflected difference of balls.
  have hmemB : ∀ a : Work.LWP.R3,
      (x - a ∈ (Metric.ball x ρ) \ (Metric.ball (x - y) R))
        ↔ (a ∈ (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R)) := by
    intro a
    simp only [Set.mem_sdiff, hmem1 a, hmem2 a]
  have hmemB' : ∀ a : Work.LWP.R3,
      (a ∈ (Metric.ball x ρ) \ (Metric.ball (x - y) R))
        ↔ (x - a ∈ (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R)) := by
    intro a
    have h := hmemB (x - a)
    rwa [show x - (x - a) = a by abel] at h
  have hset : (fun a : Work.LWP.R3 => x - a) ''
      ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R))
      = (Metric.ball x ρ) \ (Metric.ball (x - y) R) := by
    ext b
    rw [Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hmemB a).mpr ha
    · intro hb
      exact ⟨x - b, (hmemB' b).mp hb, by simp⟩
  rw [← MeasureTheory.MeasurePreserving.setIntegral_image_emb hT hTemb f _, hset]

end Work.CoreResiduals.BiotSavart.Bundle
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.KfBall.inner_add_sqrt_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.KfBall

/-- For `‖z‖ < ρ` and any `ω` on the unit sphere, the quantity
`⟪z, ω⟫ + √(⟪z, ω⟫² + (ρ² - ‖z‖²))` is strictly positive. -/
theorem inner_add_sqrt_pos (z : Work.LWP.R3) {ρ : ℝ} (hz : ‖z‖ < ρ)
    (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    0 < inner ℝ z (ω : Work.LWP.R3)
      + Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2)) := by
  set a := inner ℝ z (ω : Work.LWP.R3) with ha
  -- `ρ² - ‖z‖² > 0` because `‖z‖ < ρ` (which forces `ρ > 0`).
  have hb : 0 < ρ ^ 2 - ‖z‖ ^ 2 := by
    have h1 : 0 ≤ ‖z‖ := norm_nonneg z
    have h2 : 0 < ρ := lt_of_le_of_lt h1 hz
    nlinarith
  -- The square root dominates `|a|`.
  have hlt : |a| < Real.sqrt (a ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg a) (by nlinarith)
  -- `-a ≤ |a| < √(...)`, hence `a + √(...) > 0`.
  linarith [neg_le_abs a, hlt]

end Work.CoreResiduals.BiotSavart.KfBall
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.KfBall.mem_ball_smul_sphere_iff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.KfBall

/-- **The ball membership criterion.**  For `‖z‖ < ρ`, a point `ω` of the unit sphere and a
radius `r > 0`, the point `r • ω` lies in the open ball `B(z, ρ)` exactly when `r` is below the
larger root `⟨z, ω⟩ + √(⟨z, ω⟩² + (ρ² - ‖z‖²))` of the quadratic that describes `‖r ω - z‖ = ρ`.

The proof is the elementary computation
`‖r ω - z‖² = r² - 2 r ⟨z, ω⟩ + ‖z‖²`, whose comparison with `ρ²` is the quadratic inequality
`(r - ⟨z, ω⟩)² < ⟨z, ω⟩² + ρ² - ‖z‖²`; the *lower* root of the quadratic is automatically negative
(because `ρ² - ‖z‖² > 0`), so for `r > 0` only the upper root matters. -/
theorem mem_ball_smul_sphere_iff (z : Work.LWP.R3) {ρ : ℝ} (hz : ‖z‖ < ρ)
    (ω : Metric.sphere (0 : Work.LWP.R3) 1) {r : ℝ} (hr : 0 < r) :
    r • (ω : Work.LWP.R3) ∈ Metric.ball z ρ ↔
      r < inner ℝ z (ω : Work.LWP.R3)
        + Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2)) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hz
  have hω_norm : ‖(ω : Work.LWP.R3)‖ = 1 := by
    have h := ω.2
    rw [mem_sphere_iff_norm, sub_zero] at h
    exact h
  rw [Metric.mem_ball, dist_eq_norm]
  set a : ℝ := inner ℝ z (ω : Work.LWP.R3) with ha
  set c : ℝ := a ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2) with hc
  have hcpos : 0 < c := by
    rw [hc]; nlinarith [sq_nonneg a, norm_nonneg z]
  have hsq : ‖r • (ω : Work.LWP.R3) - z‖ ^ 2 = r ^ 2 - 2 * r * a + ‖z‖ ^ 2 := by
    rw [norm_sub_sq_real]
    have h1 : ‖r • (ω : Work.LWP.R3)‖ ^ 2 = r ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hω_norm, mul_one, sq_abs]
    have h2 : inner ℝ (r • (ω : Work.LWP.R3)) z = r * a := by
      rw [inner_smul_left]; simp [ha, real_inner_comm]
    rw [h1, h2]; ring
  have hstep1 : ‖r • (ω : Work.LWP.R3) - z‖ < ρ ↔
      ‖r • (ω : Work.LWP.R3) - z‖ ^ 2 < ρ ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_pos hρ]
  have hstep2 : ‖r • (ω : Work.LWP.R3) - z‖ ^ 2 < ρ ^ 2 ↔ (r - a) ^ 2 < c := by
    rw [hsq, hc]
    constructor <;> intro h <;> nlinarith
  rw [hstep1, hstep2]
  have hlt : a - Real.sqrt c < 0 := by
    have h2c : a ^ 2 < c := by rw [hc]; nlinarith [norm_nonneg z]
    have h1 : Real.sqrt (a ^ 2) < Real.sqrt c := Real.sqrt_lt_sqrt (sq_nonneg a) h2c
    rw [Real.sqrt_sq_eq_abs] at h1
    nlinarith [le_abs_self a]
  have hfin : (r - a) ^ 2 < c ↔ r < a + Real.sqrt c := by
    have hL : (r - a) ^ 2 < c ↔ |r - a| < Real.sqrt c := by
      rw [← sq_abs (r - a), Real.lt_sqrt (abs_nonneg (r - a))]
    rw [hL, abs_lt]
    constructor
    · rintro ⟨-, h2⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩
  rw [hfin]

end Work.CoreResiduals.BiotSavart.KfBall
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_even_smul_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sphere integral of `f (⟪z, ω⟫) • ω` vanishes for even `f`

For an even function `f : ℝ → ℝ` the antipodal map `ω ↦ -ω` of the unit sphere `S² ⊆ ℝ³`
sends the integrand `ω ↦ f (⟪z, ω⟫) • ω` to its pointwise negative, while preserving the
surface measure `Measure.toSphere volume`.  Hence the integral equals its own negative, so it
vanishes.

The single measure-theoretic input is that `μ.toSphere` inherits invariance under `ω ↦ -ω`
from `μ` (proved below as the instance `Measure.IsNegInvariant (μ.toSphere)`).
-/

namespace Work.CoreResiduals.BiotSavart.KfBall

open MeasureTheory Set
open scoped Pointwise

/-- If a measure `μ` on a normed space is invariant under `x ↦ -x`, then so is its unit sphere
measure `μ.toSphere`: the defining formula `μ.toSphere s = dim E * μ ((0,1) • ↑''s)` together
with `(0,1) • (-A) = -((0,1) • A)` and the negation invariance of `μ` gives the claim. -/
instance instIsNegInvariantToSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsNegInvariant] :
    μ.toSphere.IsNegInvariant := by
  refine ⟨?_⟩
  rw [Measure.neg_def]
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  rw [Measure.toSphere_apply' μ (hs.preimage measurable_neg),
      Measure.toSphere_apply' μ hs]
  congr 1
  -- the image of the preimage of `s` under the coercion is the negation of the image of `s`
  have hset : Subtype.val '' (Neg.neg ⁻¹' s) = -(Subtype.val '' s) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨-a, ha, by simp⟩
    · rintro ⟨a, ha, hx⟩
      exact ⟨-a, by simpa using ha, by simp [hx]⟩
  rw [hset]
  -- scaling a set by `(0,1) ⊆ ℝ` commutes with pointwise negation
  have hsmul : Set.Ioo (0:ℝ) 1 • (-(Subtype.val '' s)) =
      -(Set.Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_neg, Set.mem_Ioo]
    constructor
    · rintro ⟨c, hc, y, hy, rfl⟩
      exact ⟨c, hc, -y, hy, by simp⟩
    · rintro ⟨c, hc, a, ha, hx⟩
      exact ⟨c, hc, -a, by simpa using ha, by rw [smul_neg, hx, neg_neg]⟩
  rw [hsmul]
  exact Measure.measure_neg μ _

/-- For an even function `f` and any vector `z`, the vector-valued integral over the unit sphere
of `f (⟪z, ω⟫) • ω` vanishes: the antipodal map preserves the sphere measure and negates the
integrand. -/
theorem sphere_integral_even_smul_eq_zero (f : ℝ → ℝ) (hf : ∀ t, f (-t) = f t) (z : Work.LWP.R3) :
    ∫ ω, f (inner ℝ z (ω : Work.LWP.R3)) • (ω : Work.LWP.R3)
      ∂(MeasureTheory.Measure.toSphere (MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3)) = 0 := by
  let g : Metric.sphere (0 : Work.LWP.R3) 1 → Work.LWP.R3 :=
    fun ω => f (inner ℝ z (ω : Work.LWP.R3)) • (ω : Work.LWP.R3)
  change ∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere) = 0
  -- the integrand is odd under the antipodal map
  have hpoint : ∀ ω : Metric.sphere (0:Work.LWP.R3) 1, g (-ω) = -g ω := by
    intro ω
    simp only [g]
    rw [show ((-ω : Metric.sphere (0:Work.LWP.R3) 1) : Work.LWP.R3) = -(ω : Work.LWP.R3) from rfl]
    rw [inner_neg_right, hf, smul_neg]
  -- the antipodal map preserves the sphere measure
  have hmp : MeasurePreserving
      (Neg.neg : Metric.sphere (0:Work.LWP.R3) 1 → Metric.sphere (0:Work.LWP.R3) 1)
      ((volume : Measure Work.LWP.R3).toSphere) ((volume : Measure Work.LWP.R3).toSphere) :=
    Measure.measurePreserving_neg _
  have h1 : ∫ ω, g (-ω) ∂((volume : Measure Work.LWP.R3).toSphere)
      = ∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere) :=
    hmp.integral_comp (MeasurableEquiv.neg (Metric.sphere (0:Work.LWP.R3) 1)).measurableEmbedding g
  have h2 : ∫ ω, g (-ω) ∂((volume : Measure Work.LWP.R3).toSphere)
      = -∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with ω
    exact hpoint ω
  -- hence the integral equals its own negative, so it vanishes
  have key : (∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere))
      = -(∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere)) := h1.symm.trans h2
  have hsum : (∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere))
      + (∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere)) = 0 := by
    have := congrArg
      (fun x => x + (∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere))) key
    simpa using this
  have h2s : (2:ℝ) • (∫ ω, g ω ∂((volume : Measure Work.LWP.R3).toSphere)) = 0 := by
    rw [two_smul]
    exact hsum
  exact (smul_eq_zero.mp h2s).resolve_left two_ne_zero

end Work.CoreResiduals.BiotSavart.KfBall
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.exists_rpow_dom_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Pointwise domination of a singular Biot--Savart kernel power by a weight
`1 + ‖a‖^(c-3)`, uniformly for `‖x‖ ≤ X` and `δ ≤ ‖x - a‖`.

For the exponent `c - 3 ≥ 0` we use `‖x - a‖ ≤ (X+1) * (1 + ‖a‖)` and
`(1 + t)^p ≤ 2^p (1 + t^p)`; for `c - 3 ≤ 0` we use monotonicity of `t ↦ t^p`
together with `δ ≤ ‖x - a‖`. -/
theorem exists_rpow_dom_bound {C c X δ : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hX : 0 ≤ X) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x a : Work.LWP.R3), ‖x‖ ≤ X → δ ≤ ‖x - a‖ →
      4 * C * (‖x - a‖ : ℝ) ^ (c - 3) ≤ K * (1 + (‖a‖ : ℝ) ^ (c - 3)) := by
  have hc0 : (0 : ℝ) < c := hc
  by_cases h3 : 3 ≤ c
  · have hp : 0 ≤ c - 3 := by linarith
    refine ⟨4 * C * ((X + 1) ^ (c - 3) * (2:ℝ) ^ (c - 3)), ?_, ?_⟩
    · refine mul_nonneg (by linarith) (mul_nonneg ?_ ?_)
      · exact Real.rpow_nonneg (by linarith) _
      · exact Real.rpow_nonneg (by norm_num) _
    · intro x a hx hd
      have ht : (0:ℝ) ≤ ‖a‖ := norm_nonneg _
      have hsub : ‖x - a‖ ≤ (X + 1) * (1 + ‖a‖) := by
        have h1 : ‖x - a‖ ≤ ‖x‖ + ‖a‖ := norm_sub_le x a
        have h2 : ‖x‖ + ‖a‖ ≤ X + ‖a‖ := by linarith
        have h3' : X + ‖a‖ ≤ (X + 1) * (1 + ‖a‖) := by nlinarith
        linarith
      have hsp : ‖x - a‖ ^ (c - 3) ≤ ((X + 1) * (1 + ‖a‖)) ^ (c - 3) :=
        Real.rpow_le_rpow (norm_nonneg _) hsub hp
      rw [Real.mul_rpow (by linarith : (0:ℝ) ≤ X + 1) (by linarith : (0:ℝ) ≤ 1 + ‖a‖)] at hsp
      have h1t : (1 + ‖a‖) ^ (c - 3) ≤ (2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3)) := by
        by_cases ht1 : ‖a‖ ≤ 1
        · have hle : (1 + ‖a‖) ^ (c - 3) ≤ (2:ℝ) ^ (c - 3) :=
            Real.rpow_le_rpow (by linarith) (by linarith) hp
          exact le_trans hle (le_mul_of_one_le_right (Real.rpow_nonneg (by norm_num) _)
            (by linarith [Real.rpow_nonneg ht (c-3)]))
        · have hle : (1 + ‖a‖) ^ (c - 3) ≤ ((2:ℝ) * ‖a‖) ^ (c - 3) :=
            Real.rpow_le_rpow (by linarith) (by linarith) hp
          rw [Real.mul_rpow (by norm_num) ht] at hle
          refine le_trans hle (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _))
          linarith [Real.rpow_nonneg ht (c-3)]
      have step : ‖x - a‖ ^ (c - 3) ≤
          (X + 1) ^ (c - 3) * ((2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3))) :=
        calc ‖x - a‖ ^ (c - 3) ≤ (X + 1) ^ (c - 3) * (1 + ‖a‖) ^ (c - 3) := hsp
          _ ≤ (X + 1) ^ (c - 3) * ((2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3))) :=
              mul_le_mul_of_nonneg_left h1t (Real.rpow_nonneg (by linarith) _)
      calc 4 * C * ‖x - a‖ ^ (c - 3)
          ≤ 4 * C * ((X + 1) ^ (c - 3) * ((2:ℝ) ^ (c - 3) * (1 + ‖a‖ ^ (c - 3)))) :=
            mul_le_mul_of_nonneg_left step (by linarith)
        _ = 4 * C * ((X + 1) ^ (c - 3) * (2:ℝ) ^ (c - 3)) * (1 + ‖a‖ ^ (c - 3)) := by ring
  · have hp : c - 3 ≤ 0 := by linarith
    refine ⟨4 * C * δ ^ (c - 3), ?_, ?_⟩
    · exact mul_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos hδ _))
    · intro x a hx hd
      have ht : (0:ℝ) ≤ ‖a‖ := norm_nonneg _
      have hsp : ‖x - a‖ ^ (c - 3) ≤ δ ^ (c - 3) :=
        Real.rpow_le_rpow_of_nonpos hδ hd hp
      have h1 : 4 * C * ‖x - a‖ ^ (c - 3) ≤ 4 * C * δ ^ (c - 3) :=
        mul_le_mul_of_nonneg_left hsp (by linarith)
      have h2 : 4 * C * δ ^ (c - 3) ≤ 4 * C * δ ^ (c - 3) * (1 + ‖a‖ ^ (c - 3)) :=
        le_mul_of_one_le_right (mul_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos hδ _)))
          (by linarith [Real.rpow_nonneg ht (c-3)])
      exact le_trans h1 h2

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.integrableOn_one_add_norm_rpow_ball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Set

/-- The function `a ↦ 1 + ‖a‖ ^ s` is integrable on any ball centred at the origin of `ℝ³`,
provided `s > -3` (which is exactly the threshold at which `‖a‖ ^ s` is integrable near the
origin in dimension `3`). -/
theorem integrableOn_one_add_norm_rpow_ball (s r : ℝ) (hs : -3 < s) :
    MeasureTheory.IntegrableOn (fun a : Work.LWP.R3 => 1 + (‖a‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) r) MeasureTheory.volume := by
  rcases le_or_gt r 0 with hr | hr
  · -- Empty ball.
    rw [Metric.ball_eq_empty.mpr hr]
    exact integrableOn_empty
  · -- Polar coordinates: integrability on the ball is equivalent to integrability on `(0, r)`
    -- of `y ↦ y ^ (3 - 1) * (1 + y ^ s) = y ^ 2 + y ^ (2 + s)`.
    rw [MeasureTheory.integrableOn_fun_norm_addHaar (μ := (volume : Measure Work.LWP.R3))
        (f := fun y : ℝ => 1 + y ^ s) (r := r)]
    have hdim : Module.finrank ℝ Work.LWP.R3 = 3 := by
      simp only [Work.LWP.R3]; exact finrank_euclideanSpace_fin
    rw [hdim]
    norm_num
    have h1 : IntegrableOn (fun y : ℝ => y ^ (2 : ℝ)) (Ioo 0 r) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by norm_num)
    have h2 : IntegrableOn (fun y : ℝ => y ^ (2 + s)) (Ioo 0 r) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)
    refine (h1.add h2).congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [Pi.add_apply]
    rw [Real.rpow_add hy.1, ← Real.rpow_natCast y 2]
    ring_nf

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_gSub_le_interp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

theorem norm_gSub_le_interp {α A H : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) (hH : 0 ≤ H)
    {g : Work.LWP.R3 → Work.LWP.R3} (hbdd : ∀ a, ‖g a‖ ≤ A)
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H * ‖a - b‖ ^ α)
    (x a : Work.LWP.R3) :
    ‖g a - g x‖ ≤ (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α)) := by
  set u : ℝ := ‖g a - g x‖ with hu_def
  set t : ℝ := ‖x - a‖ with ht_def
  have hu : 0 ≤ u := by rw [hu_def]; exact norm_nonneg _
  have ht : 0 ≤ t := by rw [ht_def]; exact norm_nonneg _
  have h2A : 0 ≤ 2 * A := by linarith
  have h2H : 0 ≤ 2 * H := by linarith
  -- the two bounds on `u = ‖g a - g x‖`
  have hbdd' : u ≤ 2 * A := by
    rw [hu_def]
    calc ‖g a - g x‖ ≤ ‖g a‖ + ‖g x‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add (hbdd a) (hbdd x)
      _ = 2 * A := by ring
  have hhold' : u ≤ 2 * H * t ^ α := by
    rw [hu_def, ht_def]
    have h := hhold a x
    rw [norm_sub_rev a x] at h
    exact h
  -- split `u` as `u^α · u^{1-α}`
  have hkey : u = u ^ α * u ^ (1 - α) := by
    have h := Real.rpow_add' hu (x := u) (y := α) (z := 1 - α) (by linarith)
    rw [show α + (1 - α) = 1 by ring, Real.rpow_one] at h
    exact h
  -- apply `rpow_le_rpow` to each factor
  have hA_le : u ^ α ≤ (2 * A) ^ α := Real.rpow_le_rpow hu hbdd' hα.le
  have hH_le : u ^ (1 - α) ≤ (2 * H * t ^ α) ^ (1 - α) :=
    Real.rpow_le_rpow hu hhold' (by linarith)
  calc u = u ^ α * u ^ (1 - α) := hkey
    _ ≤ (2 * A) ^ α * (2 * H * t ^ α) ^ (1 - α) :=
        mul_le_mul hA_le hH_le (Real.rpow_nonneg hu _) (Real.rpow_nonneg h2A _)
    _ = (2 * A) ^ α * (2 * H) ^ (1 - α) * t ^ (α * (1 - α)) := by
        rw [Real.mul_rpow h2H (Real.rpow_nonneg ht α), ← Real.rpow_mul ht]
        ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.polar_decomposition =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Work.CoreResiduals.BiotSavart

/-- `Module.finrank ℝ ℝ³ = 3`. -/
lemma finrank_R3 : Module.finrank ℝ Work.LWP.R3 = 3 := by
  simp [Work.LWP.R3, finrank_euclideanSpace]

/-- **Polar decomposition of `ℝ³`.**  Integration against Lebesgue measure on `ℝ³` can be
written as an iterated integral over the unit sphere (`Measure.toSphere`) and the radial
measure `Measure.volumeIoiPow 2` on `(0,∞)` (which has density `r ↦ r²` with respect to
Lebesgue measure). -/
lemma polar_decomposition (F : Work.LWP.R3 → ℝ) :
    ∫ x, F x ∂(volume : Measure Work.LWP.R3)
      = ∫ p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ),
          F (p.2.1 • (p.1.1 : Work.LWP.R3))
          ∂((volume : Measure Work.LWP.R3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  have hmp := MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (μ := (volume : Measure Work.LWP.R3))
  rw [finrank_R3] at hmp
  conv_lhs => rw [← restrict_compl_singleton (μ := (volume : Measure Work.LWP.R3)) (0 : Work.LWP.R3)]
  rw [← integral_subtype_comap (measurableSet_singleton (0:Work.LWP.R3)).compl F]
  have hcongr : ∀ x : ({0}ᶜ : Set Work.LWP.R3),
      (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ) =>
          F (p.2.1 • (p.1.1 : Work.LWP.R3)))
        (homeomorphUnitSphereProd Work.LWP.R3 x) = F ↑x := by
    intro x
    have h := homeomorphUnitSphereProd_symm_apply_coe Work.LWP.R3
      (homeomorphUnitSphereProd Work.LWP.R3 x)
    rw [Homeomorph.symm_apply_apply] at h
    exact congrArg F h.symm
  rw [show (∫ x : ({0}ᶜ : Set Work.LWP.R3),
              F ↑x ∂(Measure.comap Subtype.val (volume : Measure Work.LWP.R3)))
        = ∫ x, (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ) =>
              F (p.2.1 • (p.1.1 : Work.LWP.R3)))
            (homeomorphUnitSphereProd Work.LWP.R3 x)
            ∂(Measure.comap Subtype.val (volume : Measure Work.LWP.R3))
        from integral_congr_ae (Filter.Eventually.of_forall fun x => (hcongr x).symm)]
  exact hmp.integral_comp (Homeomorph.measurableEmbedding _)
    (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ) =>
      F (p.2.1 • (p.1.1 : Work.LWP.R3)))

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.radial_rpow_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- Radial power integral over the ball of radius `r` in `ℝ³`:
`∫_{‖z‖<r} ‖z‖^s dz = 4π r^{s+3} / (s+3)` for `s > -3`.
Proved from the general radial decomposition `MeasureTheory.integral_fun_norm_addHaar`
together with the volume `|B_1| = 4π/3` and `∫_0^r y^{s+2} dy = r^{s+3}/(s+3)`. -/
theorem radial_rpow_integral (s : ℝ) (hs : -3 < s) (r : ℝ) (hr : 0 < r) :
    ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s
      = 4 * Real.pi * r ^ (s + 3) / (s + 3) := by
  have hfin : Module.finrank ℝ Work.LWP.R3 = 3 := by simp [finrank_euclideanSpace]
  -- rewrite the ball integral as the full-space integral of the radial profile
  -- `(Iio r).indicator (·^s)`
  have hball : ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s
      = ∫ z : Work.LWP.R3, ((Iio r).indicator (fun y : ℝ => y ^ s)) ‖z‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Metric.ball (0 : Work.LWP.R3) r
    · have hzr : ‖z‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hz
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show ‖z‖ ∈ Iio r from hzr)]
    · have hzr : ¬ ‖z‖ < r := by
        intro h; exact hz (by rwa [Metric.mem_ball, dist_zero_right])
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show ‖z‖ ∉ Iio r from hzr)]
  -- volume of the unit ball
  have hvol : volume.real (Metric.ball (0 : Work.LWP.R3) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    rw [show ENNReal.ofReal (1:ℝ) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
          = ENNReal.ofReal (Real.pi * 4 / 3) by simp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  -- the radial integral `∫_{Ioi 0} y^2 • indicator (Iio r) y^s = ∫_0^r y^{s+2} = r^{s+3}/(s+3)`
  have hInt : ∫ y in Ioi (0:ℝ), y ^ ((3:ℕ) - 1) • ((Iio r).indicator (fun y : ℝ => y ^ s)) y
      = r ^ (s + 3) / (s + 3) := by
    simp only [Nat.reduceSub]
    have hstep : ∫ y in Ioi (0:ℝ), y ^ (2:ℕ) • ((Iio r).indicator (fun y : ℝ => y ^ s)) y
        = ∫ y in Ioo (0:ℝ) r, y ^ (s + 2) := by
      rw [← integral_indicator measurableSet_Ioi]
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hy]
        by_cases hyr : y < r
        · rw [Set.indicator_of_mem (show y ∈ Iio r from hyr),
            Set.indicator_of_mem (show y ∈ Ioo (0:ℝ) r from ⟨hy, hyr⟩)]
          rw [smul_eq_mul, ← Real.rpow_natCast y 2, ← Real.rpow_add hy ((2:ℕ):ℝ) s,
            show ((2:ℕ):ℝ) + s = s + 2 by ring]
        · rw [Set.indicator_of_notMem (show y ∉ Iio r from hyr),
            Set.indicator_of_notMem (show y ∉ Ioo (0:ℝ) r from fun h => hyr h.2), smul_zero]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (show y ∉ Ioo (0:ℝ) r from fun h => hy (Ioo_subset_Ioi_self h))]
    rw [hstep]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < s + 2))]
    rw [show s + 2 + 1 = s + 3 by ring, Real.zero_rpow (by linarith : s + 3 ≠ 0)]
    rw [sub_zero]
  rw [hball, integral_fun_norm_addHaar volume ((Iio r).indicator (fun y : ℝ => y ^ s))]
  rw [hfin]
  rw [hInt, hvol]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.volume_real_ball_three =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- The Lebesgue measure (as a real number) of an open ball in `ℝ³`:
`|B(x,r)| = (4π/3) r³`, in the form `r³ * (π * 4 / 3)`.

Immediate from the explicit three-dimensional volume formula
`EuclideanSpace.volume_ball_fin_three`, which gives
`volume (B(x,r)) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (π * 4 / 3)`. -/
theorem volume_real_ball_three {x : Work.LWP.R3} {r : ℝ} (hr : 0 ≤ r) :
    MeasureTheory.volume.real (Metric.ball x r) = r ^ 3 * (Real.pi * 4 / 3) := by
  rw [MeasureTheory.Measure.real_def, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity)]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.exists_holder_bound_of_lipschitzOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- A function that is `K`-Lipschitz in its second variable on the interval `[0, S]`
admits a `N₁`-Hölder bound with any exponent `α ≤ 1`.

The uniform constant is `N₁ = max K (2 * (K * S))`.  Indeed for `t, t' ∈ [0, S]`
the Lipschitz bound gives `‖f y t - f y t'‖ ≤ K * |t - t'|` *and* (using
`|t - t'| ≤ S`) the uniform bound `‖f y t - f y t'‖ ≤ 2 * (K * S)`; combining the
two with the elementary inequality `min (K * d) (2 * M) ≤ max K (2 * M) * d ^ α`
for `0 ≤ d` and `α ≤ 1` yields the claim. -/
theorem exists_holder_bound_of_lipschitzOn {X E : Type*} [NormedAddCommGroup E]
    {f : X → ℝ → E} {S K : ℝ} {α : NNReal} (hS : 0 ≤ S) (hK : 0 ≤ K) (hα : α ≤ 1)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S, ∀ y : X,
      ‖f y t - f y t'‖ ≤ K * |t - t'|) :
    ∃ N₁ : ℝ, ∀ y : X, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S,
      ‖f y t - f y t'‖ ≤ N₁ * |t - t'| ^ (α : ℝ) := by
  refine ⟨max K (2 * (K * S)), ?_⟩
  intro y t ht t' ht'
  have hd0 : 0 ≤ |t - t'| := abs_nonneg _
  have hdS : |t - t'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht.2, ht'.1], by linarith [ht'.2, ht.1]⟩
  have hKS : 0 ≤ K * S := mul_nonneg hK hS
  have hb : ‖f y t - f y t'‖ ≤ K * |t - t'| := h t ht t' ht' y
  have hb2 : ‖f y t - f y t'‖ ≤ 2 * (K * S) := by
    calc ‖f y t - f y t'‖ ≤ K * |t - t'| := hb
      _ ≤ K * S := mul_le_mul_of_nonneg_left hdS hK
      _ ≤ 2 * (K * S) := by linarith
  exact le_trans (le_min hb hb2) (Work.Stability.min_mul_le_max_mul_rpow hK hKS hd0 hα)

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I4BV.i4_limit_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I4BV

/-! ## Two elementary calculus helpers -/

/-- The derivative of `s ↦ a/(b - s)` away from `b`. -/
private lemma hasDerivAt_rat (a b : ℝ) {x : ℝ} (hx : x ≠ b) :
    HasDerivAt (fun s : ℝ => a / (b - s)) (a / (b - x) ^ 2) x := by
  have hxb : b - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h1 : HasDerivAt (fun s : ℝ => b - s) (-1) x := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) x).const_sub b
  have h2 : HasDerivAt (fun s : ℝ => (b - s)⁻¹) (-(-1) / (b - x) ^ 2) x := h1.inv hxb
  have h3 : HasDerivAt (fun s : ℝ => a * (b - s)⁻¹) (a * (-(-1) / (b - x) ^ 2)) x :=
    h2.const_mul a
  have hone : a * (-(-1) / (b - x) ^ 2) = a / (b - x) ^ 2 := by
    rw [neg_neg, one_div, div_eq_mul_inv]
  rw [hone] at h3
  have hfun : (fun s : ℝ => a * (b - s)⁻¹) = (fun s : ℝ => a / (b - s)) := by
    funext s; rw [div_eq_mul_inv]
  rw [hfun] at h3
  exact h3

/-- The value of the derivative of `s ↦ a/(b - s)` away from `b`. -/
private lemma deriv_rat (a b : ℝ) {x : ℝ} (hx : x ≠ b) :
    deriv (fun s : ℝ => a / (b - s)) x = a / (b - x) ^ 2 :=
  (hasDerivAt_rat a b hx).deriv

/-! ## Growth from a derivative lower bound -/

/-- If `ψ` is `C¹` on `(b-ε, b)` and `ψ' θ ≥ a/(b-θ)²` there (`a > 0`), then `ψ` grows at
least like `(a/2)/(b-θ)` as `θ → b⁻`.  Indeed `g θ = ψ θ - a/(b-θ)` has
`g' = ψ' - a/(b-θ)² ≥ 0`, so `g` is nondecreasing. -/
private theorem exists_ge_div_of_deriv_ge {ψ : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hsm : ContDiffOn ℝ 1 ψ (Set.Ioo (b - ε) b))
    (hbound : ∀ θ ∈ Set.Ioo (b - ε) b, a / (b - θ) ^ 2 ≤ deriv ψ θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ θ ∈ Set.Ioo (b - δ) b, a / 2 / (b - θ) ≤ ψ θ := by
  set θ₀ : ℝ := b - ε / 2 with hθ₀
  have hθ₀mem : θ₀ ∈ Set.Ioo (b - ε) b :=
    ⟨by rw [hθ₀]; linarith, by rw [hθ₀]; linarith⟩
  have hdiffOn : DifferentiableOn ℝ ψ (Set.Ioo (b - ε) b) := hsm.differentiableOn (by norm_num)
  -- `g θ = ψ θ - a/(b-θ)` is nondecreasing on `[θ₀, θ]`.
  have hmono : ∀ θ ∈ Set.Ioo θ₀ b, ψ θ₀ - a / (b - θ₀) ≤ ψ θ - a / (b - θ) := by
    intro θ hθ
    have hsub : Set.Icc θ₀ θ ⊆ Set.Ioo (b - ε) b := fun s hs =>
      ⟨by linarith [hs.1, hθ₀mem.1], by linarith [hs.2, hθ.2]⟩
    have hlt : ∀ s ∈ Set.Icc θ₀ θ, s < b := fun s hs => lt_of_le_of_lt hs.2 hθ.2
    have hmon : MonotoneOn (fun s : ℝ => ψ s - a / (b - s)) (Set.Icc θ₀ θ) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc θ₀ θ) ?_ ?_ ?_
      · refine ContinuousOn.sub (hsm.continuousOn.mono hsub) ?_
        refine ContinuousOn.div continuousOn_const
          (continuousOn_const.sub continuousOn_id) ?_
        intro s hs
        exact ne_of_gt (sub_pos.mpr (hlt s hs))
      · rw [interior_Icc]
        refine DifferentiableOn.sub (hdiffOn.mono ?_) ?_
        · intro s hs
          exact ⟨by linarith [hs.1, hθ₀mem.1], by linarith [hs.2, hθ.2]⟩
        · refine DifferentiableOn.div (differentiableOn_const a)
            ((differentiableOn_const b).sub differentiableOn_id) ?_
          intro s hs
          exact ne_of_gt (sub_pos.mpr (lt_trans hs.2 hθ.2))
      · intro x hx
        rw [interior_Icc] at hx
        have hxmem : x ∈ Set.Ioo (b - ε) b :=
          ⟨by linarith [hx.1, hθ₀mem.1], by linarith [hx.2, hθ.2]⟩
        have hxb : x ≠ b := ne_of_lt (lt_trans hx.2 hθ.2)
        have hdψ : DifferentiableAt ℝ ψ x :=
          hdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hxmem)
        have hdrat : DifferentiableAt ℝ (fun s : ℝ => a / (b - s)) x :=
          (hasDerivAt_rat a b hxb).differentiableAt
        have hdv : deriv (fun s : ℝ => ψ s - a / (b - s)) x
            = deriv ψ x - a / (b - x) ^ 2 := by
          change deriv (ψ - fun s : ℝ => a / (b - s)) x = deriv ψ x - a / (b - x) ^ 2
          rw [deriv_sub hdψ hdrat, deriv_rat a b hxb]
        rw [hdv]
        linarith [hbound x hxmem]
    have h' := hmon (Set.left_mem_Icc.mpr hθ.1.le) (Set.right_mem_Icc.mpr hθ.1.le) hθ.1.le
    simpa using h'
  -- The constant `K = ψ θ₀ - a/(b-θ₀)` and the choice of `δ`.
  set K : ℝ := ψ θ₀ - a / (b - θ₀) with hK
  set δ : ℝ := min (ε / 2) (a / 2 / (|K| + 1)) with hδ
  have hδleL : δ ≤ ε / 2 := by rw [hδ]; exact min_le_left _ _
  have hδleR : δ ≤ a / 2 / (|K| + 1) := by rw [hδ]; exact min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith) (div_pos (by linarith) (by positivity))
  refine ⟨δ, hδpos, le_trans hδleL (by linarith), ?_⟩
  intro θ hθ
  have hθb : θ < b := hθ.2
  have hbθ : 0 < b - θ := sub_pos.mpr hθb
  have hθgt : θ₀ < θ := by
    rw [hθ₀]
    linarith [hθ.1, hδleL]
  have h1 : K ≤ ψ θ - a / (b - θ) := by
    have h := hmono θ ⟨hθgt, hθb⟩
    simpa [hK] using h
  have hbθA : b - θ < a / 2 / (|K| + 1) := lt_of_lt_of_le (by linarith [hθ.1]) hδleR
  have hKle : |K| * (b - θ) ≤ a / 2 := by
    have h1' : |K| * (b - θ) ≤ |K| * (a / 2 / (|K| + 1)) :=
      mul_le_mul_of_nonneg_left hbθA.le (abs_nonneg K)
    have h2' : |K| * (a / 2 / (|K| + 1)) = |K| * (a / 2) / (|K| + 1) := by ring
    have h3' : |K| * (a / 2) / (|K| + 1) ≤ a / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < |K| + 1)]
      nlinarith [abs_nonneg K, ha]
    linarith
  have hKl : -K ≤ a / 2 / (b - θ) := by
    have h1' : |K| ≤ a / 2 / (b - θ) := by
      rw [le_div_iff₀ hbθ]
      exact hKle
    linarith [neg_le_abs K]
  have hZX : a / (b - θ) - a / 2 / (b - θ) = a / 2 / (b - θ) := by
    have ht : b - θ ≠ 0 := ne_of_gt hbθ
    field_simp
    ring
  have h3 : a / (b - θ) + K ≤ ψ θ := by linarith
  have h4 : a / 2 / (b - θ) ≤ a / (b - θ) + K := by linarith
  linarith

/-! ## Non-integrability of `ψ²` from the derivative lower bound -/

private theorem not_integrableOn_sq_of_deriv_ge' {ψ : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hε : 0 < ε) (hsm : ContDiffOn ℝ 1 ψ (Set.Ioo (b - ε) b))
    (hbound : ∀ θ ∈ Set.Ioo (b - ε) b, a / (b - θ) ^ 2 ≤ deriv ψ θ) :
    ¬ MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2) (Set.Ioo (b - ε) b) := by
  obtain ⟨δ, hδpos, hδε, hlow⟩ := exists_ge_div_of_deriv_ge ha hε hsm hbound
  have hsub : Set.Ioo (b - δ) b ⊆ Set.Ioo (b - ε) b := fun θ hθ =>
    ⟨by linarith [hθ.1, hδε], hθ.2⟩
  have hc : 0 < (a / 2) ^ 2 := by positivity
  have hnot := not_integrableOn_inv_sq_right (c := (a / 2) ^ 2) (b := b) (ε := δ) hc hδpos
  intro hint
  refine hnot ?_
  have hint' : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2) (Set.Ioo (b - δ) b) :=
    hint.mono_set hsub
  refine MeasureTheory.Integrable.mono' hint' ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => (a / 2) ^ 2 / (b - θ) ^ 2) (Set.Ioo (b - δ) b) := by
      refine ContinuousOn.div continuousOn_const
        ((continuousOn_const.sub continuousOn_id).pow 2) ?_
      intro θ hθ
      exact pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hθ.2))
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hbθ : 0 < b - θ := sub_pos.mpr hθ.2
    have hle := hlow θ hθ
    have hnonneg : 0 ≤ a / 2 / (b - θ) := div_nonneg (by linarith) hbθ.le
    have hsq : (a / 2 / (b - θ)) ^ 2 ≤ ψ θ ^ 2 := pow_le_pow_left₀ hnonneg hle 2
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [div_pow] at hsq
    exact hsq

/-! ## The main lemma -/

/-- **The `I₄` limit vanishes.**  See the module docstring. -/
theorem i4_limit_eq_zero (ψ : ℝ → ℝ) (L : ℝ)
    (hsm : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => ψ θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)))
    (hL : Filter.Tendsto (fun θ => (Real.cos θ) ^ 2 * deriv ψ θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) :
    L = 0 := by
  by_contra hLne
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  -- The angular weight is at least `1` on the open interval.
  have hσ1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      1 ≤ (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)) := by
    intro θ hθ
    simpa only [s4] using one_le_s4 hθ
  -- The contradiction engine: `ψ²` is never integrable on a right neighbourhood of `π/2`,
  -- while `hA` forces it to be.
  have hcontra : ∀ δ : ℝ, 0 < δ → δ < Real.pi / 2 →
      ¬ MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) → False := by
    intro δ hδpos hδlt hnot
    have hsub : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.1, hδlt], hθ.2⟩
    have hA' : MeasureTheory.IntegrableOn
        (fun θ => ψ θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := hA.mono_set hsub
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => ψ θ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2))) := by
      have hc : ContinuousOn (fun θ : ℝ => ψ θ ^ 2)
          (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) :=
        (hsm.continuousOn.mono hsub).pow 2
      exact hc.aestronglyMeasurable measurableSet_Ioo
    have hint : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
      refine MeasureTheory.Integrable.mono' hA' haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hθI := hsub hθ
      rw [Real.norm_of_nonneg (sq_nonneg (ψ θ))]
      exact le_mul_of_one_le_right (sq_nonneg (ψ θ)) (hσ1 θ hθI)
    exact hnot hint
  rcases lt_or_gt_of_ne hLne with hneg | hpos
  · -- Case `L < 0`: apply the engine to `-ψ`.
    have hev : ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        (Real.cos x) ^ 2 * deriv ψ x < L / 2 :=
      hL.eventually (Iio_mem_nhds (show L < L / 2 by linarith))
    obtain ⟨b, hb, hbsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
    have hblt : b < Real.pi / 2 := hb
    set δ : ℝ := min (Real.pi / 2 - b) (Real.pi / 4) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) hpi4
    have hδlt : δ < Real.pi / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
    have hδleb : δ ≤ Real.pi / 2 - b := min_le_left _ _
    have hsub1 : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo b (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.1, hδleb], hθ.2⟩
    have hkey : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        (-L) / 2 / (Real.pi / 2 - θ) ^ 2 ≤ deriv (fun θ => -ψ θ) θ := by
      intro θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ.1, hδlt], hθ.2⟩
      have hlt : (Real.cos θ) ^ 2 * deriv ψ θ < L / 2 := hbsub (hsub1 hθ)
      have hcospos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
      have hcossqpos : 0 < (Real.cos θ) ^ 2 := pow_pos hcospos 2
      have h1 : deriv ψ θ < L / 2 / (Real.cos θ) ^ 2 := by
        rw [lt_div_iff₀ hcossqpos]
        exact lt_of_eq_of_lt (mul_comm (deriv ψ θ) ((Real.cos θ) ^ 2)) hlt
      have hcle : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_lin hθI
      have hcossqle : (Real.cos θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
        pow_le_pow_left₀ hcospos.le hcle 2
      have h2 : (-L) / 2 / (Real.pi / 2 - θ) ^ 2 ≤ (-L) / 2 / (Real.cos θ) ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) hcossqpos hcossqle
      have h4 : (-L) / 2 / (Real.cos θ) ^ 2 = -(L / 2 / (Real.cos θ) ^ 2) := by ring
      have h5 : (-L) / 2 / (Real.pi / 2 - θ) ^ 2 ≤ -(L / 2 / (Real.cos θ) ^ 2) := by
        rw [← h4]; exact h2
      have hder : deriv (fun θ => -ψ θ) θ = -deriv ψ θ := by
        have hd : DifferentiableAt ℝ ψ θ :=
          (hsm.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
        exact hd.hasDerivAt.neg.deriv
      rw [hder]
      linarith
    have hsm1 : ContDiffOn ℝ 1 ψ (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) :=
      (hsm.of_le (by norm_num)).mono (fun θ hθ => ⟨by linarith [hθ.1, hδlt], hθ.2⟩)
    have hnot := not_integrableOn_sq_of_deriv_ge'
      (show (0 : ℝ) < (-L) / 2 by linarith) hδpos hsm1.neg hkey
    have hnot' : ¬ MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
      rw [show (fun θ : ℝ => (-ψ θ) ^ 2) = (fun θ => ψ θ ^ 2) from
        funext (fun θ => neg_sq (ψ θ))] at hnot
      exact hnot
    exact hcontra δ hδpos hδlt hnot'
  · -- Case `L > 0`.
    have hev : ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        L / 2 < (Real.cos x) ^ 2 * deriv ψ x :=
      hL.eventually (Ioi_mem_nhds (show L / 2 < L by linarith))
    obtain ⟨b, hb, hbsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
    have hblt : b < Real.pi / 2 := hb
    set δ : ℝ := min (Real.pi / 2 - b) (Real.pi / 4) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) hpi4
    have hδlt : δ < Real.pi / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
    have hδleb : δ ≤ Real.pi / 2 - b := min_le_left _ _
    have hsub1 : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo b (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.1, hδleb], hθ.2⟩
    have hkey : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        L / 2 / (Real.pi / 2 - θ) ^ 2 ≤ deriv ψ θ := by
      intro θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ.1, hδlt], hθ.2⟩
      have hgt : L / 2 < (Real.cos θ) ^ 2 * deriv ψ θ := hbsub (hsub1 hθ)
      have hcospos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
      have hcossqpos : 0 < (Real.cos θ) ^ 2 := pow_pos hcospos 2
      have h1 : L / 2 / (Real.cos θ) ^ 2 < deriv ψ θ := by
        rw [div_lt_iff₀ hcossqpos]
        exact lt_of_lt_of_eq hgt (mul_comm ((Real.cos θ) ^ 2) (deriv ψ θ))
      have hcle : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_lin hθI
      have hcossqle : (Real.cos θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
        pow_le_pow_left₀ hcospos.le hcle 2
      have h2 : L / 2 / (Real.pi / 2 - θ) ^ 2 ≤ L / 2 / (Real.cos θ) ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) hcossqpos hcossqle
      exact le_trans h2 h1.le
    have hsm1 : ContDiffOn ℝ 1 ψ (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) :=
      (hsm.of_le (by norm_num)).mono (fun θ hθ => ⟨by linarith [hθ.1, hδlt], hθ.2⟩)
    have hnot := not_integrableOn_sq_of_deriv_ge'
      (show (0 : ℝ) < L / 2 by linarith) hδpos hsm1 hkey
    exact hcontra δ hδpos hδlt hnot

end Work.FTS.EllipticEst.I4BV
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.lintegralConv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux


end Work.FTS.EllipticEst.Prop.CutEnergyAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.GamSliceDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.AslotGam

set_option autoImplicit false

/-- The `γ`-weighted angular weight `sgam α θ = sin(2θ)^{2-γ}`, `γ = 1 + α/10`. -/
def sgam (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-! ## Elementary facts about `γ` -/




theorem two_sub_gam_pos {α : ℝ} (hα4 : α ≤ 1 / 4) : 0 < 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem gam_lt_two {α : ℝ} (hα4 : α ≤ 1 / 4) : Work.Spaces.gam α < 2 := by
  rw [Work.Spaces.gam]; linarith



/-! ## The weight and its reciprocal -/

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


theorem sgam_nonneg {α θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ sgam α θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _





/-! ## Jordan's inequality and the resulting pointwise domination -/

/-- Jordan's inequality in the form needed here:
`(4/π)·min θ (π/2 - θ) ≤ sin(2θ)` on `[0, π/2]`. -/
theorem four_div_pi_mul_min_le_sin_two {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  have hpi := Real.pi_pos
  have h0 : (0 : ℝ) ≤ θ := hθ.1
  have h2 : θ ≤ Real.pi / 2 := hθ.2
  rcases le_total θ (Real.pi / 4) with h | h
  · have hm : min θ (Real.pi / 2 - θ) = θ := min_eq_left (by linarith)
    rw [hm]
    have h1 : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have h2' : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
    linarith [h1, h2'.symm.le, h2'.le]
  · have hm : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := min_eq_right (by linarith)
    rw [hm]
    have h1 : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) ≤ Real.sin (2 * (Real.pi / 2 - θ)) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hs : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rw [hs] at h1
    have h2' : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) = (4 / Real.pi) * (Real.pi / 2 - θ) := by ring
    linarith [h1, h2'.symm.le, h2'.le]





end Work.FTS.EllipticEst.Prop.AslotGam
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.CutBdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Boundedness of the first two derivatives of a smoothed step

If `χ` is `C²` and is constantly `1` on `(-∞, a]` and constantly `0` on `[b, ∞)` with `a < b`,
then `χ` is constant off the compact interval `[a,b]`, so `deriv χ` and `deriv (deriv χ)` both
vanish off `[a,b]`; continuity on the compact interval then gives a common bound `K ≥ 1`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.Prop.TraceLeftPieces


end Work.FTS.EllipticEst.Prop.TraceLeftPieces
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.angIbpWild =====
section

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


end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.radialIbpWild =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-- The derivative of the "flux weight" `z ↦ z·w(z)²` at a point `z > 0`: on a neighbourhood of
`z` it is the rational function `y ↦ (1+y)⁴/y³`, whose derivative is
`w(z)²·((z-3)/(1+z))`. -/
private lemma hasDerivAt_zw2 (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hEq : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) =ᶠ[nhds z]
      (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
    filter_upwards [isOpen_ne.mem_nhds hzne] with y hy
    rw [Work.Spaces.w]
    field_simp
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 3 hzne)
  have hd : HasDerivAt (fun y : ℝ => (1 + y) ^ 4 / y ^ 3)
      (deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z) z := hdiff.hasDerivAt
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  rw [deriv_fun_div (c := fun y : ℝ => (1 + y) ^ 4) (d := fun y : ℝ => y ^ 3)
      (by fun_prop) (by fun_prop) (pow_ne_zero 3 hzne),
    deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 4,
    deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 3,
    deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  rw [Work.Spaces.w]
  field_simp
  ring

/-- A one-sided limit `0` at `0⁺` together with the value `0` at `0` gives continuity of `f` within
`[0,∞)` at `0`.  (The filters `𝓝[>] 0` and `𝓝[≥] 0` are not comparable, so the value information
is genuinely used.) -/
private lemma continuousWithinAt_Ici_of_tendsto {f : ℝ → ℝ}
    (h0 : Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)) (hf0 : f 0 = 0) :
    ContinuousWithinAt f (Set.Ici 0) 0 := by
  rw [ContinuousWithinAt, hf0]
  intro s hs
  rw [Filter.mem_map]
  have h1 : f ⁻¹' s ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Filter.mem_map.mp (h0 hs)
  rw [nhdsWithin, mem_inf_iff_superset] at h1
  rw [nhdsWithin, mem_inf_iff_superset]
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := h1
  refine ⟨t1, ht1, t2 ∪ {0}, ?_, ?_⟩
  · intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with h | h
    · exact Or.inr (by simp [h])
    · exact Or.inl (ht2 h)
  · intro y hy
    rcases hy.2 with h | h
    · exact hsub ⟨hy.1, h⟩
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      simpa [Set.mem_preimage, hf0] using mem_of_mem_nhds hs

theorem radialIbpWild {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hint1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z)) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) (Set.Ioi 0))
    (hf0 : Filter.Tendsto (fun z => z * (Work.Spaces.w z) ^ 2 * φ z * ψ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hf1 : Filter.Tendsto (fun z => z * (Work.Spaces.w z) ^ 2 * φ z * ψ z) Filter.atTop (nhds 0)) :
    (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z := by
  -- the pointwise derivative of the flux `z ↦ z w(z)² φ(z) ψ(z)`
  have hderiv : ∀ z ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * φ y * ψ y)
        ((Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z)
          - (Work.Spaces.w z) ^ 2
              * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) z := by
    intro z hz
    have hA : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
        ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := hasDerivAt_zw2 z hz
    have hφd : HasDerivAt φ (deriv φ z) z :=
      ((hφ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    have hψd : HasDerivAt ψ (deriv ψ z) z :=
      ((hψ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    have hprod : HasDerivAt (fun y : ℝ => (y * (Work.Spaces.w y) ^ 2) * (φ y * ψ y))
        (((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) * (φ z * ψ z)
          + (z * (Work.Spaces.w z) ^ 2) * (deriv φ z * ψ z + φ z * deriv ψ z)) z :=
      hA.mul (hφd.mul hψd)
    have hFB : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * φ y * ψ y) =ᶠ[nhds z]
        (fun y : ℝ => (y * (Work.Spaces.w y) ^ 2) * (φ y * ψ y)) :=
      Filter.Eventually.of_forall (fun y => by ring)
    exact (hprod.congr_of_eventuallyEq hFB).congr_deriv (by ring)
  -- the derivative is integrable: it is the difference of the two given integrands
  have hDint : MeasureTheory.IntegrableOn
      ((fun z : ℝ => (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
        - fun z : ℝ => (Work.Spaces.w z) ^ 2
            * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) (Set.Ioi 0) :=
    hint1.sub hint2
  -- the flux is continuous on `[0,∞)` at `0` and has limit `0` at `+∞`
  have hcont : ContinuousWithinAt (fun z : ℝ => z * (Work.Spaces.w z) ^ 2 * φ z * ψ z)
      (Set.Ici 0) 0 :=
    continuousWithinAt_Ici_of_tendsto hf0 (by simp)
  -- the fundamental theorem of calculus on `(0,∞)`
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (a := (0:ℝ)) (m := (0:ℝ))
    hcont hderiv hDint hf1
  have hzero : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z)
      - (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) = 0 := by
    rw [hFTC]
    simp
  have hsplit := MeasureTheory.integral_sub hint1 hint2
  linarith

end Work.FTS.EllipticEst.Prop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.HkNorm_le_of_HkSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh



end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SinCompleteAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Auxiliary lemmas for `Work.FTS.EllipticEst.sin_complete_Ioc`.

The odd extension `sinOdd F` of `F` has all Fourier coefficients on the circle of period `2L`
equal (up to a constant) to the sine coefficients `∫_0^L F θ sin (n π θ / L) dθ`; Parseval's
identity then forces `F` to vanish a.e.
-/

open MeasureTheory Set
open scoped Interval

namespace Work.FTS.EllipticEst

/-- The odd extension of an `L²` function on `(0,L)` is `L²` on `(-L,L)`. -/
theorem sinOdd_memLp {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MemLp F 2 (volume.restrict (Ioc (0:ℝ) L))) :
    MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) L)) := by
  have hpos : MemLp (sinOdd F) 2 (volume.restrict (Ioc (0:ℝ) L)) := by
    refine MemLp.ae_eq ?_ (hmem.ofReal (K := ℂ))
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact (sinOdd_of_pos hx.1).symm
  have hneg : MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) 0)) := by
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ico (0:ℝ) L = Set.Ioc (-L) 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_Ioc]
      constructor
      · intro hx; exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1]⟩
      · intro hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmap : Measure.map (fun x : ℝ => -x) (volume.restrict (Ioc (-L) 0))
        = volume.restrict (Ico (0:ℝ) L) := by
      have h := measurableEmbedding_neg.restrict_map (volume : Measure ℝ) (Set.Ico (0:ℝ) L)
      rw [Measure.map_neg_eq_self] at h
      rw [hpre] at h
      exact h.symm
    have hg : MemLp (fun y : ℝ => (F y : ℂ)) 2 (volume.restrict (Ico (0:ℝ) L)) := by
      rw [Measure.restrict_congr_set
        (MeasureTheory.Ico_ae_eq_Ioc' (μ := volume) (a := (0:ℝ)) (b := L) (by simp) (by simp))]
      exact hmem.ofReal (K := ℂ)
    have hcomp : MemLp (fun x : ℝ => (F (-x) : ℂ)) 2 (volume.restrict (Ioc (-L) 0)) := by
      have h' : MemLp (fun y : ℝ => (F y : ℂ)) 2
          (Measure.map (fun x : ℝ => -x) (volume.restrict (Ioc (-L) 0))) := by
        rw [hmap]; exact hg
      have h2 := h'.comp_of_map (f := fun x : ℝ => -x) measurable_neg.aemeasurable
      exact h2
    refine MemLp.ae_eq ?_ (memLp_neg_iff.mpr hcomp)
    rw [← Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc' (μ := volume) (a := (-L)) (b := (0:ℝ)) (by simp))]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    simp only [Pi.neg_apply, sinOdd_of_neg hx.2]
  have hμ : volume.restrict (Ioc (-L) L)
      = volume.restrict (Ioc (-L) 0) + volume.restrict (Ioc (0:ℝ) L) := by
    have hun : Set.Ioc (-L) L = Set.Ioc (-L) 0 ∪ Set.Ioc (0:ℝ) L := by
      ext x
      simp only [Set.mem_Ioc, Set.mem_union]
      constructor
      · intro hx
        by_cases h : x ≤ 0
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr ⟨lt_of_not_ge h, hx.2⟩
      · rintro (hx | hx)
        · exact ⟨hx.1, by linarith [hx.2]⟩
        · exact ⟨by linarith [hx.1], hx.2⟩
    have hd : Disjoint (Set.Ioc (-L) 0) (Set.Ioc (0:ℝ) L) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx'.1 (not_lt.mpr hx.2)
    rw [hun, Measure.restrict_union hd measurableSet_Ioc]
  rw [hμ]
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · exact hneg.aestronglyMeasurable.add_measure hpos.aestronglyMeasurable
  · rw [integrable_add_measure]
    exact ⟨(memLp_two_iff_integrable_sq_norm hneg.aestronglyMeasurable).mp hneg,
      (memLp_two_iff_integrable_sq_norm hpos.aestronglyMeasurable).mp hpos⟩

/-- If all the sine coefficients `∫_0^L F θ sin (n π θ / L) dθ` for `n ≥ 1` vanish, then the
same integrals vanish for *all* integer frequencies, as complex integrals. -/
theorem sinInt_eq_zero {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (h : ∀ n : ℕ, 0 < n → ∫ θ in (0:ℝ)..L, F θ * Real.sin (n * Real.pi * θ / L) = 0) :
    ∀ m : ℤ, ∫ θ in (0:ℝ)..L, (Real.sin (Real.pi * m * θ / L) : ℂ) * (F θ : ℂ) = 0 := by
  have hcast : ∀ m : ℤ,
      (∫ θ in (0:ℝ)..L, (Real.sin (Real.pi * m * θ / L) : ℂ) * (F θ : ℂ))
        = ((∫ θ in (0:ℝ)..L, Real.sin (Real.pi * m * θ / L) * F θ : ℝ) : ℂ) := by
    intro m
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Complex.ofReal_mul]
  have key : ∀ k : ℤ, 0 < k →
      (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * k * θ / L) * F θ) = 0 := by
    intro k hk
    have hk0 : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
    have hk' : 0 < k.toNat := by
      refine Nat.pos_of_ne_zero (fun h0 => ?_)
      rw [h0] at hk0
      simp at hk0
      omega
    have hkR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hk0
    have h1 := h k.toNat hk'
    have h2 : (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * k * θ / L) * F θ)
        = ∫ θ in (0:ℝ)..L, F θ * Real.sin (k.toNat * Real.pi * θ / L) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [hkR]
      rw [show Real.pi * (k : ℝ) * θ / L = (k : ℝ) * Real.pi * θ / L from by ring]
      ring
    rw [h2, h1]
  intro m
  rw [hcast m]
  have hreal : (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * m * θ / L) * F θ) = 0 := by
    rcases lt_trichotomy m 0 with hm | hm | hm
    · have hmn : 0 < -m := by omega
      have hpt : ∀ θ : ℝ, Real.sin (Real.pi * (m : ℝ) * θ / L) * F θ
          = -(Real.sin (Real.pi * (-(m : ℝ)) * θ / L) * F θ) := by
        intro θ
        have harg : Real.pi * (m : ℝ) * θ / L = -(Real.pi * (-(m : ℝ)) * θ / L) := by ring
        rw [harg, Real.sin_neg]
        ring
      have hargh : (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * m * θ / L) * F θ)
          = -(∫ θ in (0:ℝ)..L, Real.sin (Real.pi * (-m) * θ / L) * F θ) := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
      rw [hargh, neg_eq_zero]
      simpa using key (-m) hmn
    · rw [hm]; simp
    · exact key m hm
  rw [hreal, Complex.ofReal_zero]

/-- If the odd extension of `F` has vanishing `L²` norm on `Ioc (-L) L`, then `F` vanishes a.e.
on `Ioc 0 L`. -/
theorem sinOdd_ae_eq_zero {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) L)))
    (hint : ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2 = 0) :
    F =ᵐ[volume.restrict (Ioc (0:ℝ) L)] 0 := by
  have hInt : Integrable (fun x => ‖sinOdd F x‖ ^ 2) (volume.restrict (Ioc (-L) L)) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hII : IntervalIntegrable (fun x => ‖sinOdd F x‖ ^ 2) volume (-L) L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (-L : ℝ) ≤ L)]
    exact hInt
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (-L) L ∪ Ioc L (-L))] (fun x => ‖sinOdd F x‖ ^ 2) :=
    Filter.Eventually.of_forall fun x => by positivity
  have hzero := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnn hII).mp hint
  have hU : Ioc (-L) L ∪ Ioc L (-L) = Ioc (-L) L := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc]
    refine ⟨fun h => ?_, fun h => Or.inl h⟩
    rcases h with h | h
    · exact h
    · exact absurd (lt_of_lt_of_le h.1 h.2) (not_lt.mpr (by linarith : (-L : ℝ) ≤ L))
  rw [hU] at hzero
  have h1 : sinOdd F =ᵐ[volume.restrict (Ioc (-L) L)] 0 := by
    filter_upwards [hzero] with x hx
    simpa [sq_eq_zero_iff, norm_eq_zero] using hx
  have hsub : Ioc (0:ℝ) L ⊆ Ioc (-L) L := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have h2 : sinOdd F =ᵐ[volume.restrict (Ioc (0:ℝ) L)] 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub h1
  filter_upwards [h2, self_mem_ae_restrict measurableSet_Ioc] with x hx hxm
  rw [sinOdd_of_pos hxm.1] at hx
  exact Complex.ofReal_eq_zero.mp hx

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.integrableOn_sq_mul_sin_rpow_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory Set Filter
open scoped Real Topology



end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.lightInvBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Real

namespace Work.FTS.EllipticEst.TT

noncomputable section












end

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TanTheta


/-! ### This statement is FALSE as written: it is missing a measurability hypothesis

`MeasureTheory.Integrable f μ` unfolds to `AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`
(see `Mathlib.MeasureTheory.Function.L1Space.Integrable`) and `IntegrableOn f s μ` is, by
definition, `Integrable f (μ.restrict s)`.  Hence the *conclusion* above demands that
`fun θ => f θ * g θ * sin (2*θ) ^ (-η)` be a.e. strongly measurable, and that does **not**
follow from the two hypotheses:

* take `η = 0`, `g = fun _ => 1` and `f = 1_A - 1_{Aᶜ}` where `A ⊆ (0, π/2)` is not Lebesgue
  measurable (such an `A` exists in Lean's ambient classical logic — a Vitali set; note that
  `MeasureTheory.MeasureSpace ℝ` is the *Borel* σ-algebra, `borel ℝ`, which is not complete).
  Then `f ^ 2 = 1`, so both hypotheses hold (`(0, π/2)` has finite measure), while the
  conclusion would say that `f` is integrable, i.e. a.e. equal to a measurable function; that
  is false, since then `A = {θ ∈ (0, π/2) | f θ = 1}` would differ from a Borel set by a null
  set, hence would be Lebesgue measurable.
* Equivalently: the hypothesis `Integrable (fun θ => f θ ^ 2 * w θ)` only makes `f ^ 2 * w`
  (hence `f ^ 2`) a.e. measurable.  A.e. measurability of a *square* does not imply a.e.
  measurability of the function: the sign is unrecoverable (`(±1) ^ 2 = 1`), and Lean's `ℝ`
  carries the Borel σ-algebra, where non-measurable sign functions exist.  (Note that
  `Integrable.aestronglyMeasurable` applied to the hypothesis only yields measurability of
  `f ^ 2 * sin(2θ) ^ (-η)`, never of `f` itself.)

In the intended application `f` and `g` are slices of smooth (in particular measurable)
functions, so adding a.e. measurability of `f` and `g` is harmless.

**Repair applied here.**  `integrable_mul_of_sq_weight` above now carries the two extra
hypotheses `AEMeasurable f (volume.restrict (Ioo 0 (π/2)))` and
`AEMeasurable g (volume.restrict (Ioo 0 (π/2)))` (which hold whenever `f`, `g` are continuous
on the interval, by `ContinuousOn.aemeasurable`) and is proved by re-exporting the sorry-free
`Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable` of the sibling
module `Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable`.
The name is kept so that existing imports continue to build; a caller of the old
(measurability-free) form must now supply the two measurability facts, which is the *only*
change. -/

end Work.FTS.EllipticEst.TanTheta
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.integrable_wrho_products =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Auxiliary lemmas

The auxiliary facts used by `integrable_wrho_products`: the bound `|ρ| ≤ 1/2` on `(0, π/2)`,
the integrability of the weight `sin(2θ)^{-η}` there, the pointwise bounds for the two products
(one via the bounds on `ψ` and `ψ'`, one via the algebraic identity of `halg`), and the
consequence `ψ θ = (cos θ ψ'' θ - u'' θ - 2 sin θ ψ' θ)/cos θ` of that identity. -/


/-- The weight `sin(2θ)^{-η}` is integrable on `(0, π/2)` for `η < 1`. -/
theorem integrableOn_sin_two_rpow_neg (η : ℝ) (hη1 : η < 1) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const (-η)).aestronglyMeasurable
  have hfin : (volume : Measure ℝ) (Set.Ioo 0 (Real.pi / 2)) ≠ ⊤ := by
    have hle : (volume : Measure ℝ) (Set.Ioo 0 (Real.pi / 2))
        ≤ (volume : Measure ℝ) (Set.Icc 0 (Real.pi / 2)) :=
      measure_mono Set.Ioo_subset_Icc_self
    have htop : (volume : Measure ℝ) (Set.Icc 0 (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    exact ne_of_lt (lt_of_le_of_lt hle htop)
  by_cases hη : η ≤ 0
  · refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ))
      (integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ)) hfin) hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsin.le _)]
    exact Real.rpow_le_one hsin.le (Real.sin_le_one _) (by linarith)
  · have hηpos : 0 < η := not_le.mp hη
    refine Integrable.mono'
      (g := fun θ : ℝ => (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)))
      ((Work.Spaces.integrableOn_majorant_rpow η hηpos hη1).mono_set Set.Ioo_subset_Icc_self)
      hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsin.le _)]
    exact Work.Spaces.sin_rpow_le_majorant η θ hηpos ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩




/-! ## The main theorem -/


end Work.FTS.EllipticEst.TanTheta
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.psi_contdiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TanTheta


end Work.FTS.EllipticEst.TanTheta
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.psi_deriv_formula =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TanTheta


end Work.FTS.EllipticEst.TanTheta
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.psi_second_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TanTheta

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedSimpArgs false

/-- **The chain rule for `u = cos θ · ψ`.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then with
`ψ = u / cos` one has `u''(θ) = ψ''(θ)·cos θ - 2·ψ'(θ)·sin θ - ψ(θ)·cos θ`.

Route: near `θ` the identity `u = ψ · cos` holds (as `cos ≠ 0`), so `u' = ψ'·cos - ψ·sin` as
functions near `θ`; differentiating that exhibited expression at `θ` (product rule, for which
`ψ'` must be differentiable at `θ`, which follows from `ψ` being `C²` there since it is the
quotient of the `C²` function `u` by the nonvanishing smooth function `cos`) gives the claim. -/
private lemma deriv_deriv_eq_div_cos (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv u) θ
      = deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ * Real.cos θ
        - 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        - (u θ / Real.cos θ) * Real.cos θ := by
  obtain ⟨s, hs_mem, hs_reg⟩ := hu.contDiffOn le_rfl (by simp)
  have hmem : interior s ∈ 𝓝 θ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs_mem)
  have hreg : ContDiffOn ℝ 2 u (interior s) := hs_reg.mono interior_subset
  have hdiff : ∀ t ∈ interior s, DifferentiableAt ℝ u t := fun t ht =>
    (hreg.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds ht)
  have hcos_nhds : ∀ᶠ t in 𝓝 θ, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hcos
  -- `u' = ψ' · cos - ψ · sin`, as an eventual equality of functions
  have heq_deriv : deriv u =ᶠ[𝓝 θ]
      fun t : ℝ =>
        deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t - (u t / Real.cos t) * Real.sin t := by
    filter_upwards [hcos_nhds, hmem] with t ht hts
    have heqt : u =ᶠ[𝓝 t] fun s : ℝ => (u s / Real.cos s) * Real.cos s := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne ht] with s hs
      exact (div_mul_cancel₀ (u s) hs).symm
    have hd : deriv (fun s : ℝ => (u s / Real.cos s) * Real.cos s) t
        = deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
          + (u t / Real.cos t) * (-Real.sin t) := by
      have hVt : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) t :=
        (hdiff t hts).div Real.differentiableAt_cos ht
      have h3 : HasDerivAt (fun s : ℝ => (u s / Real.cos s) * Real.cos s)
          (deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
            + (u t / Real.cos t) * (-Real.sin t)) t :=
        hVt.hasDerivAt.mul (Real.hasDerivAt_cos t)
      exact h3.deriv
    rw [heqt.deriv_eq, hd]
    ring
  rw [heq_deriv.deriv_eq]
  -- the two factors of the exhibited expression are differentiable at `θ`
  have hVd : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) θ :=
    (hu.div (Real.contDiff_cos.contDiffAt) hcos).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (deriv (fun s : ℝ => u s / Real.cos s)) θ :=
    ((hu.div (Real.contDiff_cos.contDiffAt) hcos).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by simp)
  have h1 : HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t)
      (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
        + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ)) θ :=
    hDd.hasDerivAt.mul (Real.hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun t : ℝ => (u t / Real.cos t) * Real.sin t)
      (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ) θ :=
    hVd.hasDerivAt.mul (Real.hasDerivAt_sin θ)
  have h3 := h1.sub h2
  have h4 : deriv (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
        - (u t / Real.cos t) * Real.sin t) θ
      = (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
          + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ))
        - (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
            + (u θ / Real.cos θ) * Real.cos θ) := h3.deriv
  rw [h4]
  ring

/-- The second derivative of `ψ = u / cos` satisfies, on `(0, π/2)`,
`cos θ · ψ'' θ = u'' θ + cos θ · ψ θ + 2 sin θ · ψ' θ`
(this is the rearrangement of `u'' = -cos θ ψ - 2 sin θ ψ' + cos θ ψ''`).

Route: on `(0, π/2)` one has `u = cos · ψ` (since `cos θ ≠ 0`), so the second derivative of
`θ ↦ Real.cos θ * psi u θ` equals `deriv (deriv u)`; expand that second derivative with the
product rule twice (`HasDerivAt.mul`, `.congr_of_eventuallyEq` to move between `u` and
`cos * ψ`, `.deriv`) and use `psi_deriv_formula` for `ψ'` (or redo the quotient rule). -/
theorem psi_second_deriv (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ * deriv (deriv (Work.FTS.EllipticEst.TanTheta.psi u)) θ
      = deriv (deriv u) θ + Real.cos θ * Work.FTS.EllipticEst.TanTheta.psi u θ
        + 2 * Real.sin θ * deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ := by
  have hθI : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have huAt : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθI)
  have h := deriv_deriv_eq_div_cos u huAt hc
  change Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
      = deriv (deriv u) θ + Real.cos θ * (u θ / Real.cos θ)
        + 2 * Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ
  rw [h]
  ring

end Work.FTS.EllipticEst.TanTheta
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.wrho_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.EllipticEst.TanTheta

/-- On `(0, π/2)` the weight `ρ = sin θ · cos θ · sin(2θ)^{-η}` equals `(1/2) sin(2θ)^{1-η}`
(using `sin(2θ) = 2 sin θ cos θ` and `Real.rpow_add` at the positive base `sin (2θ)`). -/
theorem wrho_eventuallyEq (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    wrho η =ᶠ[𝓝 θ] fun θ' => (1 / 2) * (Real.sin (2 * θ')) ^ (1 - η) := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
  have hpos : 0 < Real.sin (2 * θ') :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1]) (by linarith [hθ'.2])
  show Real.sin θ' * Real.cos θ' * (Real.sin (2 * θ')) ^ (-η)
      = (1 / 2) * (Real.sin (2 * θ')) ^ (1 - η)
  have h1 : Real.sin θ' * Real.cos θ' = Real.sin (2 * θ') / 2 := by
    rw [Real.sin_two_mul]; ring
  have h2 : Real.sin (2 * θ') * (Real.sin (2 * θ')) ^ (-η)
      = (Real.sin (2 * θ')) ^ (1 - η) := by
    have h3 := Real.rpow_add hpos (1 : ℝ) (-η)
    rw [Real.rpow_one, show (1 : ℝ) + -η = 1 - η by ring] at h3
    exact h3.symm
  rw [h1,
    show Real.sin (2 * θ') / 2 * (Real.sin (2 * θ')) ^ (-η)
        = (1 / 2) * (Real.sin (2 * θ') * (Real.sin (2 * θ')) ^ (-η)) by ring,
    h2]

/-- The derivative of the integration weight `ρ θ = sin θ cos θ sin(2θ)^{-η}` on `(0, π/2)`:
`ρ' θ = (1-η) cos(2θ) sin(2θ)^{-η}`.  (Note `sin θ cos θ = sin(2θ)/2`, so on the open interval
`ρ = (1/2) sin(2θ)^{1-η}`, whose derivative is `(1-η) cos(2θ) sin(2θ)^{-η}`; the definition
`wrhoD` in `Submission/Work/FTS/EllipticEst/TanTheta/Basic.lean` matches this.)

Route: `ρ = (1/2) · s^{1-η}` with `s θ = sin(2θ)`, using `Real.rpow_add` at the positive base
`sin (2θ)` (`Work.FTS.H2.sin_two_pos_of_Ioo` in `Submission/Work/FTS/H2/STBasic.lean`, or
`Real.sin_pos_of_pos_of_lt_pi`); then differentiate `s ↦ s^{1-η}` with
`Real.hasDerivAt_rpow_const` and the chain rule with
`HasDerivAt (fun θ => Real.sin (2 θ)) (2 cos (2θ)) θ`, and finish with `Real.rpow_add` and
`ring`. -/
theorem wrho_deriv (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Work.FTS.EllipticEst.TanTheta.wrho η)
      (Work.FTS.EllipticEst.TanTheta.wrhoD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := hasDerivAt_const_mul (2 : ℝ)
    exact (HasDerivAt.comp (hh₂ := Real.hasDerivAt_sin (2 * θ)) (hh := h1)).congr_deriv (by ring)
  have hrpow :
      HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (1 - η))
        (2 * Real.cos (2 * θ) * (1 - η) * (Real.sin (2 * θ)) ^ (1 - η - 1)) θ :=
    hsin.rpow_const (p := 1 - η) (Or.inl (ne_of_gt hspos))
  have hval :
      (1 / 2) * (2 * Real.cos (2 * θ) * (1 - η) * (Real.sin (2 * θ)) ^ (1 - η - 1))
        = Work.FTS.EllipticEst.TanTheta.wrhoD η θ := by
    simp only [Work.FTS.EllipticEst.TanTheta.wrhoD]
    rw [show (1 : ℝ) - η - 1 = -η by ring]
    ring
  have hconst :
      HasDerivAt (fun θ' : ℝ => (1 / 2) * (Real.sin (2 * θ')) ^ (1 - η))
        (Work.FTS.EllipticEst.TanTheta.wrhoD η θ) θ :=
    (HasDerivAt.const_mul (1 / 2 : ℝ) hrpow).congr_deriv hval
  exact HasDerivAt.congr_of_eventuallyEq hconst (wrho_eventuallyEq η hθ)

end Work.FTS.EllipticEst.TanTheta
end
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.powerHardyFinite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst.UopHk

/-! ## The slice estimate -/


/-! ## The weighted Cauchy–Schwarz bound at the lower endpoint -/



end Work.FTS.EllipticEst.UopHk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.continuousOn_of_primitive_of_sqrt_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-! ## Auxiliary estimates

We prove the continuity of a function `u` whose increments are the integral of `v r / r`,
where `v` obeys the weighted square-root bound of the paper (with the radial weight
`w r = (1+r)²/r²`).  The only point that requires care is that no measurability of `v` is
assumed; the estimate is therefore formulated with `intervalIntegral.norm_integral_le_of_norm_le`,
which is valid for arbitrary integrands.
-/

/-- For every real `x`, `√x ≤ |x| + 1`. -/
private lemma sqrt_le_abs_add_one (x : ℝ) : Real.sqrt x ≤ |x| + 1 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [abs_of_nonneg hx]
    nlinarith [sq_nonneg x]
  · rw [Real.sqrt_eq_zero_of_nonpos hx.le]
    positivity

/-- If `|f|` is dominated pointwise on `(s,z]` by an interval-integrable function `Θ`, then the
integral of `f` over `[s,z]` is dominated by the integral of `Θ`.  No measurability of `f` is
required: if `f` fails to be interval integrable its integral is `0` by definition. -/
private lemma abs_intervalIntegral_le_integral_of_abs_le {f Θ : ℝ → ℝ} {s z : ℝ}
    (hsz : s ≤ z) (hΘ : IntervalIntegrable Θ volume s z)
    (hbd : ∀ t ∈ Set.Ioc s z, |f t| ≤ Θ t) :
    |∫ t in s..z, f t| ≤ ∫ t in s..z, Θ t := by
  have h1 : ‖∫ t in s..z, f t‖ ≤ ∫ t in s..z, Θ t :=
    intervalIntegral.norm_integral_le_of_norm_le hsz
      (Filter.Eventually.of_forall fun t ht => by
        simpa only [Real.norm_eq_abs] using hbd t ht) hΘ
  rwa [Real.norm_eq_abs] at h1

/-- **Continuity from the weighted square-root bound.**  If `u` has `v r / r` as its derivative
in the sense of the integral identity `u z - u s = ∫ r in s..z, v r / r` for `0 < s ≤ z`, and
`|v r| ≤ √(π/2) √(A r) / w r` with `A` integrable on `(0,∞)` and `w r = (1+r)²/r²`, then `u` is
continuous on `(0,∞)`.

The proof only uses the local `L¹` bound `√(A r) ≤ 1 + |A r|`; it is a genuine primitive
continuity argument, no differentiability of `u` is needed. -/
theorem continuousOn_of_primitive_of_sqrt_bound {u v A : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A (Set.Ioi 0))
    (hbd : ∀ r ∈ Set.Ioi (0 : ℝ),
      |v r| ≤ Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r)
    (hchain : ∀ s z : ℝ, 0 < s → s ≤ z → u z - u s = ∫ r in s..z, v r / r) :
    ContinuousOn u (Set.Ioi 0) := by
  -- The majorant `Θ r = √(π/2) (1 + |A r|)`.
  let Θ : ℝ → ℝ := fun r => Real.sqrt (π / 2) * (|A r| + 1)
  have hΘnonneg : ∀ r, 0 ≤ Θ r := fun r =>
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  -- Pointwise bound `|v r / r| ≤ Θ r` for `r > 0`.
  have hmajor : ∀ r ∈ Set.Ioi (0 : ℝ), |v r / r| ≤ Θ r := by
    intro r hr
    have hrpos : 0 < r := hr
    have hwpos : 0 < Work.Spaces.w r := by rw [Work.Spaces.w]; positivity
    have key : (Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r) / r
        = Real.sqrt (π / 2) * Real.sqrt (A r) * (r / (1 + r) ^ 2) := by
      rw [Work.Spaces.w]; field_simp
    have hratio : r / (1 + r) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hrpos.le]
    have hstep : (Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r) / r
        ≤ Real.sqrt (π / 2) * Real.sqrt (A r) := by
      rw [key]
      have h := mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (Real.sqrt_nonneg (π / 2)) (Real.sqrt_nonneg (A r)))
      simpa using h
    calc |v r / r| = |v r| / r := by rw [abs_div, abs_of_pos hrpos]
      _ ≤ (Real.sqrt (π / 2) * Real.sqrt (A r) / Work.Spaces.w r) / r :=
            div_le_div_of_nonneg_right (hbd r hr) hrpos.le
      _ ≤ Real.sqrt (π / 2) * Real.sqrt (A r) := hstep
      _ ≤ Θ r := mul_le_mul_of_nonneg_left (sqrt_le_abs_add_one (A r)) (Real.sqrt_nonneg _)
  -- Reduce to continuity at a single point `x₀ > 0`.
  intro x₀ hx₀
  have hx₀pos : 0 < x₀ := hx₀
  set lo : ℝ := x₀ / 2 with hlo_def
  set hi : ℝ := 2 * x₀ with hhi_def
  have hlo_pos : 0 < lo := by rw [hlo_def]; linarith
  have hlo_lt : lo < x₀ := by rw [hlo_def]; linarith
  have hlt_hi : x₀ < hi := by rw [hhi_def]; linarith
  have hlo_hi : lo ≤ hi := le_of_lt (lt_trans hlo_lt hlt_hi)
  -- Integrability of the majorant on `[lo,hi]`.
  have hΘIcc : MeasureTheory.IntegrableOn Θ (Set.Icc lo hi) := by
    have hsub : Set.Icc lo hi ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hlo_pos hx.1
    have hA' : MeasureTheory.IntegrableOn A (Set.Icc lo hi) := hA.mono_set hsub
    have habs : MeasureTheory.IntegrableOn (fun r => |A r|) (Set.Icc lo hi) := hA'.abs
    have h1 : MeasureTheory.IntegrableOn (fun r => |A r| + 1) (Set.Icc lo hi) :=
      habs.add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by simp))
    exact h1.const_mul (Real.sqrt (π / 2))
  have hminorInt : ∀ {s z : ℝ}, lo ≤ s → s ≤ z → z ≤ hi → IntervalIntegrable Θ volume s z := by
    intro s z hs hsz hz
    have hm : MeasureTheory.IntegrableOn Θ (Set.Icc s z) :=
      hΘIcc.mono_set (Set.Icc_subset_Icc hs hz)
    have hm' : MeasureTheory.IntegrableOn Θ (Set.uIcc s z) := by
      rw [Set.uIcc_of_le hsz]; exact hm
    exact hm'.intervalIntegrable
  -- The primitive `z ↦ ∫ t in x₀..z, Θ t` of the majorant is continuous at `x₀`.
  have hGcont : ContinuousOn (fun z => ∫ t in x₀..z, Θ t) (Set.uIcc lo hi) :=
    intervalIntegral.continuousOn_primitive_interval' (hminorInt le_rfl hlo_hi le_rfl)
      (by rw [Set.uIcc_of_le hlo_hi]; exact ⟨hlo_lt.le, hlt_hi.le⟩)
  have hGmem : Set.uIcc lo hi ∈ 𝓝 x₀ := by
    rw [Set.uIcc_of_le hlo_hi]; exact Icc_mem_nhds hlo_lt hlt_hi
  have hGat : ContinuousAt (fun z => ∫ t in x₀..z, Θ t) x₀ := hGcont.continuousAt hGmem
  have hGtend : Filter.Tendsto (fun z => ‖∫ t in x₀..z, Θ t‖) (𝓝 x₀) (𝓝 0) := by
    have h := hGat.norm
    simpa [ContinuousAt] using h
  -- On a neighbourhood of `x₀`, `u · - u x₀` is squeezed by that primitive.
  have hev : ∀ᶠ z in 𝓝 x₀, ‖u z - u x₀‖ ≤ ‖∫ t in x₀..z, Θ t‖ := by
    filter_upwards [Icc_mem_nhds hlo_lt hlt_hi] with z hz
    have hzpos : 0 < z := lt_of_lt_of_le hlo_pos hz.1
    rcases le_total x₀ z with hxz | hzx
    · -- `x₀ ≤ z`
      have hrepr : u z - u x₀ = ∫ r in x₀..z, v r / r := hchain x₀ z hx₀pos hxz
      have hmaj : |∫ r in x₀..z, v r / r| ≤ ∫ r in x₀..z, Θ r :=
        abs_intervalIntegral_le_integral_of_abs_le (f := fun r => v r / r) (Θ := Θ) hxz
          (hminorInt hlo_lt.le hxz hz.2)
          (fun t ht => hmajor t (Set.mem_Ioi.mpr (lt_trans hx₀pos ht.1)))
      have hGz : ‖∫ t in x₀..z, Θ t‖ = ∫ r in x₀..z, Θ r := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (intervalIntegral.integral_nonneg hxz (fun t _ => hΘnonneg t))]
      calc ‖u z - u x₀‖ = |∫ r in x₀..z, v r / r| := by rw [hrepr, Real.norm_eq_abs]
        _ ≤ ∫ r in x₀..z, Θ r := hmaj
        _ = ‖∫ t in x₀..z, Θ t‖ := hGz.symm
    · -- `z ≤ x₀`
      have hrepr : u z - u x₀ = -(∫ r in z..x₀, v r / r) := by
        have h := hchain z x₀ hzpos hzx
        linarith
      have hmaj : |∫ r in z..x₀, v r / r| ≤ ∫ r in z..x₀, Θ r :=
        abs_intervalIntegral_le_integral_of_abs_le (f := fun r => v r / r) (Θ := Θ) hzx
          (hminorInt hz.1 hzx hlt_hi.le)
          (fun t ht => hmajor t (Set.mem_Ioi.mpr (lt_trans hzpos ht.1)))
      have hGz : ‖∫ t in x₀..z, Θ t‖ = ∫ r in z..x₀, Θ r := by
        rw [intervalIntegral.integral_symm z x₀, norm_neg, Real.norm_eq_abs,
          abs_of_nonneg (intervalIntegral.integral_nonneg hzx (fun t _ => hΘnonneg t))]
      calc ‖u z - u x₀‖ = ‖-(∫ r in z..x₀, v r / r)‖ := by rw [hrepr]
        _ = |∫ r in z..x₀, v r / r| := by rw [norm_neg, Real.norm_eq_abs]
        _ ≤ ∫ r in z..x₀, Θ r := hmaj
        _ = ‖∫ t in x₀..z, Θ t‖ := hGz.symm
  -- Squeeze.
  have hnorm : Filter.Tendsto (fun z => ‖u z - u x₀‖) (𝓝 x₀) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun z => norm_nonneg _) hev hGtend
  have hdiff : Filter.Tendsto (fun z => u z - u x₀) (𝓝 x₀) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hcont : ContinuousAt u x₀ := by
    have h2 := hdiff.add_const (u x₀)
    have h3 : (fun z => (u z - u x₀) + u x₀) = u := by funext z; ring
    rw [h3] at h2
    simpa [ContinuousAt] using h2
  exact hcont.continuousWithinAt

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.harOp_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Hardy transform vanishes at `+∞`

If `|φ| ≤ M` on `(0,∞)` with `∫₀^∞ M² < ∞`, then for `β > 0`

  `z^{-β} ∫₀^z s^{β-1} φ(s) ds → 0`   as `z → ∞`.

The key point is that `M ∈ L²(0,∞)` and `|φ| ≤ M` (so `φ ∈ L²`); Cauchy–Schwarz splits the
integral at `s = 1`, and `∫₁^z s^{2β-2} ds` is `O(z^{2β-1})` (β > 1/2), `= log z` (β = 1/2) or
bounded (β < 1/2), which is exactly what is needed after multiplication by `z^{-β}`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.GsingAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary integrability of `s ↦ s ^ r` on `Ioc 1 z` -/

lemma integrableOn_rpow_Ioc (r z : ℝ) :
    IntegrableOn (fun s : ℝ => s ^ r) (Set.Ioc 1 z) := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ r) (Set.Icc 1 (max 1 z)) := fun x hx =>
    (Real.continuousAt_rpow_const x r
      (Or.inl (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)))).continuousWithinAt
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set
    (fun x hx => ⟨hx.1.le, le_trans hx.2 (le_max_right _ _)⟩)

lemma memLp_rpow_Ioc (r z : ℝ) :
    MemLp (fun s : ℝ => s ^ r) 2 (volume.restrict (Set.Ioc 1 z)) := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ r) (Set.Ioc 1 z) := fun x hx =>
    (Real.continuousAt_rpow_const x r
      (Or.inl (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)))).continuousWithinAt
  have h1 : AEStronglyMeasurable (fun s : ℝ => s ^ r) (volume.restrict (Set.Ioc 1 z)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  refine (memLp_two_iff_integrable_sq h1).mpr ?_
  refine IntegrableOn.congr_fun (integrableOn_rpow_Ioc (2 * r) z) (fun s hs => ?_)
    measurableSet_Ioc
  have hs0 : 0 ≤ s := by linarith [hs.1]
  rw [show (2 : ℝ) * r = r * 2 by ring, Real.rpow_mul hs0, Real.rpow_two]

lemma memLp_M_Ioc {M : ℝ → ℝ} (hM2 : IntegrableOn (fun s => (M s) ^ 2) (Set.Ioi 0))
    (hMex : AEMeasurable M (volume.restrict (Set.Ioi 0))) (z : ℝ) :
    MemLp M 2 (volume.restrict (Set.Ioc 1 z)) := by
  have hsub : Set.Ioc 1 z ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    show (0 : ℝ) < x
    linarith [hx.1]
  have h1 : AEStronglyMeasurable M (volume.restrict (Set.Ioc 1 z)) :=
    (hMex.mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq h1).mpr (hM2.mono_set hsub)

/-! ## The Cauchy–Schwarz bound on the tail -/

/-- The tail integral `∫_{Ioc 1 z} s^{β-1} φ s` is dominated by
`sqrt (∫_{Ioc 1 z} s^{2β-2}) * sqrt (∫_{Ioc 1 z} M²)`. -/
lemma abs_integral_Ioc_le (β : ℝ) {φ M : ℝ → ℝ}
    (hMnn : ∀ s, 0 ≤ M s)
    (hM2 : IntegrableOn (fun s => (M s) ^ 2) (Set.Ioi 0))
    (hMex : AEMeasurable M (volume.restrict (Set.Ioi 0)))
    (hφ : ∀ s, 0 < s → |φ s| ≤ M s) (z : ℝ) :
    |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
      ≤ Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
        * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2) := by
  have hW : MemLp (fun s : ℝ => s ^ (β - 1)) 2 (volume.restrict (Set.Ioc 1 z)) :=
    memLp_rpow_Ioc (β - 1) z
  have hM : MemLp M 2 (volume.restrict (Set.Ioc 1 z)) := memLp_M_Ioc hM2 hMex z
  have hcs := Work.Spaces.cs_integral (s := Set.Ioc 1 z)
    (u := fun s : ℝ => s ^ (β - 1)) (v := M) hW hM
  have hAeq : (∫ s in Set.Ioc 1 z, (s ^ (β - 1)) ^ 2)
      = ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 ≤ s := by linarith [hs.1]
    rw [show (2 : ℝ) * β - 2 = (β - 1) * 2 by ring, Real.rpow_mul hs0, Real.rpow_two]
  rw [hAeq] at hcs
  have hprod : MemLp (fun s : ℝ => s ^ (β - 1) * M s) 1 (volume.restrict (Set.Ioc 1 z)) :=
    hW.mul hM
  have hInt : Integrable (fun s : ℝ => s ^ (β - 1) * M s) (volume.restrict (Set.Ioc 1 z)) :=
    memLp_one_iff_integrable.mp hprod
  have hstep1 : |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
      ≤ ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s := by
    have h1 : |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
        ≤ ∫ s in Set.Ioc 1 z, |s ^ (β - 1) * φ s| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Set.Ioc 1 z)) (fun s : ℝ => s ^ (β - 1) * φ s))
    refine h1.trans ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun s => abs_nonneg _) hInt ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := by linarith [hs.1]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    exact mul_le_mul_of_nonneg_left (hφ s hs0) (Real.rpow_nonneg hs0.le _)
  have hnn : 0 ≤ ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s :=
    setIntegral_nonneg measurableSet_Ioc fun s hs =>
      mul_nonneg (Real.rpow_nonneg (by linarith [hs.1]) _) (hMnn s)
  have hA0 : 0 ≤ ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) :=
    setIntegral_nonneg measurableSet_Ioc fun s hs =>
      Real.rpow_nonneg (by linarith [hs.1]) _
  have hstep2 : ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s
      ≤ Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
        * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2) := by
    calc ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s
        = Real.sqrt ((∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
            * (∫ s in Set.Ioc 1 z, (M s) ^ 2)) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
            * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2) := Real.sqrt_mul hA0 _
  exact hstep1.trans hstep2

/-! ## The tail factor tends to `0` -/

lemma tail_factor_tendsto (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun z : ℝ => z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2)))
      atTop (nhds 0) := by
  have hnn : ∀ᶠ z : ℝ in atTop,
      0 ≤ z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact mul_nonneg (Real.rpow_nonneg hz _) (Real.sqrt_nonneg _)
  have hAz : ∀ z : ℝ, 1 ≤ z → β ≠ 1 / 2 → ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2)
      = (z ^ (2 * β - 1) - 1) / (2 * β - 1) := by
    intro z hz hβne
    rw [← intervalIntegral.integral_of_le hz]
    rw [integral_rpow (Or.inr ⟨fun h => hβne (by linarith),
      by rw [Set.uIcc_of_le hz]; rintro ⟨h1, _⟩; linarith⟩)]
    rw [show (2 : ℝ) * β - 2 + 1 = 2 * β - 1 by ring, Real.one_rpow]
  rcases lt_trichotomy β (1 / 2) with hlt | heq | hgt
  · -- β < 1/2 : the integral stays bounded
    have hbd : ∀ᶠ z : ℝ in atTop,
        z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (-β) / Real.sqrt (1 - 2 * β) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hzpos : 0 < z := by linarith
      have hAle : ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) ≤ 1 / (1 - 2 * β) := by
        have hkey : 1 / (1 - 2 * β) = -1 / (2 * β - 1) := by
          rw [div_eq_div_iff (by linarith) (by linarith)]; ring
        have hdiff : -1 / (2 * β - 1) - (z ^ (2 * β - 1) - 1) / (2 * β - 1)
            = z ^ (2 * β - 1) / (1 - 2 * β) := by
          rw [← sub_div, show (1 : ℝ) - 2 * β = -(2 * β - 1) by ring, div_neg, ← neg_div]
          congr 1
          ring
        rw [hAz z hz (by linarith), hkey, ← sub_nonneg, hdiff]
        exact div_nonneg (Real.rpow_nonneg hzpos.le _) (by linarith)
      have hsqrt : Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ Real.sqrt (1 / (1 - 2 * β)) := Real.sqrt_le_sqrt hAle
      calc z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (-β) * Real.sqrt (1 / (1 - 2 * β)) :=
            mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hzpos.le _)
        _ = z ^ (-β) / Real.sqrt (1 - 2 * β) := by
            rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]; ring
    have hlim : Tendsto (fun z : ℝ => z ^ (-β) / Real.sqrt (1 - 2 * β)) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop hβ).div_const (Real.sqrt (1 - 2 * β))
    exact squeeze_zero' hnn hbd hlim
  · -- β = 1/2 : the integral is `log z`
    subst heq
    rw [show (2 : ℝ) * (1 / 2) - 2 = (-1 : ℝ) by norm_num]
    have hev : (fun z : ℝ =>
          z ^ ((-(1 / 2) : ℝ)) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (-1 : ℝ)))
        =ᶠ[atTop] fun z : ℝ => Real.sqrt (z⁻¹ * Real.log z) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hzpos : 0 < z := by linarith
      have hAz1 : ∫ s in Set.Ioc 1 z, s ^ (-1 : ℝ) = Real.log z := by
        rw [← intervalIntegral.integral_of_le hz]
        rw [show (fun s : ℝ => s ^ (-1 : ℝ)) = fun s => s⁻¹ from funext fun s =>
          Real.rpow_neg_one s]
        rw [integral_inv (by rw [Set.uIcc_of_le hz]; rintro ⟨h1, _⟩; linarith)]
        rw [Real.log_div hzpos.ne' one_ne_zero, Real.log_one, sub_zero]
      have hsqz : Real.sqrt z⁻¹ = z ^ ((-(1 / 2) : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one z, ← Real.rpow_mul hzpos.le]
        congr 1
        ring
      rw [hAz1, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ z⁻¹), hsqz]
    refine Filter.Tendsto.congr' hev.symm ?_
    have hlog : Tendsto (fun z : ℝ => Real.log z / z) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun z : ℝ => Real.sqrt (Real.log z / z)) atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hlog
    have hsqrt0 : Tendsto (fun z : ℝ => Real.sqrt (z⁻¹ * Real.log z)) atTop (nhds 0) := by
      rw [← Real.sqrt_zero]
      refine Filter.Tendsto.congr' ?_ h2
      filter_upwards with z
      congr 1
      ring
    exact hsqrt0
  · -- 1/2 < β
    have hbd : ∀ᶠ z : ℝ in atTop,
        z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ ((-(1 / 2) : ℝ)) / Real.sqrt (2 * β - 1) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hzpos : 0 < z := by linarith
      have hden : 0 < 2 * β - 1 := by linarith
      have hAle : ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) ≤ z ^ (2 * β - 1) / (2 * β - 1) := by
        rw [hAz z hz (by linarith)]
        refine div_le_div_of_nonneg_right ?_ hden.le
        have hzp := Real.rpow_nonneg hzpos.le (2 * β - 1)
        linarith
      have hsqrt : Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (β - 1 / 2) / Real.sqrt (2 * β - 1) := by
        refine (Real.sqrt_le_sqrt hAle).trans (le_of_eq ?_)
        rw [Real.sqrt_div (Real.rpow_nonneg hzpos.le _)]
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hzpos.le]
        congr 1
        ring
      calc z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (-β) * (z ^ (β - 1 / 2) / Real.sqrt (2 * β - 1)) :=
            mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hzpos.le _)
        _ = z ^ ((-(1 / 2) : ℝ)) / Real.sqrt (2 * β - 1) := by
            rw [← mul_div_assoc, ← Real.rpow_add hzpos,
              show -β + (β - 1 / 2) = (-(1 / 2) : ℝ) by ring]
    have hlim : Tendsto (fun z : ℝ => z ^ ((-(1 / 2) : ℝ)) / Real.sqrt (2 * β - 1))
        atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).div_const
        (Real.sqrt (2 * β - 1))
    exact squeeze_zero' hnn hbd hlim

/-! ## The main statement -/

theorem harOp_tendsto_zero (β : ℝ) (hβ : 0 < β) (φ M : ℝ → ℝ)
    (hMnn : ∀ s, 0 ≤ M s)
    (hM2 : IntegrableOn (fun s => (M s) ^ 2) (Set.Ioi 0))
    (hMex : AEMeasurable M (volume.restrict (Set.Ioi 0)))
    (hφ : ∀ s, 0 < s → |φ s| ≤ M s) :
    Filter.Tendsto (fun z : ℝ => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * φ s)
      Filter.atTop (nhds 0) := by
  rcases em (∀ z : ℝ, 0 ≤ z →
      IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 0 z)) with hgood | hbad
  · -- main case: `s^{β-1}φ` is locally integrable
    set C : ℝ := ∫ s in Set.Ioc 0 1, s ^ (β - 1) * φ s with hC
    have hCint : IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 0 1) :=
      hgood 1 zero_le_one
    have hev : (fun z : ℝ => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * φ s) =ᶠ[atTop]
        fun z : ℝ => z ^ (-β) * (C + ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hz0 : (0 : ℝ) ≤ z := by linarith
      have hunion : Set.Ioc 0 1 ∪ Set.Ioc 1 z = Set.Ioc 0 z :=
        Set.Ioc_union_Ioc_eq_Ioc zero_le_one hz
      have hdisj : Disjoint (Set.Ioc 0 1) (Set.Ioc 1 z) :=
        Set.disjoint_left.mpr fun x hx1 hx2 => by linarith [hx1.2, hx2.1]
      have h2int : IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 1 z) :=
        (hgood z hz0).mono_set fun x hx => ⟨by linarith [hx.1], hx.2⟩
      rw [intervalIntegral.integral_of_le hz0, ← hunion,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hCint h2int]
      try ring
    refine Filter.Tendsto.congr' hev.symm ?_
    have h1 : Tendsto (fun z : ℝ => z ^ (-β) * C) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop hβ).mul_const C
    have h2 : Tendsto (fun z : ℝ => z ^ (-β) * ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s)
        atTop (nhds 0) := by
      have hB : 0 ≤ ∫ s in Set.Ioi 0, (M s) ^ 2 :=
        setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _
      have hbd2 : ∀ᶠ z : ℝ in atTop,
          |z ^ (-β) * ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
            ≤ z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
              * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
        have hz0 : (0 : ℝ) < z := by linarith
        have hbd := abs_integral_Ioc_le β hMnn hM2 hMex hφ z
        have hMz : ∫ s in Set.Ioc 1 z, (M s) ^ 2 ≤ ∫ s in Set.Ioi 0, (M s) ^ 2 :=
          MeasureTheory.setIntegral_mono_set hM2
            (Eventually.of_forall fun s => sq_nonneg _)
            (Eventually.of_forall fun s hs => by show (0 : ℝ) < s; linarith [hs.1])
        have hMsq : Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2)
            ≤ Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2) := Real.sqrt_le_sqrt hMz
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hz0.le _)]
        calc z ^ (-β) * |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
            ≤ z ^ (-β) * (Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
                * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2)) :=
              mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg hz0.le _)
          _ ≤ z ^ (-β) * (Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
                * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hMsq (Real.sqrt_nonneg _))
                (Real.rpow_nonneg hz0.le _)
          _ = z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
                * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2) := by ring
      have hlim2 : Tendsto (fun z : ℝ => z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z,
          s ^ (2 * β - 2)) * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2)) atTop (nhds 0) := by
        simpa using (tail_factor_tendsto β hβ).mul_const
          (Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2))
      have hsq : Tendsto (fun z : ℝ =>
          |z ^ (-β) * ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|) atTop (nhds 0) :=
        squeeze_zero' (Eventually.of_forall fun z => abs_nonneg _) hbd2 hlim2
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [Real.norm_eq_abs] using hsq
    have hsum : Tendsto (fun z : ℝ => z ^ (-β) * (C + ∫ s in Set.Ioc 1 z,
        s ^ (β - 1) * φ s)) atTop (nhds 0) := by
      simpa [mul_add] using h1.add h2
    exact hsum
  · -- degenerate case: the integral is `0` from some point on
    simp only [not_forall] at hbad
    obtain ⟨z0, hz0nn, hz0bad⟩ := hbad
    have hz0pos : 0 < z0 := by
      rcases lt_or_eq_of_le hz0nn with h | h
      · exact h
      · exfalso
        apply hz0bad
        rw [← h, Set.Ioc_self]
        exact integrableOn_empty
    have hev : (fun z : ℝ => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * φ s) =ᶠ[atTop]
        fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [eventually_ge_atTop z0] with z hz
      have hz0le : (0 : ℝ) ≤ z := le_trans hz0pos.le hz
      have hni : ¬ IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 0 z) :=
        fun hc => hz0bad (hc.mono_set (Set.Ioc_subset_Ioc_right hz))
      rw [intervalIntegral.integral_of_le hz0le, MeasureTheory.integral_undef hni, mul_zero]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

end Work.FTS.EllipticEst.GsingAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Algebraic identity underlying the weight computation: for a nonnegative base `s` and any
real exponent `e`, the square of `a * (w / s ^ e)` collects the powers of `s` into a single
real power, `(a * (w / s ^ e))² = a² w² s^{-2e}`.  (`s = 0` is allowed: both sides vanish
thanks to Lean's totalised `x ^ e = 0` for `x = 0`, `e ≠ 0`.) -/
private lemma mul_div_rpow_sq (a w s e : ℝ) (hs : 0 ≤ s) :
    (a * (w / s ^ e)) ^ 2 = a ^ 2 * w ^ 2 * s ^ (-(2 * e)) := by
  have h2 : (s ^ e) ^ ((2 : ℕ) : ℝ) = s ^ (e * ((2 : ℕ) : ℝ)) :=
    (Real.rpow_mul hs e ((2 : ℕ) : ℝ)).symm
  have he : e * ((2 : ℕ) : ℝ) = 2 * e := by ring
  rw [mul_pow, div_pow, ← Real.rpow_natCast (s ^ e) 2, h2, he]
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (2 * e)]
  ring

theorem mul_w_sin_rpow_sq (a w : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (a * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = a ^ 2 * w ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have he : 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta := by
    norm_num [Work.Spaces.eta]
  have h := mul_div_rpow_sq a w (Real.sin (2 * θ)) (Work.Spaces.eta / 2) hs
  rw [he] at h
  exact h

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.PthSlotPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Baux


end Work.FTS.EllipticEst.remov.Baux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.angSum_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `angSum_sq_le`

A binomial-convolution square bound.  With `c_j = (k+1).choose j` and
`d_j = sin^{(k+1-j)}(θ)` (the `k+1-j`-st iterated derivative of `sin` at `θ`),
Cauchy–Schwarz gives

  `(Σ_j c_j d_j x_j)² ≤ (Σ_j (c_j d_j)²)·(Σ_j x_j²)`,

and since `|sin^{(m)}(θ)| ≤ 1` for every `m` (`Real.abs_iteratedDeriv_sin_le_one`) and
`Σ_j c_j² ≤ (Σ_j c_j)² = (2^{k+1})²` (binomial theorem, all terms nonnegative) this is

  `(Σ_j c_j d_j x_j)² ≤ (2^{k+1})²·(Σ_j x_j²) ≤ (2^{k+1})²·(k+2)·(Σ_j x_j²)`,

which is the statement.
-/

namespace Work.FTS.EllipticEst.remov.Baux

theorem angSum_sq_le (k : ℕ) (x : ℕ → ℝ) (θ : ℝ) :
    (∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
        * iteratedDeriv (k + 1 - j) Real.sin θ * x j) ^ 2
      ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2)
          * ∑ j ∈ Finset.range (k + 2), (x j) ^ 2 := by
  classical
  set t := Finset.range (k + 2) with ht
  -- The binomial sum `Σ_j (k+1).choose j = 2^{k+1}`.
  have hrange : Finset.range (k + 1 + 1) = t := by rw [ht]
  have hchoose : ∑ j ∈ t, ((k + 1).choose j : ℝ) = (2 : ℝ) ^ (k + 1) := by
    rw [← hrange, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  -- Pointwise: `(c_j·d_j)² ≤ c_j²` since `|d_j| ≤ 1`.
  have hterm : ∀ j ∈ t, (((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2
      ≤ ((k + 1).choose j : ℝ) ^ 2 := by
    intro j hj
    rw [mul_pow]
    have hd : (iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (Real.abs_iteratedDeriv_sin_le_one _ _)
    simpa using mul_le_mul_of_nonneg_left hd (sq_nonneg ((k + 1).choose j : ℝ))
  -- `Σ_j c_j² ≤ (2^{k+1})²`.
  have hsum_sq :
      ∑ j ∈ t, (((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2
        ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsingle : ∀ j ∈ t, ((k + 1).choose j : ℝ) ^ 2
        ≤ ((k + 1).choose j : ℝ) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) := by
      intro j hj
      have hle : ((k + 1).choose j : ℝ) ≤ ∑ i ∈ t, ((k + 1).choose i : ℝ) :=
        Finset.single_le_sum (f := fun i => ((k + 1).choose i : ℝ))
          (fun i _ => Nat.cast_nonneg _) hj
      calc ((k + 1).choose j : ℝ) ^ 2
          = ((k + 1).choose j : ℝ) * ((k + 1).choose j : ℝ) := by ring
        _ ≤ ((k + 1).choose j : ℝ) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) :=
            mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    calc ∑ j ∈ t, ((k + 1).choose j : ℝ) ^ 2
        ≤ ∑ j ∈ t, ((k + 1).choose j : ℝ) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) :=
          Finset.sum_le_sum hsingle
      _ = (∑ j ∈ t, ((k + 1).choose j : ℝ)) * (∑ i ∈ t, ((k + 1).choose i : ℝ)) := by
          rw [Finset.sum_mul]
      _ = ((2 : ℝ) ^ (k + 1)) ^ 2 := by rw [hchoose]; ring
  have hX : 0 ≤ ∑ j ∈ t, (x j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hk2 : (1 : ℝ) ≤ (k : ℝ) + 2 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  -- Cauchy–Schwarz and the small bookkeeping for the factor `k+2 ≥ 1`.
  calc (∑ j ∈ t, ((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ * x j) ^ 2
      ≤ (∑ j ∈ t, (((k + 1).choose j : ℝ) * iteratedDeriv (k + 1 - j) Real.sin θ) ^ 2)
          * ∑ j ∈ t, (x j) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq t _ x
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ∑ j ∈ t, (x j) ^ 2 :=
        mul_le_mul_of_nonneg_right hsum_sq hX
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * (((k : ℝ) + 2) * ∑ j ∈ t, (x j) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ j ∈ t, (x j) ^ 2 = (∑ j ∈ t, (x j) ^ 2) * 1 := by ring
          _ ≤ (∑ j ∈ t, (x j) ^ 2) * ((k : ℝ) + 2) := mul_le_mul_of_nonneg_left hk2 hX
          _ = ((k : ℝ) + 2) * ∑ j ∈ t, (x j) ^ 2 := by ring
    _ = ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * ∑ j ∈ t, (x j) ^ 2 := by ring

end Work.FTS.EllipticEst.remov.Baux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.absIntegrableOfSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- On a finite-measure set, `L²` integrability implies `L¹` integrability: here we use the
elementary pointwise bound `|g| ≤ (g² + 1)/2` (the AM–GM inequality), so that `|g|` is
dominated by the integrable function `(g² + 1)/2`.  The two measures involved,
`volume.restrict (Ioo 0 (π/2))` and `volume.restrict Iθ = volume.restrict (Icc 0 (π/2))`,
differ only by the null set `{0, π/2}`. -/
theorem absIntegrableOfSq {g : ℝ → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (h : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |g θ|) (Set.Ioo 0 (Real.pi / 2)) := by
  -- `Ioo 0 (π/2)` and `Iθ = Icc 0 (π/2)` differ by a null set, so they carry the same
  -- restricted Lebesgue measure.
  have hrestrict : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hsq : MeasureTheory.Integrable (fun θ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    rw [hrestrict]
    exact h
  -- The constant `1` is integrable on a set of finite measure.
  have h1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    have hne : (MeasureTheory.volume (Set.Ioo 0 (Real.pi / 2)) : ENNReal) ≠ ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    exact MeasureTheory.integrableOn_const hne
  have hbound : MeasureTheory.Integrable (fun θ => (1 / 2 : ℝ) * ((g θ) ^ 2 + 1))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hsq.add h1).const_mul (1 / 2)
  refine MeasureTheory.Integrable.mono' hbound (by simpa using hgm.norm) ?_
  filter_upwards with θ
  have hnorm : ‖|g θ|‖ = |g θ| := by simp
  rw [hnorm]
  nlinarith [sq_nonneg (|g θ| - 1), sq_abs (g θ)]

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.ftcBoundOfIntegrableDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open MeasureTheory Set
open scoped Real


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.integral_invSinSqCosCu_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open MeasureTheory


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.coerc.not_integrableOn_of_le_div_sub_pow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.coerc

open MeasureTheory

/-- If `f` dominates `θ ↦ c / (b - θ)^k` on `(b - ε, b)` with `c > 0`, `ε > 0` and `k ≥ 2`,
then `f` is not integrable on `(b - ε, b)`: the singularity at the right endpoint is too strong.

The interval is reflected onto `(0, ε)` by the measure preserving map `y ↦ b - y`, which turns
the lower bound into `c / z^k ≤ f (b - z)` on `(0, ε)`; there the power `c / z^k` is already
non-integrable (`AxisIntegral.not_integrableOn_const_div_pow`), and domination transfers
non-integrability to `f`. -/
theorem not_integrableOn_of_le_div_sub_pow {f : ℝ → ℝ} {c b ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    {k : ℕ} (hk : 2 ≤ k) (h : ∀ θ ∈ Set.Ioo (b - ε) b, c / (b - θ) ^ k ≤ f θ) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioo (b - ε) b) := by
  intro hf
  -- the reflection `y ↦ b - y` is measure preserving and a measurable embedding
  have hmp : MeasurePreserving (fun y : ℝ => b - y) volume volume := by
    simpa using (Measure.measurePreserving_sub_left (volume : Measure ℝ) b)
  have hemb : MeasurableEmbedding (fun y : ℝ => b - y) :=
    (Homeomorph.subLeft b).measurableEmbedding
  -- it maps `(b - ε, b)` back to `(0, ε)`
  have hpre : (fun y : ℝ => b - y) ⁻¹' (Set.Ioo (b - ε) b) = Set.Ioo 0 ε := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]
  -- transport integrability of `f` to the reflected function on `(0, ε)`
  have hf' : MeasureTheory.IntegrableOn (fun y : ℝ => f (b - y)) (Set.Ioo 0 ε) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hemb).mpr hf
  -- the reflected lower bound makes `z ↦ c / z ^ k` integrable on `(0, ε)`
  have hg : MeasureTheory.IntegrableOn (fun z : ℝ => c / z ^ k) (Set.Ioo 0 ε) := by
    refine hf'.mono' ?_ ?_
    · exact (measurable_const.div (measurable_id.pow_const k)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hzpos : 0 < z := hz.1
      have hle : c / z ^ k ≤ f (b - z) := by
        have h1 : c / (b - (b - z)) ^ k ≤ f (b - z) :=
          h (b - z) (by simp only [Set.mem_Ioo]; constructor <;> linarith [hz.1, hz.2])
        have h2 : b - (b - z) = z := by ring
        rwa [h2] at h1
      have hpos : 0 < c / z ^ k := div_pos hc (pow_pos hzpos k)
      rw [Real.norm_of_nonneg hpos.le]
      exact hle
  exact Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_const_div_pow hc hε hk hg

end Work.FTS.EllipticEst.remov.coerc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.coerc.weak_poincare_second =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Interval

namespace Work.FTS.EllipticEst.remov.coerc

/-! ## Cauchy–Schwarz for interval integrals -/

lemma sq_intervalIntegral_le {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume p q)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume p q) :
    (∫ t in p..q, f t) ^ 2 ≤ (q - p) * (∫ t in p..q, (f t) ^ 2) := by
  have hm : Integrable f (volume.restrict (Set.Ioc p q)) := hf.1
  have hm2 : Integrable (fun t => (f t) ^ 2) (volume.restrict (Set.Ioc p q)) := hf2.1
  have hmem : MemLp f 2 (volume.restrict (Set.Ioc p q)) :=
    (memLp_two_iff_integrable_sq hm.1).2 hm2
  have hm1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc p q)) :=
    (intervalIntegrable_const (μ := volume) (a := p) (b := q) (c := (1 : ℝ))).1
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc p q)) :=
    (memLp_two_iff_integrable_sq
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.Ioc p q)))).2 (by simpa only [one_pow] using hm1)
  have hcs := Work.Spaces.cs_integral hmem hmem1
  have hfun : (fun x : ℝ => f x * 1) = f := by
    funext x
    rw [mul_one]
  have h1 : (∫ x in Set.Ioc p q, f x * 1) = ∫ x in p..q, f x := by
    rw [hfun]
    exact (intervalIntegral.integral_of_le hpq).symm
  have h2 : (∫ x in Set.Ioc p q, f x ^ 2) = ∫ x in p..q, (f x) ^ 2 :=
    (intervalIntegral.integral_of_le hpq).symm
  have h3 : (∫ x in Set.Ioc p q, (1 : ℝ) ^ 2) = q - p := by
    rw [show (fun x : ℝ => (1 : ℝ) ^ 2) = (fun _ => (1 : ℝ)) by funext x; norm_num]
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc_of_le hpq]
  rw [h1, h2, h3] at hcs
  exact hcs.trans (le_of_eq (mul_comm (∫ x in p..q, (f x) ^ 2) (q - p)))

/-! ## Integrability of a function with integrable square -/

lemma integrableOn_of_integrableOn_sq {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 L))
    (hg2 : MeasureTheory.IntegrableOn (fun x => (g x) ^ 2) (Set.Icc 0 L)) :
    MeasureTheory.IntegrableOn g (Set.Icc 0 L) := by
  have hAESM : AEStronglyMeasurable g (volume.restrict (Set.Icc 0 L)) := by
    rw [← Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := L) (μ := volume))]
    exact hg.aestronglyMeasurable measurableSet_Ioo
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Icc 0 L)) :=
    MeasureTheory.integrableOn_const
      (s := Set.Icc (0 : ℝ) L) (μ := volume) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have h2 : Integrable (fun x => 1 + (g x) ^ 2) (volume.restrict (Set.Icc 0 L)) :=
    hconst.add hg2
  refine Integrable.mono' h2 hAESM ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|g x| - 1), sq_abs (g x), abs_nonneg (g x)]

/-! ## The fundamental theorem of calculus up to the singular endpoint `0` -/




/-! ## FTC between two interior points -/


/-! ## Mean-zero Poincaré bound (sup form) -/


/-! ## The Poincaré inequality -/


end Work.FTS.EllipticEst.remov.coerc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.invCos_jets_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- **Jets of `u / cos` on a compact subinterval of `(0, π/2)`.**

For every `N` there is a positive constant `A` (depending only on `N`) such that, for every
`u : ℝ → ℝ` of class `C^N` on `(0, π/2)`, every `θ ∈ (0, 3π/8)` and every `m ≤ N`, the square of
the `m`-th derivative of `θ ↦ u θ / cos θ` at `θ` is bounded by `A` times the sum of the squares
of the derivatives of `u` up to order `m` at `θ`.

The proof is Leibniz' formula for the `m`-th derivative of a product, combined with
Cauchy–Schwarz and the fact that on `(0, 3π/8)` (whose closure is a compact subset of
`(-π/2, π/2)`) every jet of `1 / cos` is bounded. -/
theorem invCos_jets_le (N : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ N u (Set.Ioo 0 (Real.pi / 2)) →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8), ∀ m : ℕ, m ≤ N →
        (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          ≤ A * ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2 := by
  classical
  -- a bound for every jet of `1 / cos` on `(0, 3π/8)`
  obtain ⟨B, hB⟩ := invCos_jet_bound
  -- the constant `A = 1 + ∑_{m ≤ N} ∑_{j ≤ m} (C(m,j) B (m-j))²`
  set T : ℝ := ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (n + 1),
      (n.choose j * B (n - j)) ^ 2 with hT
  have hTnn : 0 ≤ T := by
    simp only [hT]
    exact Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  refine ⟨1 + T, by linarith, ?_⟩
  intro u hu θ hθ m hm
  -- `θ ∈ (0, π/2)`, so `cos θ > 0`
  have hθlt : θ < Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθlt⟩
  -- differentiability of the two factors at `θ`
  have hu_at : ContDiffAt ℝ m u θ :=
    (hu.contDiffAt (isOpen_Ioo.mem_nhds ⟨hθ.1, hθlt⟩)).of_le (by exact_mod_cast hm)
  have hsec_at : ContDiffAt ℝ m (fun t : ℝ => (Real.cos t)⁻¹) θ :=
    (Real.contDiff_cos.contDiffAt).inv (ne_of_gt hcos_pos)
  have hfun : (fun t : ℝ => u t / Real.cos t) = u * (fun t : ℝ => (Real.cos t)⁻¹) := by
    funext t; simp [div_eq_mul_inv]
  -- Leibniz + Cauchy–Schwarz
  have hcs := iteratedDeriv_mul_sq_le m u (fun t : ℝ => (Real.cos t)⁻¹) θ B hu_at hsec_at
      (fun k _ => hB k θ hθ)
  -- the coefficient sum is bounded by the constant
  have hcoef : (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) ≤ 1 + T := by
    have hstep : (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) ≤ T := by
      simp only [hT]
      exact Finset.single_le_sum
        (f := fun n => ∑ j ∈ Finset.range (n + 1), (n.choose j * B (n - j)) ^ 2)
        (fun n _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    linarith
  calc (iteratedDeriv m (fun t : ℝ => u t / Real.cos t) θ) ^ 2
      = (iteratedDeriv m (u * (fun t : ℝ => (Real.cos t)⁻¹)) θ) ^ 2 := by rw [hfun]
    _ ≤ (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) *
          ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2 := hcs
    _ ≤ (1 + T) * ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j u θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun j _ => sq_nonneg _))

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.sin_weight_compare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_bd_tail_gprime =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real

set_option maxHeartbeats 1000000

/-- `cos⁶ t ≤ sin(2t)^{2-γ}` on the open right quarter of the slice, for `1 ≤ γ ≤ 3/2`.

`sin(2t) = 2 sin t cos t ≥ cos t` because `sin t ≥ sin (π/4) ≥ 1/2`, and for
`0 < cos t ≤ 1` and `2-γ ≤ 6` the `rpow` is monotone decreasing in the exponent. -/
private lemma sbg_cos_six_le_sigma (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {t : ℝ}
    (ht : t ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.cos t) ^ 6 ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) := by
  have ht1 : Real.pi / 4 < t := ht.1
  have ht2 : t < Real.pi / 2 := ht.2
  have hcpos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht2⟩
  have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have hsint : (1 : ℝ) / 2 ≤ Real.sin t := by
    have h1 : Real.sin (Real.pi / 6) ≤ Real.sin t :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [ht2]) (by linarith [ht1, Real.pi_pos])
    rw [Real.sin_pi_div_six] at h1
    linarith
  have hsin2 : Real.cos t ≤ Real.sin (2 * t) := by
    rw [Real.sin_two_mul]
    nlinarith [hcpos, hsint]
  calc (Real.cos t) ^ 6 = Real.rpow (Real.cos t) (6 : ℝ) :=
        (Real.rpow_natCast (Real.cos t) 6).symm
    _ ≤ Real.rpow (Real.cos t) (2 - γ) :=
        Real.rpow_le_rpow_of_exponent_ge hcpos hc1 (by linarith)
    _ ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) :=
        Real.rpow_le_rpow hcpos.le hsin2 (by linarith)

/-- The pointwise AM–GM (Young) inequality behind the integrability of `cos³·|g'|`:
`cos³t·|g' t| ≤ ½ (g' t)²σ + ½ cos⁶t/σ` whenever `σ = sin(2t)^{2-γ} > 0`.

Put `a = √σ·|g' t|` and `b = cos³t/√σ`; then `a·b = cos³t·|g' t|` (commutativity of `ℝ`
handles `cos t < 0`), `a² = (g' t)²σ`, `b² = cos⁶t/σ`, and `2ab ≤ a²+b²`. -/
private lemma sbg_amgm (γ : ℝ) {g : ℝ → ℝ} {t : ℝ}
    (hσ : 0 < Real.rpow (Real.sin (2 * t)) (2 - γ)) :
    (Real.cos t) ^ 3 * |deriv g t|
      ≤ (1 / 2) * ((deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
        + (1 / 2) * ((Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)) := by
  set a : ℝ := Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |deriv g t| with ha
  set b : ℝ := (Real.cos t) ^ 3 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) with hb
  have hs : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hσ)
  have hsq : (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2
      = Real.rpow (Real.sin (2 * t)) (2 - γ) := Real.sq_sqrt hσ.le
  have hab : a * b = (Real.cos t) ^ 3 * |deriv g t| := by
    rw [ha, hb]; field_simp
  have ha2 : a ^ 2 = (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [ha, mul_pow, hsq, sq_abs]; ring
  have hb2 : b ^ 2 = (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    rw [hb, div_pow, hsq]; ring
  have h2ab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  rw [hab, ha2, hb2] at h2ab
  linarith

/-- Weighted Cauchy–Schwarz on the right half of the slice: the `g'`-part of the tail.

For `ν ∈ [π/4, π/2)`, `deriv g` a.e.-strongly-measurable and `(g')²σ` integrable on `(ν, π/2)`
(`σ = sin(2t)^{2-γ}`, `1 ≤ γ ≤ 3/2`), the function `cos³|g'|` is integrable there and

  `∫_{Ioo ν (π/2)} cos³t · |g' t| ≤ √(Cw · ∫_{Ioo ν (π/2)} (g')²σ) · (π/2-ν)^{(5+γ)/2}`

whenever `∫_{Ioo ν (π/2)} cos⁶/σ ≤ Cw (π/2-ν)^{5+γ}`.

Proof: write `cos³|g'| = (√σ·|g'|)·(cos³/√σ)` (σ > 0 on the open interval) and apply
Cauchy–Schwarz; `∫(√σ g')² = ∫σ(g')²` and `∫(cos³/√σ)² = ∫cos⁶/σ`.  Integrability of
`cos³|g'|` follows from the pointwise AM–GM bound `cos³|g'| ≤ (g')²σ/2 + (cos⁶/σ)/2` together
with the boundedness of `cos⁶/σ` on `[ν, π/2]`.  NOTE: `cos⁶/σ` is *unconditionally* integrable
on `(ν, π/2)` for `ν > 0` — do not try to extract its `MemLp` from `hI6` (a non-integrable
nonneg function has Bochner integral `0` in Mathlib). -/
theorem slice_bd_tail_gprime (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {g : ℝ → ℝ} {Cw ν : ℝ}
    (hCw : 0 ≤ Cw) (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2))
    (hGm : MeasureTheory.AEStronglyMeasurable (deriv g)
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))))
    (hG : MeasureTheory.IntegrableOn
      (fun t => (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo ν (Real.pi / 2)))
    (hI6 : (∫ t in ν..(Real.pi / 2),
        (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        ≤ Cw * (Real.pi / 2 - ν) ^ (5 + γ)) :
    (MeasureTheory.IntegrableOn (fun t => (Real.cos t) ^ 3 * |deriv g t|)
        (Set.Ioo ν (Real.pi / 2)))
      ∧ (∫ t in Set.Ioo ν (Real.pi / 2), (Real.cos t) ^ 3 * |deriv g t|
          ≤ Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
                (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((5 + γ) / 2)) := by
  set I : Set ℝ := Set.Ioo ν (Real.pi / 2) with hIdef
  have hne : ν < Real.pi / 2 := hν.2
  have hν4 : Real.pi / 4 ≤ ν := hν.1
  have hdpos : 0 < Real.pi / 2 - ν := by linarith
  have hmeasI : MeasurableSet I := by rw [hIdef]; exact measurableSet_Ioo
  have hvol : volume I ≠ ⊤ := by
    rw [hIdef, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  -- hypothesis transport to the abbreviated set `I`
  have hGmI : AEStronglyMeasurable (deriv g) (volume.restrict I) := by
    simpa only [hIdef] using hGm
  have hGI : IntegrableOn
      (fun t => (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) I := by
    simpa only [hIdef] using hG
  have hGm_abs : AEStronglyMeasurable (fun t => |deriv g t|) (volume.restrict I) := by
    simpa only [Real.norm_eq_abs] using hGmI.norm
  -- elementary weight facts on `I`
  have hσpos : ∀ t ∈ I, 0 < Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    rw [hIdef] at ht
    have hsin : 0 < Real.sin (2 * t) := by
      apply Real.sin_pos_of_mem_Ioo
      exact ⟨by linarith [hν4, ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
    exact Real.rpow_pos_of_pos hsin _
  have hσnn : ∀ t ∈ I, 0 ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) :=
    fun t ht => (hσpos t ht).le
  have hcos_pos : ∀ t ∈ I, 0 < Real.cos t := by
    intro t ht
    rw [hIdef] at ht
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hν4, ht.1, Real.pi_pos], ht.2⟩
  have hI_sub : ∀ t ∈ I, t ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    rw [hIdef] at ht
    exact ⟨lt_of_le_of_lt hν4 ht.1, ht.2⟩
  have hdiv_le_one : ∀ t ∈ I,
      (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) ≤ 1 := by
    intro t ht
    have hpos := hσpos t ht
    have h6 := sbg_cos_six_le_sigma γ hγ1 hγ2 (hI_sub t ht)
    calc (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)
        ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) / Real.rpow (Real.sin (2 * t)) (2 - γ) :=
          div_le_div_of_nonneg_right h6 hpos.le
      _ = 1 := div_self hpos.ne'
  -- the Cauchy–Schwarz pair
  have hσcont : Continuous (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  set F : ℝ → ℝ :=
    fun t => Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |deriv g t| with hFdef
  set Hc : ℝ → ℝ :=
    fun t => (Real.cos t) ^ 3 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) with hHdef
  have hF_aesm : AEStronglyMeasurable F (volume.restrict I) := by
    rw [hFdef]
    exact ((Real.continuous_sqrt.comp hσcont).aestronglyMeasurable).mul hGm_abs
  have hHc_aesm : AEStronglyMeasurable Hc (volume.restrict I) := by
    rw [hHdef]
    simp only [div_eq_mul_inv]
    exact (((Real.continuous_cos.pow 3).measurable).mul
      (((Real.continuous_sqrt.comp hσcont).measurable).inv)).aestronglyMeasurable
  -- pointwise identities on `I`
  have hF2 : ∀ t ∈ I, F t ^ 2
      = (deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    have h := hσnn t ht
    simp only [hFdef]
    rw [mul_pow, Real.sq_sqrt h, sq_abs]
    ring
  have hH2 : ∀ t ∈ I, Hc t ^ 2
      = (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    have h := hσnn t ht
    simp only [hHdef]
    rw [div_pow, Real.sq_sqrt h]
    ring
  have hFH : ∀ t ∈ I, F t * Hc t = (Real.cos t) ^ 3 * |deriv g t| := by
    intro t ht
    have hs : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hσpos t ht))
    simp only [hFdef, hHdef]
    field_simp
  -- integrability of the two Cauchy–Schwarz factors
  have hH2i : Integrable
      (fun t => (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      (volume.restrict I) := by
    have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict I) :=
      integrableOn_const (s := I) (μ := volume) hvol
    refine Integrable.mono' hconst ?_ ?_
    · simp only [div_eq_mul_inv]
      exact (((Real.continuous_cos.pow 6).measurable).mul
        (hσcont.measurable.inv)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      have hnn : 0 ≤ (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) :=
        div_nonneg (pow_nonneg (hcos_pos t ht).le 6) (hσnn t ht)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hdiv_le_one t ht
  have hF2i : Integrable (fun t => F t ^ 2) (volume.restrict I) :=
    hGI.congr (by
      filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      exact (hF2 t ht).symm)
  have hH2i' : Integrable (fun t => Hc t ^ 2) (volume.restrict I) :=
    hH2i.congr (by
      filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      exact (hH2 t ht).symm)
  -- Cauchy–Schwarz
  have hFmem : MemLp F 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hF_aesm).mpr hF2i
  have hHmem : MemLp Hc 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hHc_aesm).mpr hH2i'
  have hcs := Work.Spaces.cs_integral (s := I) hFmem hHmem
  have hW : (∫ x in I, F x * Hc x) = ∫ x in I, (Real.cos x) ^ 3 * |deriv g x| :=
    setIntegral_congr_fun hmeasI (fun t ht => hFH t ht)
  have hX : (∫ x in I, F x ^ 2)
      = ∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ) :=
    setIntegral_congr_fun hmeasI (fun t ht => hF2 t ht)
  have hY : (∫ x in I, Hc x ^ 2)
      = ∫ x in I, (Real.cos x) ^ 6 / Real.rpow (Real.sin (2 * x)) (2 - γ) :=
    setIntegral_congr_fun hmeasI (fun t ht => hH2 t ht)
  -- the bound on the second factor coming from `hI6`
  have hI6I : (∫ t in I, (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      ≤ Cw * (Real.pi / 2 - ν) ^ (5 + γ) := by
    have h1 : (∫ t in ν..(Real.pi / 2),
          (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        = ∫ t in I, (Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ) := by
      rw [intervalIntegral.integral_of_le hne.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← hIdef]
    rw [h1] at hI6
    exact hI6
  have hX0 : 0 ≤ ∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ) :=
    setIntegral_nonneg hmeasI (fun t ht => mul_nonneg (sq_nonneg _) (hσnn t ht))
  have hW0 : 0 ≤ ∫ x in I, (Real.cos x) ^ 3 * |deriv g x| :=
    setIntegral_nonneg hmeasI
      (fun t ht => mul_nonneg (pow_nonneg (hcos_pos t ht).le 3) (abs_nonneg _))
  -- the squared Cauchy–Schwarz bound
  have hstep : (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|) ^ 2
      ≤ (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
        * (Cw * (Real.pi / 2 - ν) ^ (5 + γ)) := by
    calc (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|) ^ 2
        = (∫ x in I, F x * Hc x) ^ 2 := by rw [hW]
      _ ≤ (∫ x in I, F x ^ 2) * (∫ x in I, Hc x ^ 2) := hcs
      _ = (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
            * (∫ x in I, (Real.cos x) ^ 6 / Real.rpow (Real.sin (2 * x)) (2 - γ)) := by
          rw [hX, hY]
      _ ≤ (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
            * (Cw * (Real.pi / 2 - ν) ^ (5 + γ)) :=
          mul_le_mul_of_nonneg_left hI6I hX0
  -- the two conclusions
  have hsqrt_rpow : Real.sqrt ((Real.pi / 2 - ν) ^ (5 + γ))
      = (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (hx := hdpos.le) (y := 5 + γ) (z := 1 / 2)]
    congr 1
    ring
  have hmain : (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|)
      ≤ Real.sqrt (Cw * (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
        * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
    calc (∫ x in I, (Real.cos x) ^ 3 * |deriv g x|)
        = Real.sqrt ((∫ x in I, (Real.cos x) ^ 3 * |deriv g x|) ^ 2) :=
          (Real.sqrt_sq hW0).symm
      _ ≤ Real.sqrt ((∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
            * (Cw * (Real.pi / 2 - ν) ^ (5 + γ))) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt (Cw * (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((5 + γ) / 2) := by
          have e1 : Real.sqrt ((∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
                * (Cw * (Real.pi / 2 - ν) ^ (5 + γ)))
              = Real.sqrt (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ))
                * Real.sqrt (Cw * (Real.pi / 2 - ν) ^ (5 + γ)) :=
            Real.sqrt_mul hX0 _
          have e2 : Real.sqrt (Cw * (Real.pi / 2 - ν) ^ (5 + γ))
              = Real.sqrt Cw * Real.sqrt ((Real.pi / 2 - ν) ^ (5 + γ)) :=
            Real.sqrt_mul hCw _
          have e3 : Real.sqrt (Cw * (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)))
              = Real.sqrt Cw * Real.sqrt (∫ x in I, (deriv g x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 - γ)) :=
            Real.sqrt_mul hCw _
          rw [e1, e2, e3, hsqrt_rpow]
          ring
  have hint : IntegrableOn (fun t => (Real.cos t) ^ 3 * |deriv g t|) I := by
    have hdom : Integrable
        (fun t => (1 / 2) * ((deriv g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
          + (1 / 2) * ((Real.cos t) ^ 6 / Real.rpow (Real.sin (2 * t)) (2 - γ)))
        (volume.restrict I) :=
      (hGI.const_mul (1 / 2)).add (hH2i.const_mul (1 / 2))
    refine Integrable.mono' hdom ?_ ?_
    · exact ((Real.continuous_cos.pow 3).aestronglyMeasurable).mul hGm_abs
    · filter_upwards [self_mem_ae_restrict hmeasI] with t ht
      have hnn : 0 ≤ (Real.cos t) ^ 3 * |deriv g t| :=
        mul_nonneg (pow_nonneg (hcos_pos t ht).le 3) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact sbg_amgm γ (hσpos t ht)
  refine ⟨?_, ?_⟩
  · simpa only [hIdef] using hint
  · simpa only [hIdef] using hmain

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_not_integrable_of_lower_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov




end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_u_div_cos_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

/-- `Real.rpow` and the `^` notation for real exponents are the same operation. -/
private lemma rpow_eq_hpow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-- Cauchy–Schwarz for the set integral over a closed interval:
`(∫_{[a,b]} f)² ≤ (b-a) ∫_{[a,b]} f²` for `f` square integrable and a.e. strongly measurable. -/
private lemma sq_setIntegral_Icc_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntegrableOn (fun x => f x ^ 2) (Set.Icc a b))
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) :
    (∫ x in Set.Icc a b, f x) ^ 2 ≤ (b - a) * (∫ x in Set.Icc a b, f x ^ 2) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hm1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Icc a b)) := memLp_const 1
  have hmf : MemLp f 2 (volume.restrict (Set.Icc a b)) :=
    (memLp_two_iff_integrable_sq hmeas).mpr hint
  have h := Work.Spaces.cs_integral hm1 hmf
  have h1 : (∫ x in Set.Icc a b, (1 : ℝ) * f x) = ∫ x in Set.Icc a b, f x := by simp
  have h2 : (∫ x in Set.Icc a b, (1 : ℝ) ^ 2) = b - a := by
    rw [one_pow, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul,
      mul_one]
  rw [h1, h2] at h
  exact h

/-- The angular weight bound: for `1 ≤ γ ≤ 3/2` and `θ ∈ (0, π/2)`,
`sin(2θ)^{2-γ}/cos²θ ≤ 2^{2-γ} (π/2)^γ (π/2 - θ)^{-γ}`. -/
private lemma sin2_div_cos_sq_le_aux (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 2
        ≤ (2 ^ (2 - γ) * (Real.pi / 2) ^ γ) * (Real.pi / 2 - θ) ^ (-γ) := by
  intro θ hθ
  have hpi2 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
  have hbase : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have h2γ : (0 : ℝ) ≤ 2 - γ := by linarith
  -- `sin θ ^ (2-γ) ≤ 1`
  have hsin1 : (Real.sin θ) ^ (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsin.le (Real.sin_le_one θ) h2γ
  -- `cos θ ^ (2-γ) = cos²θ * cos θ ^ (-γ)`
  have hsplit : (Real.cos θ) ^ (2 - γ) = (Real.cos θ) ^ 2 * (Real.cos θ) ^ (-γ) := by
    have h : (Real.cos θ) ^ (2 + (-γ)) = (Real.cos θ) ^ (2 : ℝ) * (Real.cos θ) ^ (-γ) :=
      Real.rpow_add hcos 2 (-γ)
    have h' : (2 : ℝ) + (-γ) = 2 - γ := by ring
    have h2 : (Real.cos θ) ^ (2 : ℝ) = (Real.cos θ) ^ 2 := Real.rpow_two _
    rw [h', h2] at h
    exact h
  -- Jordan's inequality: `π/2 - θ ≤ (π/2) cos θ`
  have hjordan : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have h := Real.mul_le_sin hbase.le (by linarith [hθ.1])
    rw [Real.sin_pi_div_two_sub] at h
    have h2 := mul_le_mul_of_nonneg_left h hpi2.le
    have h3 : Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by
      field_simp
    linarith [h2, h3]
  -- `cos θ ^ (-γ) ≤ (π/2)^γ (π/2-θ)^(-γ)`
  have hcos_bound : (Real.cos θ) ^ (-γ)
      ≤ (Real.pi / 2) ^ γ * (Real.pi / 2 - θ) ^ (-γ) := by
    have h1 : (Real.pi / 2) ^ (-γ) * (Real.cos θ) ^ (-γ) ≤ (Real.pi / 2 - θ) ^ (-γ) := by
      have h2 : (Real.pi / 2 * Real.cos θ) ^ (-γ)
          = (Real.pi / 2) ^ (-γ) * (Real.cos θ) ^ (-γ) := Real.mul_rpow hpi2.le hcos.le
      rw [← h2]
      exact Real.rpow_le_rpow_of_nonpos hbase hjordan (by linarith : -γ ≤ (0 : ℝ))
    have h4 : 0 < (Real.pi / 2) ^ γ := Real.rpow_pos_of_pos hpi2 γ
    have h5 : (Real.pi / 2) ^ γ * (Real.pi / 2) ^ (-γ) = 1 := by
      have h6 : (Real.pi / 2) ^ (γ + (-γ)) = (Real.pi / 2) ^ γ * (Real.pi / 2) ^ (-γ) :=
        Real.rpow_add hpi2 γ (-γ)
      have hz : (Real.pi / 2) ^ (0 : ℝ) = 1 := Real.rpow_zero _
      rw [show γ + (-γ) = (0 : ℝ) by ring, hz] at h6
      exact h6.symm
    calc (Real.cos θ) ^ (-γ)
        = ((Real.pi / 2) ^ γ * (Real.pi / 2) ^ (-γ)) * (Real.cos θ) ^ (-γ) := by
            rw [h5, one_mul]
      _ = (Real.pi / 2) ^ γ * ((Real.pi / 2) ^ (-γ) * (Real.cos θ) ^ (-γ)) := by ring
      _ ≤ (Real.pi / 2) ^ γ * (Real.pi / 2 - θ) ^ (-γ) := mul_le_mul_of_nonneg_left h1 h4.le
  rw [div_le_iff₀ (pow_pos hcos 2)]
  calc (Real.sin (2 * θ)) ^ (2 - γ)
      = (2 * Real.sin θ * Real.cos θ) ^ (2 - γ) := by rw [Real.sin_two_mul]
    _ = (2 * Real.sin θ) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ) :=
          Real.mul_rpow (by positivity) hcos.le
    _ = (2 ^ (2 - γ) * (Real.sin θ) ^ (2 - γ)) * (Real.cos θ) ^ (2 - γ) := by
          rw [show (2 * Real.sin θ) ^ (2 - γ)
              = 2 ^ (2 - γ) * (Real.sin θ) ^ (2 - γ) from
            Real.mul_rpow (by norm_num) hsin.le]
    _ ≤ (2 ^ (2 - γ) * 1) * (Real.cos θ) ^ (2 - γ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsin1 (Real.rpow_nonneg (by norm_num) _))
            (Real.rpow_nonneg hcos.le _)
    _ = (2 ^ (2 - γ) * 1) * ((Real.cos θ) ^ 2 * (Real.cos θ) ^ (-γ)) := by rw [hsplit]
    _ ≤ (2 ^ (2 - γ) * 1) * ((Real.cos θ) ^ 2 *
          ((Real.pi / 2) ^ γ * (Real.pi / 2 - θ) ^ (-γ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos_bound ?_)
            (le_of_lt (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) one_pos))
          positivity
    _ = (2 ^ (2 - γ) * (Real.pi / 2) ^ γ) * (Real.pi / 2 - θ) ^ (-γ) * (Real.cos θ) ^ 2 := by
          ring

/-- Integrability of `θ ↦ (π/2 - θ)^{1-γ}` on `Iθ = [0, π/2]` for `γ < 2`. -/
private lemma integrableOn_pi_sub_rpow_aux {γ : ℝ} (hγ : γ < 2) :
    IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (1 - γ)) Work.Spaces.Iθ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ, ← intervalIntegrable_iff_integrableOn_Icc_of_le hle]
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume (Real.pi / 2) 0 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 1 - γ)
  have h := (IntervalIntegrable.comp_sub_left_iff (f := fun x : ℝ => x ^ (1 - γ))
    (a := Real.pi / 2) (b := 0) (Real.pi / 2)).mpr hbase
  simpa using h

/-- The value of `∫_{Iθ} (π/2 - θ)^{1-γ}` for `γ < 2`. -/
private lemma integral_pi_sub_rpow_aux {γ : ℝ} (hγ : γ < 2) :
    (∫ θ in Work.Spaces.Iθ, (Real.pi / 2 - θ) ^ (1 - γ))
      = (Real.pi / 2) ^ (2 - γ) / (2 - γ) := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (1 - γ)) (Real.pi / 2)]
  rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring,
    show Real.pi / 2 - 0 = Real.pi / 2 by ring]
  have h := integral_rpow (a := (0 : ℝ)) (b := Real.pi / 2) (r := 1 - γ)
    (Or.inl (by linarith : (-1 : ℝ) < 1 - γ))
  have hz : (0 : ℝ) ^ (2 - γ) = 0 := Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
  rw [show (1 : ℝ) - γ + 1 = 2 - γ by ring, hz, sub_zero] at h
  exact h

/-- Fundamental theorem of calculus for a slice with the regularity hypotheses of the main
theorem: `u θ = -∫_θ^{π/2} deriv u` for `θ ∈ Iθ`, and `deriv u` is integrable on `Iθ`. -/
private lemma slice_ftc_aux {u : ℝ → ℝ}
    (hC3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hpi : u (Real.pi / 2) = 0)
    (hint : IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    IntegrableOn (deriv u) Work.Spaces.Iθ ∧
      ∀ θ ∈ Work.Spaces.Iθ, u θ = -∫ s in θ..(Real.pi / 2), deriv u s := by
  have hIθ_ne_top : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const hIθ_ne_top
  have hdom : IntegrableOn (fun θ => (1 : ℝ) + (deriv u θ) ^ 2) Work.Spaces.Iθ := hInt1.add hint
  have hderivInt : IntegrableOn (deriv u) Work.Spaces.Iθ := by
    refine Integrable.mono' hdom (measurable_deriv u).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (deriv u x), sq_abs (deriv u x), sq_nonneg (|deriv u x| - 1 / 2)]
  constructor
  · exact hderivInt
  · intro θ hθ
    have hsub : Set.Icc θ (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
      fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hint' : IntegrableOn (deriv u) (Set.Icc θ (Real.pi / 2)) := hderivInt.mono_set hsub
    have hint'' : IntervalIntegrable (deriv u) volume θ (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hθ.2).mpr hint'
    have hderiv : ∀ x ∈ Set.Ioo θ (Real.pi / 2), HasDerivAt u (deriv u x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨lt_of_le_of_lt hθ.1 hx.1, hx.2⟩
      exact ((hC3.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hcont' : ContinuousOn u (Set.Icc θ (Real.pi / 2)) :=
      hcont.mono fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hftc :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.2 hcont' hderiv hint''
    rw [hpi, zero_sub] at hftc
    rw [hftc]
    ring

theorem slice_u_div_cos_sq_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  simp only [rpow_eq_hpow]
  have hγ2' : γ < 2 := by linarith
  have h2γ : (0 : ℝ) ≤ 2 - γ := by linarith
  set M : ℝ := 2 ^ (2 - γ) * (Real.pi / 2) ^ γ with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hCpos : 0 < 1 + M * Real.pi := by
    have h := mul_pos hMpos Real.pi_pos
    linarith
  refine ⟨1 + M * Real.pi, hCpos, ?_⟩
  intro u hC3 hcont hu0 hpi hIntd hIntu
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg fun θ => sq_nonneg _
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg fun θ => sq_nonneg _
  obtain ⟨hderivInt, hftc⟩ := slice_ftc_aux hC3 hcont hpi hIntd
  -- pointwise bound for `u²`
  have hu_sq : ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * A := by
    intro θ hθ
    have hsub : Set.Icc θ (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
      fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hint' : IntegrableOn (fun x => (deriv u x) ^ 2) (Set.Icc θ (Real.pi / 2)) :=
      hIntd.mono_set hsub
    have hmeas' : AEStronglyMeasurable (deriv u)
        (volume.restrict (Set.Icc θ (Real.pi / 2))) :=
      (measurable_deriv u).aestronglyMeasurable
    have hcs := sq_setIntegral_Icc_le (f := deriv u) (a := θ) (b := Real.pi / 2) hθ.2 hint' hmeas'
    have e1 : (∫ s in θ..(Real.pi / 2), deriv u s) = ∫ s in Set.Icc θ (Real.pi / 2), deriv u s := by
      rw [intervalIntegral.integral_of_le hθ.2, MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hu2 : (u θ) ^ 2 = (∫ s in Set.Icc θ (Real.pi / 2), deriv u s) ^ 2 := by
      rw [hftc θ hθ, e1]
      ring
    rw [hu2]
    refine le_trans hcs (mul_le_mul_of_nonneg_left ?_ (by linarith [hθ.2]))
    exact setIntegral_mono_set hIntd (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall fun x hx => hsub hx)
  -- pointwise bound for the integrand on the interior
  have hweight := sin2_div_cos_sq_le_aux γ hγ1 hγ2
  have key_int : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        ≤ M * A * (Real.pi / 2 - θ) ^ (1 - γ) := by
    intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hbase : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hwb := hweight θ hθ
    have hstep1 : (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        ≤ (u θ) ^ 2 * (M * (Real.pi / 2 - θ) ^ (-γ)) := by
      have hfac : (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
          = (u θ) ^ 2 * ((Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 2) := by
        rw [div_pow]
        ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hwb (sq_nonneg _)
    have hstep2 : (u θ) ^ 2 * (M * (Real.pi / 2 - θ) ^ (-γ))
        ≤ M * ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) := by
      have hw : 0 ≤ (Real.pi / 2 - θ) ^ (-γ) := Real.rpow_nonneg hbase.le _
      have hu := mul_le_mul_of_nonneg_right (hu_sq θ ⟨hθ.1.le, hθ.2.le⟩) hw
      calc (u θ) ^ 2 * (M * (Real.pi / 2 - θ) ^ (-γ))
          = M * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) := by ring
        _ ≤ M * (((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ)) :=
              mul_le_mul_of_nonneg_left hu hMpos.le
        _ = M * ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) := by ring
    have hstep3 : M * ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ)
        = M * A * (Real.pi / 2 - θ) ^ (1 - γ) := by
      have h1 : (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-γ)
          = (Real.pi / 2 - θ) ^ (1 - γ) := by
        have h := Real.rpow_add hbase (1 : ℝ) (-γ)
        have h' : (1 : ℝ) + (-γ) = 1 - γ := by ring
        rw [h', Real.rpow_one] at h
        exact h.symm
      rw [← h1]
      ring
    exact le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))
  -- the pointwise bound on all of `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        ≤ M * A * (Real.pi / 2 - θ) ^ (1 - γ) := by
    intro θ hθ
    have hRHS0 : 0 ≤ M * A * (Real.pi / 2 - θ) ^ (1 - γ) :=
      mul_nonneg (mul_nonneg hMpos.le hA0) (Real.rpow_nonneg (by linarith [hθ.2]) _)
    rcases lt_trichotomy θ 0 with hlt | heq | hgt
    · exact absurd hθ.1 (not_le.mpr hlt)
    · subst heq
      have hs : Real.sin (2 * 0) = 0 := by simp
      have hz : (0 : ℝ) ^ (2 - γ) = 0 := Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
      have hzero : (u 0 / Real.cos 0) ^ 2 * (Real.sin (2 * 0)) ^ (2 - γ) = 0 := by
        rw [hu0, hs, hz]
        simp
      rw [hzero]
      simpa using hRHS0
    · rcases lt_trichotomy θ (Real.pi / 2) with h2 | heq2 | hgt2
      · exact key_int θ ⟨hgt, h2⟩
      · subst heq2
        have hs : Real.sin (2 * (Real.pi / 2)) = 0 := by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have hz : (0 : ℝ) ^ (2 - γ) = 0 := Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
        have hzero : (u (Real.pi / 2) / Real.cos (Real.pi / 2)) ^ 2 *
            (Real.sin (2 * (Real.pi / 2))) ^ (2 - γ) = 0 := by
          rw [hpi, hs, hz]
          simp
        rw [hzero]
        simpa using hRHS0
      · exact absurd hθ.2 (not_le.mpr hgt2)
  -- integrability of the dominating function
  have hIntW : IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (1 - γ)) Work.Spaces.Iθ :=
    integrableOn_pi_sub_rpow_aux hγ2'
  have hdomInt : Integrable (fun θ => M * A * (Real.pi / 2 - θ) ^ (1 - γ))
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.const_mul hIntW (M * A)
  -- integrability of the integrand
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact measurableSet_Icc
  have hGint : Integrable (fun θ => (u θ / Real.cos θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 - γ)) (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.mono' hdomInt ?_ ?_
    · have hu_meas : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) :=
        hcont.aestronglyMeasurable hIθ_meas
      have hcos_meas : AEStronglyMeasurable (fun θ : ℝ => Real.cos θ)
          (volume.restrict Work.Spaces.Iθ) :=
        Real.measurable_cos.aestronglyMeasurable
      have hdiv : AEStronglyMeasurable (fun θ : ℝ => u θ / Real.cos θ)
          (volume.restrict Work.Spaces.Iθ) :=
        (hu_meas.aemeasurable.div hcos_meas.aemeasurable).aestronglyMeasurable
      have hsin_cont : Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - γ)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
          (fun x => Or.inr h2γ)
      exact (hdiv.pow 2).mul hsin_cont.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθmem
      have hg0 : 0 ≤ (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
        refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθmem.1])
          (by linarith [hθmem.2, Real.pi_pos])
      rw [Real.norm_eq_abs, abs_of_nonneg hg0]
      exact hpt θ hθmem
  have hG_le : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      ≤ ∫ θ in Work.Spaces.Iθ, M * A * (Real.pi / 2 - θ) ^ (1 - γ) :=
    integral_mono_ae hGint hdomInt (by
      filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθmem
      exact hpt θ hθmem)
  have hval : (∫ θ in Work.Spaces.Iθ, M * A * (Real.pi / 2 - θ) ^ (1 - γ))
      = M * A * ((Real.pi / 2) ^ (2 - γ) / (2 - γ)) := by
    rw [integral_const_mul, integral_pi_sub_rpow_aux hγ2']
  have hnum : M * A * ((Real.pi / 2) ^ (2 - γ) / (2 - γ)) ≤ M * A * Real.pi := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMpos.le hA0)
    have hP : (Real.pi / 2) ^ (2 - γ) ≤ Real.pi / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := Real.pi / 2) (y := 2 - γ) (z := 1)
        Real.one_le_pi_div_two (by linarith)
      rw [Real.rpow_one] at h
      exact h
    have hden : 0 < 2 - γ := by linarith
    have hinv : (2 - γ)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hden, mul_comm]
      linarith
    calc (Real.pi / 2) ^ (2 - γ) / (2 - γ)
        = (Real.pi / 2) ^ (2 - γ) * (2 - γ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (Real.pi / 2) * 2 := mul_le_mul hP hinv (by positivity) (by positivity)
      _ = Real.pi := by ring
  have hfin : M * A * Real.pi ≤ (1 + M * Real.pi) * (A + B) := by
    have hMpi : 0 < M * Real.pi := mul_pos hMpos Real.pi_pos
    have hc : M * Real.pi ≤ 1 + M * Real.pi := by linarith
    calc M * A * Real.pi = (M * Real.pi) * A := by ring
      _ ≤ (1 + M * Real.pi) * A := mul_le_mul_of_nonneg_right hc hA0
      _ ≤ (1 + M * Real.pi) * (A + B) :=
            mul_le_mul_of_nonneg_left (by linarith [hB0]) (by linarith)
  exact ⟨hGint, le_trans hG_le (le_trans (le_of_eq hval) (le_trans hnum hfin))⟩

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.theta_integral_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

/-- If `0 < s ≤ t ≤ 1` then `t ^ (-e)` is bounded below by `min (s ^ (-e)) 1`,
for every real exponent `e`. -/
theorem rpow_neg_ge_min {t s e : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    min (s ^ (-e)) 1 ≤ t ^ (-e) := by
  rcases le_or_gt 0 e with he | he
  · have ht0 : 0 < t := lt_of_lt_of_le hs hst
    have hte1 : t ^ e ≤ 1 := Real.rpow_le_one (le_of_lt ht0) ht he
    have htpos : 0 < t ^ e := Real.rpow_pos_of_pos ht0 e
    have h1 : (1 : ℝ) ≤ t ^ (-e) := by
      rw [Real.rpow_neg (le_of_lt ht0) e, one_le_inv₀ htpos]
      exact hte1
    exact le_trans (min_le_right _ _) h1
  · have he' : 0 ≤ -e := by linarith
    have h : s ^ (-e) ≤ t ^ (-e) := Real.rpow_le_rpow (le_of_lt hs) hst he'
    exact le_trans (min_le_left _ _) h

theorem theta_integral_lower (g : ℝ → ℝ → ℝ) (e θ₀ : ℝ) (hθ₀ : θ₀ ∈ Work.Spaces.Iθ)
    (hcont : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (0, θ₀)) (hne : g 0 θ₀ ≠ 0)
    (hint : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) Work.Spaces.Iθ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ Set.Ioo 0 ε,
      c ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := by
  -- ## Step 1: the level `c₀ = |g 0 θ₀| / 2` and a box on which `|g| ≥ c₀`.
  set c₀ : ℝ := |g 0 θ₀| / 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    have h : 0 < |g 0 θ₀| := abs_pos.mpr hne
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont c₀ hc₀pos
  have hθ₀Icc : θ₀ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    simpa only [Work.Spaces.Iθ] using hθ₀
  -- ## Step 2: an interior point `θ₁` close to `θ₀`.
  have hcl : θ₀ ∈ closure (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [closure_Ioo (a := (0 : ℝ)) (b := Real.pi / 2) (by linarith [Real.pi_pos])]
    exact hθ₀Icc
  obtain ⟨θ₁, hθ₁Ioo, hθ₁dist₀⟩ := Metric.mem_closure_iff.mp hcl (δ / 4) (by linarith)
  have hθ₁dist : dist θ₁ θ₀ < δ / 4 := by rwa [dist_comm] at hθ₁dist₀
  have hθ₁abs : |θ₁ - θ₀| < δ / 4 := by rwa [Real.dist_eq] at hθ₁dist
  have hθ₁pos : 0 < θ₁ := hθ₁Ioo.1
  have hθ₁lt : θ₁ < Real.pi / 2 := hθ₁Ioo.2
  have hspos : 0 < Real.sin (2 * θ₁) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- ## Step 3: a radius `γ` around `θ₁` on which `sin (2θ) ≥ sin (2θ₁)/2`.
  obtain ⟨γ, hγpos, hγ⟩ := Metric.continuousAt_iff.mp
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt)
    (Real.sin (2 * θ₁) / 2) (by linarith)
  have hγ'' : ∀ x : ℝ, dist x θ₁ < γ →
      dist ((fun σ : ℝ => Real.sin (2 * σ)) x) ((fun σ : ℝ => Real.sin (2 * σ)) θ₁)
        < Real.sin (2 * θ₁) / 2 := fun x hx => hγ (x := x) hx
  have hγ' : ∀ θ : ℝ, dist θ θ₁ < γ → Real.sin (2 * θ₁) / 2 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have h2 : dist (Real.sin (2 * θ)) (Real.sin (2 * θ₁)) < Real.sin (2 * θ₁) / 2 :=
      hγ'' θ hθ
    rw [Real.dist_eq] at h2
    have h3 := (abs_lt.mp h2).1
    linarith
  -- ## Step 4: the sub-interval `K = [θ₁ - rad, θ₁ + rad]`.
  set rad : ℝ := min (δ / 4) (min (γ / 2) (min (θ₁ / 2) ((Real.pi / 2 - θ₁) / 2))) with hrad
  have hradpos : 0 < rad := by
    rw [hrad]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hradδ : rad ≤ δ / 4 := by rw [hrad]; exact min_le_left _ _
  have hradγ : rad ≤ γ / 2 := by
    rw [hrad]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hradθ : rad ≤ θ₁ / 2 := by
    rw [hrad]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hradπ : rad ≤ (Real.pi / 2 - θ₁) / 2 := by
    rw [hrad]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hKsub : Set.Icc (θ₁ - rad) (θ₁ + rad) ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hθ.1, hradθ, hθ₁pos], by linarith [hθ.2, hradπ, hθ₁lt]⟩
  have hKmem : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad), |θ - θ₁| ≤ rad := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hsin_lb : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad),
      Real.sin (2 * θ₁) / 2 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    refine hγ' θ ?_
    rw [Real.dist_eq]
    have h1 : |θ - θ₁| ≤ rad := hKmem θ hθ
    have h2 : rad < γ := by linarith [hradγ, hγpos]
    linarith
  have hsin_gt : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad), 0 < Real.sin (2 * θ) :=
    fun θ hθ => lt_of_lt_of_le (by linarith [hspos]) (hsin_lb θ hθ)
  have hsin_le1 : ∀ θ : ℝ, Real.sin (2 * θ) ≤ 1 := fun θ => Real.sin_le_one (2 * θ)
  -- ## Step 5: `|g| ≥ c₀` on the box `|z| < δ`, `|θ - θ₀| < δ`.
  have hglb : ∀ (z θ : ℝ), |z| < δ → |θ - θ₀| < δ → c₀ ^ 2 ≤ (g z θ) ^ 2 := by
    intro z θ hz hθ
    have hdist : dist ((z, θ) : ℝ × ℝ) (0, θ₀) < δ := by
      have h1 : dist z 0 < δ := by rwa [Real.dist_eq, sub_zero]
      have h2 : dist θ θ₀ < δ := by rwa [Real.dist_eq]
      rw [Prod.dist_eq]
      exact max_lt h1 h2
    have hraw := hδ hdist
    rw [Real.dist_eq] at hraw
    have hlt : |g z θ - g 0 θ₀| < c₀ := hraw
    have htri : |g 0 θ₀| ≤ |g 0 θ₀ - g z θ| + |g z θ| := by
      calc |g 0 θ₀| = |(g 0 θ₀ - g z θ) + g z θ| := by
            rw [show (g 0 θ₀ - g z θ) + g z θ = g 0 θ₀ by ring]
        _ ≤ |g 0 θ₀ - g z θ| + |g z θ| := abs_add_le _ _
    have h2c₀ : |g 0 θ₀| = 2 * c₀ := by rw [hc₀]; ring
    have habs : |g 0 θ₀ - g z θ| = |g z θ - g 0 θ₀| := abs_sub_comm _ _
    have hlt2 : |g 0 θ₀| < c₀ + |g z θ| := by
      have h' : |g 0 θ₀ - g z θ| + |g z θ| < c₀ + |g z θ| := by
        rw [habs]; linarith
      linarith [htri]
    have hcle : c₀ < |g z θ| := by
      rw [h2c₀] at hlt2
      linarith
    have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ c₀ by linarith) (le_of_lt hcle) 2
    rwa [sq_abs] at hpow
  -- ## Step 6: the pointwise lower bound on `K`.
  set b₀ : ℝ := min ((Real.sin (2 * θ₁) / 2) ^ (-e)) 1 with hb₀
  have hb₀pos : 0 < b₀ := by
    rw [hb₀]
    exact lt_min (Real.rpow_pos_of_pos (show (0 : ℝ) < Real.sin (2 * θ₁) / 2 by linarith) _)
      one_pos
  have hptwise : ∀ (z θ : ℝ), |z| < δ → |θ - θ₀| < δ →
      θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad) →
      c₀ ^ 2 * b₀ ≤ (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := by
    intro z θ hz hθ hθK
    have h1 : c₀ ^ 2 ≤ (g z θ) ^ 2 := hglb z θ hz hθ
    have h2 : b₀ ≤ (Real.sin (2 * θ)) ^ (-e) := by
      rw [hb₀]
      exact rpow_neg_ge_min (s := Real.sin (2 * θ₁) / 2) (t := Real.sin (2 * θ)) (e := e)
        (by linarith) (hsin_lb θ hθK) (hsin_le1 θ)
    exact mul_le_mul h1 h2 (le_of_lt hb₀pos) (le_trans (sq_nonneg _) h1)
  -- ## Step 7: assemble.
  refine ⟨δ / 2, by linarith, c₀ ^ 2 * b₀ * (2 * rad), ?_, ?_⟩
  · exact mul_pos (mul_pos (pow_pos hc₀pos 2) hb₀pos) (by linarith)
  · intro z hz
    have hz0 : 0 < z := hz.1
    have hzabs : |z| < δ := by
      rw [abs_of_pos hz0]
      linarith [hz.2]
    have hIntθ : MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) Work.Spaces.Iθ := hint z hz0
    have hIntK : MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e))
        (Set.Icc (θ₁ - rad) (θ₁ + rad)) := hIntθ.mono_set hKsub
    have hθδ : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad), |θ - θ₀| < δ := by
      intro θ hθK
      have h1 : |θ - θ₁| ≤ rad := hKmem θ hθK
      have h3 : |θ - θ₀| ≤ |θ - θ₁| + |θ₁ - θ₀| := by
        have h4 := abs_add_le (θ - θ₁) (θ₁ - θ₀)
        rwa [show (θ - θ₁) + (θ₁ - θ₀) = θ - θ₀ by ring] at h4
      linarith [h3, h1, hθ₁abs, hradδ, hδpos]
    have hstep1 : ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad), (c₀ ^ 2 * b₀)
        ≤ ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad),
            (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) :=
      MeasureTheory.setIntegral_mono_of_nonneg
        (fun θ _ => le_of_lt (mul_pos (pow_pos hc₀pos 2) hb₀pos))
        (fun θ hθK => hptwise z θ hzabs (hθδ θ hθK) hθK) hIntK
    have hval : ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad), (c₀ ^ 2 * b₀)
        = c₀ ^ 2 * b₀ * (2 * rad) := by
      rw [MeasureTheory.setIntegral_const (c₀ ^ 2 * b₀),
        MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [hradpos]), smul_eq_mul]
      ring
    have hstep2 : ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad),
          (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) :=
      MeasureTheory.setIntegral_mono_set hIntθ
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
              ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)))
        (Filter.Eventually.of_forall fun θ hθ => hKsub hθ)
    calc c₀ ^ 2 * b₀ * (2 * rad)
        = ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad), (c₀ ^ 2 * b₀) := hval.symm
      _ ≤ ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad),
            (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := hstep1
      _ ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := hstep2

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.resid_expansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory
open Set

namespace Work.FTS.EllipticEst

/-- If two functions agree on the open interval `uIoo a b`, they agree almost everywhere for the
measure restricted to `uIoc a b` (the endpoints have measure zero). -/
private lemma ae_eq_of_eqOn_uIoo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f g (Set.uIoo a b)) :
    f =ᵐ[volume.restrict (Set.uIoc a b)] g := by
  rw [Set.uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
  intro x hx
  exact h (by rwa [Set.uIoo_of_le hab])

/-- **Residual expansion for the first sine mode on `[0, π/2]`.**

For `f ∈ C²` on `[0, π/2]` vanishing at both endpoints, the projection
`a = (4/π) ∫ f sin(2θ)` onto the mode `sin(2θ)` is exactly the `L²`-orthogonal one: the residual
`g = f - a sin(2θ)` is `L²`-orthogonal to `sin(2θ)` and to `2cos(2θ)` (its derivative), and the
`L²`-norms of `f`, `f'` decompose as `∫f² = (π/4)a² + ∫g²` and `∫(f')² = π a² + ∫(g')²`. -/
theorem resid_expansion (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    let a := (4 / π) * ∫ θ in (0:ℝ)..(π / 2), f θ * Real.sin (2 * θ)
    let g := fun θ => f θ - a * Real.sin (2 * θ)
    (∫ θ in (0:ℝ)..(π / 2), g θ * Real.sin (2 * θ) = 0) ∧
    (∫ θ in (0:ℝ)..(π / 2), deriv g θ * (2 * Real.cos (2 * θ)) = 0) ∧
    (∫ θ in (0:ℝ)..(π / 2), (f θ) ^ 2
        = (π / 4) * a ^ 2 + ∫ θ in (0:ℝ)..(π / 2), (g θ) ^ 2) ∧
    (∫ θ in (0:ℝ)..(π / 2), (deriv f θ) ^ 2
        = π * a ^ 2 + ∫ θ in (0:ℝ)..(π / 2), (deriv g θ) ^ 2) := by
  obtain ⟨T1, T2, T3, Dsin, Dcos⟩ := trig_resid
  set a : ℝ := (4 / π) * ∫ θ in (0:ℝ)..(π / 2), f θ * Real.sin (2 * θ) with ha_def
  set g : ℝ → ℝ := fun θ => f θ - a * Real.sin (2 * θ) with hg_def
  have hpi : (0:ℝ) < π/2 := by positivity
  have hpi_le : (0:ℝ) ≤ π/2 := hpi.le
  have hgpt : ∀ θ, g θ = f θ - a * Real.sin (2 * θ) := fun θ => by simp only [hg_def]
  have hsin2_CD : ContDiff ℝ 2 (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hpsi_CD : ContDiff ℝ 2 (fun θ : ℝ => 2 * Real.cos (2 * θ)) := by fun_prop
  have hgCD0 : ContDiffOn ℝ 2 (fun θ : ℝ => f θ - a * Real.sin (2 * θ)) (Set.Icc 0 (π/2)) :=
    hf.sub (ContDiffOn.const_smul a hsin2_CD.contDiffOn)
  have hgCD : ContDiffOn ℝ 2 g (Set.Icc 0 (π/2)) := hgCD0.congr (fun θ _ => hgpt θ)
  have hcont_f : ContinuousOn f (Set.uIcc 0 (π/2)) := by
    rw [Set.uIcc_of_le hpi_le]; exact hf.continuousOn
  have hcont_g : ContinuousOn g (Set.uIcc 0 (π/2)) := by
    rw [Set.uIcc_of_le hpi_le]; exact hgCD.continuousOn
  have hcont_sin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.uIcc 0 (π/2)) := by fun_prop
  have hg0 : g 0 = 0 := by
    rw [hgpt 0, h0, show (2:ℝ)*0 = 0 by ring, Real.sin_zero, mul_zero, sub_zero]
  have hg1 : g (π/2) = 0 := by
    rw [hgpt (π/2), h1, show (2:ℝ)*(π/2) = π by ring, Real.sin_pi, mul_zero, sub_zero]
  have hcdg : ContinuousOn (derivWithin g (Set.Icc 0 (π/2))) (Set.uIcc 0 (π/2)) := by
    rw [Set.uIcc_of_le hpi_le]
    exact hgCD.continuousOn_derivWithin (uniqueDiffOn_Icc hpi) (by norm_num)
  ----------------------------------------------------------------
  -- (1) orthogonality of the residual to sin(2θ)
  have hInt_fs : IntervalIntegrable (fun θ : ℝ => f θ * Real.sin (2*θ)) volume 0 (π/2) :=
    (hcont_f.mul hcont_sin2).intervalIntegrable
  have ha_pi4 : a * (π/4) = ∫ θ in (0:ℝ)..(π/2), f θ * Real.sin (2*θ) := by
    rw [ha_def]
    field_simp
  have h1main : ∫ θ in (0:ℝ)..(π/2), g θ * Real.sin (2*θ) = 0 := by
    have hc : ∫ θ in (0:ℝ)..(π/2), g θ * Real.sin (2*θ)
        = ∫ θ in (0:ℝ)..(π/2), f θ * Real.sin (2*θ) - a * (Real.sin (2*θ))^2 := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [hgpt θ]; ring
    have hInt_a : IntervalIntegrable (fun θ : ℝ => a * (Real.sin (2*θ))^2) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => a * (Real.sin (2*θ))^2) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    rw [hc, intervalIntegral.integral_sub hInt_fs hInt_a, intervalIntegral.integral_const_mul,
      T1, ha_pi4]
    ring
  ----------------------------------------------------------------
  -- (2) orthogonality of d/dθ residual to 2cos(2θ)
  have hpsi_pi : (2:ℝ) * Real.cos (2*(π/2)) = -2 := by
    rw [show (2:ℝ)*(π/2) = π by ring, Real.cos_pi]; ring
  have hpsi_0 : (2:ℝ) * Real.cos (2*0) = 2 := by
    rw [show (2:ℝ)*0 = 0 by ring, Real.cos_zero]; ring
  have hderivpsi : deriv (fun θ : ℝ => 2 * Real.cos (2*θ)) = fun θ => -4 * Real.sin (2*θ) := by
    funext θ; exact Dcos θ
  have h2main : ∫ θ in (0:ℝ)..(π/2), deriv g θ * (2 * Real.cos (2*θ)) = 0 := by
    have hIBP := ibp_contdiffon hpi hgCD hpsi_CD
    have hcross : ∫ x in (0:ℝ)..(π/2), g x * (-4 * Real.sin (2*x)) = 0 := by
      rw [show (∫ x in (0:ℝ)..(π/2), g x * (-4 * Real.sin (2*x)))
          = ∫ x in (0:ℝ)..(π/2), (-4) * (g x * Real.sin (2*x)) by
        apply intervalIntegral.integral_congr; intro x _; dsimp only; ring]
      rw [intervalIntegral.integral_const_mul, h1main]
      ring
    rw [hIBP, hderivpsi]
    dsimp only
    rw [hpsi_pi, hpsi_0, hg1, hg0, hcross]
    ring
  ----------------------------------------------------------------
  -- (3) L² decomposition of f
  have h3main : ∫ θ in (0:ℝ)..(π/2), (f θ)^2
      = (π/4) * a^2 + ∫ θ in (0:ℝ)..(π/2), (g θ)^2 := by
    have hexp : ∫ θ in (0:ℝ)..(π/2), (f θ)^2
        = ∫ θ in (0:ℝ)..(π/2), (g θ)^2 + 2*a*(g θ * Real.sin (2*θ)) + a^2*(Real.sin (2*θ))^2 := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [show f θ = g θ + a * Real.sin (2*θ) by rw [hgpt θ]; ring]
      ring
    have hX : IntervalIntegrable (fun θ : ℝ => (g θ)^2) volume 0 (π/2) :=
      (hcont_g.pow 2).intervalIntegrable
    have hY : IntervalIntegrable (fun θ : ℝ => 2*a*(g θ * Real.sin (2*θ))) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => 2*a*(g θ * Real.sin (2*θ))) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    have hZ : IntervalIntegrable (fun θ : ℝ => a^2*(Real.sin (2*θ))^2) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => a^2*(Real.sin (2*θ))^2) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    rw [hexp, intervalIntegral.integral_add (hX.add hY) hZ, intervalIntegral.integral_add hX hY,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, T1, h1main]
    ring
  ----------------------------------------------------------------
  -- (4) L² decomposition of the derivative
  have hderiv_pt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
      deriv f θ = deriv g θ + 2*a*Real.cos (2*θ) := by
    intro θ hθ
    have hfeq : f = fun θ : ℝ => g θ + a * Real.sin (2 * θ) := by
      funext x; rw [hgpt x]; ring
    have hgd : DifferentiableAt ℝ g θ :=
      (hgCD.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)).differentiableAt (by norm_num)
    have hsd : DifferentiableAt ℝ (fun θ : ℝ => a * Real.sin (2*θ)) θ := by fun_prop
    have hsd' : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (2*θ)) θ := by fun_prop
    rw [hfeq]
    change deriv (g + fun θ : ℝ => a * Real.sin (2*θ)) θ = deriv g θ + 2*a*Real.cos (2*θ)
    rw [deriv_add hgd hsd, deriv_const_mul a hsd', Dsin θ]
    ring
  have hU : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ)^2
      = ∫ θ in (0:ℝ)..(π/2), (deriv g θ)^2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    refine ae_eq_of_eqOn_uIoo hpi_le ?_
    intro x hx
    rw [Set.uIoo_of_le hpi_le] at hx
    dsimp only
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  have h1_4 : ∫ θ in (0:ℝ)..(π/2), (deriv f θ)^2
      = ∫ θ in (0:ℝ)..(π/2), (deriv g θ + 2*a*Real.cos (2*θ))^2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    refine ae_eq_of_eqOn_uIoo hpi_le ?_
    intro x hx
    rw [Set.uIoo_of_le hpi_le] at hx
    dsimp only
    rw [hderiv_pt x hx]
  have h2_4 : ∫ θ in (0:ℝ)..(π/2), (deriv g θ + 2*a*Real.cos (2*θ))^2
      = ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ + 2*a*Real.cos (2*θ))^2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    refine ae_eq_of_eqOn_uIoo hpi_le ?_
    intro x hx
    rw [Set.uIoo_of_le hpi_le] at hx
    dsimp only
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  have hzero : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ)) = 0 := by
    have hc : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ))
        = ∫ θ in (0:ℝ)..(π/2), deriv g θ * (2*Real.cos (2*θ)) := by
      apply intervalIntegral.integral_congr_ae_restrict
      refine ae_eq_of_eqOn_uIoo hpi_le ?_
      intro x hx
      rw [Set.uIoo_of_le hpi_le] at hx
      dsimp only
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
    rw [hc, h2main]
  have hexp4 : ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ + 2*a*Real.cos (2*θ))^2
      = ∫ θ in (0:ℝ)..(π/2), (derivWithin g (Set.Icc 0 (π/2)) θ)^2
          + 2*a*((derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ)))
          + a^2*(2*Real.cos (2*θ))^2 := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    ring
  have h4main : ∫ θ in (0:ℝ)..(π/2), (deriv f θ)^2 = π*a^2 + ∫ θ in (0:ℝ)..(π/2), (deriv g θ)^2 := by
    have hIU : IntervalIntegrable
        (fun θ : ℝ => (derivWithin g (Set.Icc 0 (π/2)) θ)^2) volume 0 (π/2) :=
      (hcdg.pow 2).intervalIntegrable
    have hIY : IntervalIntegrable
        (fun θ : ℝ => 2*a*((derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ)))) volume 0 (π/2) := by
      have hc2 : ContinuousOn
          (fun θ : ℝ => 2*a*((derivWithin g (Set.Icc 0 (π/2)) θ) * (2*Real.cos (2*θ))))
          (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    have hIZ : IntervalIntegrable (fun θ : ℝ => a^2*(2*Real.cos (2*θ))^2) volume 0 (π/2) := by
      have hc2 : ContinuousOn (fun θ : ℝ => a^2*(2*Real.cos (2*θ))^2) (Set.uIcc 0 (π/2)) := by fun_prop
      exact hc2.intervalIntegrable
    rw [h1_4, h2_4, hexp4, intervalIntegral.integral_add (hIU.add hIY) hIZ,
      intervalIntegral.integral_add hIU hIY, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hzero, T3, hU]
    ring
  exact ⟨h1main, h2main, h3main, h4main⟩

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.sinOdd_fourierCoeffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fourier coefficients of the odd extension: the sine-coefficient formula

For `F : ℝ → ℝ` and `L > 0`, the odd extension `sinOdd F` (see `SinCompleteDefs`) has
`n`-th Fourier coefficient on `[-L, L]` given by the sine coefficient of `F` on `[0, L]`:

`fourierCoeffOn (-L < L) (sinOdd F) n = -I / L * ∫_0^L sin (π n θ / L) F θ dθ`.

The proof splits the integral over `[-L, L]` at `0`, substitutes `x ↦ -x` on the left half
(using oddness of `sinOdd F`), and combines the two exponentials
`e^{-iπnx/L}` and `e^{iπnx/L}` into `-2i sin (π n x / L)`.
-/

open MeasureTheory Set
open scoped Interval

namespace Work.FTS.EllipticEst

/-- Pointwise difference of the `-n`-th Fourier monomials at `x` and `-x`, on the circle of
period `T`: the two exponentials combine into `-2i sin (2πnx/T)`. -/
lemma fourier_neg_sub_fourier (T : ℝ) (n : ℤ) (x : ℝ) :
    fourier (-n) ((x : ℝ) : AddCircle T) - fourier (-n) (((-x : ℝ) : AddCircle T))
      = -2 * Complex.I * (Real.sin (2 * Real.pi * n * x / T) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  set y : ℝ := 2 * Real.pi * n * x / T with hy
  have h1 : (2 * ↑Real.pi * Complex.I * ↑(-n) * ↑x / ↑T) = -((y : ℂ) * Complex.I) := by
    rw [hy]; push_cast; ring
  have h2 : (2 * ↑Real.pi * Complex.I * ↑(-n) * ↑(-x) / ↑T) = (y : ℂ) * Complex.I := by
    rw [hy]; push_cast; ring
  rw [h1, h2]
  rw [show -((y : ℂ) * Complex.I) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  simp only [Complex.ofReal_neg]
  ring

/-- The same identity for the period `2L`, with the sine written as `sin (π n x / L)`. -/
lemma fourier_neg_sub_fourier' {L : ℝ} (n : ℤ) (x : ℝ) :
    fourier (-n) ((x : ℝ) : AddCircle (2 * L)) - fourier (-n) (((-x : ℝ) : AddCircle (2 * L)))
      = -2 * Complex.I * (Real.sin (Real.pi * n * x / L) : ℂ) := by
  rw [fourier_neg_sub_fourier]
  rw [show 2 * Real.pi * n * x / (2 * L) = Real.pi * n * x / L by field_simp]

/-- The Fourier integral of the odd extension over `[-L, L]`, reduced to a sine integral over
`[0, L]`. -/
lemma integral_fourier_mul_sinOdd {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) L))) (n : ℤ) :
    ∫ x in (-L)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = (-2 * Complex.I)
          * ∫ θ in (0 : ℝ)..L, (Real.sin (Real.pi * n * θ / L) : ℂ) * (F θ : ℂ) := by
  have hInt : Integrable (sinOdd F) (volume.restrict (Ioc (-L) L)) := hmem.integrable (by norm_num)
  have hsub_L : volume.restrict (Ioc (-L) (0 : ℝ)) ≤ volume.restrict (Ioc (-L) L) :=
    Measure.restrict_mono (s := Ioc (-L) (0 : ℝ)) (s' := Ioc (-L) L)
      (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) le_rfl
  have hsub_R : volume.restrict (Ioc (0 : ℝ) L) ≤ volume.restrict (Ioc (-L) L) :=
    Measure.restrict_mono (s := Ioc (0 : ℝ) L) (s' := Ioc (-L) L)
      (fun x hx => ⟨by linarith [hx.1], hx.2⟩) le_rfl
  have hIntL : Integrable (sinOdd F) (volume.restrict (Ioc (0 : ℝ) L)) :=
    hInt.mono_measure hsub_R
  have hcont1 : Continuous (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L))) := by
    simp only [fourier_coe_apply]; fun_prop
  have hcont2 : Continuous (fun x : ℝ => fourier (-n) (((-x : ℝ)) : AddCircle (2 * L))) := by
    simp only [fourier_coe_apply]; fun_prop
  have hbd1 : ∀ (μ : Measure ℝ), ∀ᵐ x ∂μ,
      ‖fourier (-n) ((x : ℝ) : AddCircle (2 * L))‖ ≤ 1 :=
    fun μ => Filter.Eventually.of_forall (fun x => by rw [fourier_apply, Circle.norm_coe])
  have hbd2 : ∀ (μ : Measure ℝ), ∀ᵐ x ∂μ,
      ‖fourier (-n) (((-x : ℝ)) : AddCircle (2 * L))‖ ≤ 1 :=
    fun μ => Filter.Eventually.of_forall (fun x => by rw [fourier_apply, Circle.norm_coe])
  have hA : Integrable (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      (volume.restrict (Ioc (-L) L)) :=
    hInt.bdd_mul hcont1.aestronglyMeasurable (hbd1 _)
  have hAL : Integrable (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      (volume.restrict (Ioc (0 : ℝ) L)) :=
    hIntL.bdd_mul hcont1.aestronglyMeasurable (hbd1 _)
  have hArev : Integrable
      (fun x : ℝ => fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)))
      (volume.restrict (Ioc (0 : ℝ) L)) :=
    hIntL.neg.bdd_mul hcont2.aestronglyMeasurable (hbd2 _)
  have hIA1 : IntervalIntegrable
      (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x) volume (-L) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (-L : ℝ) ≤ 0)]
    exact hA.mono_measure hsub_L
  have hIA2 : IntervalIntegrable
      (fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ L)]
    exact hAL
  have hIB : IntervalIntegrable
      (fun x : ℝ => fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)))
      volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ L)]
    exact hArev
  have s1 : ∫ x in (-L)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = (∫ x in (-L)..0, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
        + ∫ x in (0 : ℝ)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x :=
    (intervalIntegral.integral_add_adjacent_intervals hIA1 hIA2).symm
  have s2 : ∫ x in (-L)..(0 : ℝ), fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = ∫ x in (0 : ℝ)..L,
          fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * sinOdd F (-x) := by
    simpa using (intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      (a := 0) (b := L)).symm
  have s3 : ∫ x in (0 : ℝ)..L,
        fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * sinOdd F (-x)
      = ∫ x in (0 : ℝ)..L,
          fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [sinOdd_neg]
  have s4 : (∫ x in (0 : ℝ)..L, fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x)))
        + ∫ x in (0 : ℝ)..L, fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
      = ∫ x in (0 : ℝ)..L,
          (fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x))
            + fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x) :=
    (intervalIntegral.integral_add hIB hIA2).symm
  have s5 : ∫ x in (0 : ℝ)..L,
        (fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x))
          + fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x)
      = ∫ x in (0 : ℝ)..L,
          (-2 * Complex.I) * ((Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx0 : 0 < x := by
      rw [uIoc_of_le (by linarith : (0 : ℝ) ≤ L)] at hx
      exact hx.1
    have e1 : fourier (-n) (((-x : ℝ)) : AddCircle (2 * L)) * (-(sinOdd F x))
          + fourier (-n) ((x : ℝ) : AddCircle (2 * L)) * sinOdd F x
        = (fourier (-n) ((x : ℝ) : AddCircle (2 * L))
            - fourier (-n) (((-x : ℝ)) : AddCircle (2 * L))) * sinOdd F x := by
      ring
    rw [e1, fourier_neg_sub_fourier' n x, sinOdd_of_pos hx0]
    ring
  have s6 : ∫ x in (0 : ℝ)..L,
        (-2 * Complex.I) * ((Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ))
      = (-2 * Complex.I)
          * ∫ x in (0 : ℝ)..L, (Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ) :=
    intervalIntegral.integral_const_mul (-2 * Complex.I)
      (fun x : ℝ => (Real.sin (Real.pi * n * x / L) : ℂ) * (F x : ℂ))
  rw [s1, s2, s3, s4, s5, s6]

/-- The `n`-th Fourier coefficient on `[-L, L]` of the odd extension of `F` equals the
(complexified) sine coefficient of `F` on `[0, L]`, with factor `-I / L`. -/
theorem sinOdd_fourierCoeffOn {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MeasureTheory.MemLp (Work.FTS.EllipticEst.sinOdd F) 2
      (MeasureTheory.volume.restrict (Set.Ioc (-L) L)))
    (n : ℤ) :
    fourierCoeffOn (show (-L) < L by linarith) (Work.FTS.EllipticEst.sinOdd F) n
      = -Complex.I / L * ∫ θ in (0:ℝ)..L, (Real.sin (Real.pi * n * θ / L) : ℂ) * (F θ : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsmulC : ∀ z w : ℂ, z • w = z * w := fun z w => by rw [Algebra.smul_def]; simp
  rw [fourierCoeffOn_eq_integral]
  rw [show L - (-L) = 2 * L by ring]
  rw [Complex.real_smul]
  simp only [hsmulC]
  rw [integral_fourier_mul_sinOdd hL hmem n]
  have hcoef : ((1 / (2 * L) : ℝ) : ℂ) * (-2 * Complex.I) = -Complex.I / (L : ℂ) := by
    push_cast
    field_simp
  rw [← mul_assoc, hcoef]

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.w_tail_lintegral_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter

/-- The radial weight can be written `w z = (1 + 1/z)²` for `z ≠ 0`; this exhibits
`w` as a decreasing function of `z` on the positive half-line. -/
private lemma w_eq_one_add_inv_sq {z : ℝ} (hz : z ≠ 0) :
    Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
  have h : (1 : ℝ) + 1 / z = (1 + z) / z := by
    rw [show (1 + z) = (1 : ℝ) + z by ring, add_div, div_self hz]
    ring
  rw [Work.Spaces.w, h, div_pow]

private lemma w_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ Work.Spaces.w z := by
  rw [w_eq_one_add_inv_sq (ne_of_gt hz)]
  positivity

private lemma w_antitoneOn : AntitoneOn Work.Spaces.w (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [w_eq_one_add_inv_sq (ne_of_gt hb), w_eq_one_add_inv_sq (ne_of_gt ha)]
  have h1 : (1 : ℝ) / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  have h2 : (1 : ℝ) + 1 / b ≤ 1 + 1 / a := by linarith
  have hb0 : 0 < b := hb
  exact pow_le_pow_left₀ (by positivity) h2 2

theorem w_tail_lintegral_bound (β : ℝ) (hβ : 1 < β) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))
      ≤ ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) := by
  have hws : 0 ≤ Work.Spaces.w s := w_nonneg hs
  -- Pointwise domination on `[s,∞)`: `w z ≤ w s` there, and `w s ≥ 0`.
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ici s)),
      ENNReal.ofReal (Work.Spaces.w z ^ 2 * z ^ (-β))
        ≤ ENNReal.ofReal (Work.Spaces.w s ^ 2) * ENNReal.ofReal (z ^ (-β)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le hs hz
    have hle : Work.Spaces.w z ≤ Work.Spaces.w s := w_antitoneOn hs hz0 hz
    have hsq : Work.Spaces.w z ^ 2 ≤ Work.Spaces.w s ^ 2 :=
      pow_le_pow_left₀ (w_nonneg hz0) hle 2
    have hzp : 0 ≤ z ^ (-β) := Real.rpow_nonneg (le_of_lt hz0) (-β)
    calc ENNReal.ofReal (Work.Spaces.w z ^ 2 * z ^ (-β))
        ≤ ENNReal.ofReal (Work.Spaces.w s ^ 2 * z ^ (-β)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hsq hzp)
      _ = ENNReal.ofReal (Work.Spaces.w s ^ 2) * ENNReal.ofReal (z ^ (-β)) :=
          ENNReal.ofReal_mul (pow_nonneg hws 2)
  calc ∫⁻ z in Set.Ici s, ENNReal.ofReal (Work.Spaces.w z ^ 2 * z ^ (-β))
      ≤ ∫⁻ z in Set.Ici s,
          ENNReal.ofReal (Work.Spaces.w s ^ 2) * ENNReal.ofReal (z ^ (-β)) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2)
          * ∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-β)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2)
          * ENNReal.ofReal (s ^ (1 - β) / (β - 1)) := by
        rw [Work.Elliptic.lintegral_Ici_ofReal_rpow hβ hs]
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2 * (s ^ (1 - β) / (β - 1))) :=
        (ENNReal.ofReal_mul (pow_nonneg hws 2)).symm
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2 * s ^ (1 - β) / (β - 1)) := by
        rw [mul_div_assoc]

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.wirt_phi_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst

/-- Elementary bound: if `|A| ≤ C * |s|`, `C ≥ 0` and `|B| ≤ 1`, then
`|r * A ^ 2 * (B / s)| ≤ r * C ^ 2 * |s|` for `r > 0`.  (With Lean's totalised division the
case `s = 0` is immediate since then `B / 0 = 0`.) -/
private theorem abs_mul_sq_div_le_aux {r C A B s : ℝ} (hr : 0 < r) (_hC : 0 ≤ C)
    (hA : |A| ≤ C * |s|) (hB : |B| ≤ 1) : |r * A ^ 2 * (B / s)| ≤ r * C ^ 2 * |s| := by
  rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos hr]
  have hs : 0 ≤ |s| := abs_nonneg s
  have hsq : |A| ^ 2 ≤ C ^ 2 * |s| ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg A) hA 2
    rwa [mul_pow] at h
  rcases eq_or_lt_of_le hs with h0 | h0
  · rw [← h0]
    simp
  · have hmul : C ^ 2 * |s| ^ 2 * (1 / |s|) = C ^ 2 * |s| := by field_simp
    have h1 : |B| / |s| ≤ 1 / |s| := div_le_div_of_nonneg_right hB hs
    have h2 : |A| ^ 2 * (|B| / |s|) ≤ C ^ 2 * |s| := by
      calc |A| ^ 2 * (|B| / |s|) ≤ |A| ^ 2 * (1 / |s|) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ ≤ C ^ 2 * |s| ^ 2 * (1 / |s|) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = C ^ 2 * |s| := hmul
    have h3 := mul_le_mul_of_nonneg_left h2 hr.le
    linarith [h3]

theorem wirt_phi_tendsto {a b r : ℝ} (hab : a < b) (hr : 0 < r) (hrb : r * (b - a) = π)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    Filter.Tendsto (fun x => r * (u x) ^ 2 * (Real.cos (r * (x - a)) / Real.sin (r * (x - a))))
        (nhdsWithin a (Set.Ioi a)) (nhds 0) ∧
      Filter.Tendsto (fun x => r * (u x) ^ 2 * (Real.cos (r * (x - a)) / Real.sin (r * (x - a))))
        (nhdsWithin b (Set.Iio b)) (nhds 0) := by
  -- `u` vanishes to first order at both endpoints: it is dominated by `|sin (r · - a)|`.
  obtain ⟨C, hC0, hC⟩ := wirt_sin_bound hab hr hrb hu ha hb
  -- each of the two filters eventually stays inside `[a, b]`, where the bound applies.
  have hmem_a : Set.Icc a b ∈ nhdsWithin a (Set.Ioi a) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hab, fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hmem_b : Set.Icc a b ∈ nhdsWithin b (Set.Iio b) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioi a, isOpen_Ioi, hab, fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  -- the sine majorant tends to `0` at both endpoints (`sin 0 = 0`, `sin π = 0`).
  have hg_a : Filter.Tendsto (fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|)
      (nhdsWithin a (Set.Ioi a)) (nhds 0) := by
    have hc : Continuous fun x : ℝ => Real.sin (r * (x - a)) := by fun_prop
    have h : Filter.Tendsto (fun x : ℝ => Real.sin (r * (x - a)))
        (nhdsWithin a (Set.Ioi a)) (nhds 0) := by
      simpa [Real.sin_zero] using (hc.tendsto a).mono_left nhdsWithin_le_nhds
    simpa using h.abs.const_mul (r * C ^ 2)
  have hg_b : Filter.Tendsto (fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|)
      (nhdsWithin b (Set.Iio b)) (nhds 0) := by
    have hc : Continuous fun x : ℝ => Real.sin (r * (x - a)) := by fun_prop
    have h : Filter.Tendsto (fun x : ℝ => Real.sin (r * (x - a)))
        (nhdsWithin b (Set.Iio b)) (nhds 0) := by
      simpa [hrb, Real.sin_pi] using (hc.tendsto b).mono_left nhdsWithin_le_nhds
    simpa using h.abs.const_mul (r * C ^ 2)
  refine ⟨?_, ?_⟩
  · refine squeeze_zero_norm' (a := fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|) ?_ hg_a
    filter_upwards [hmem_a] with x hx
    rw [Real.norm_eq_abs]
    exact abs_mul_sq_div_le_aux hr hC0 (hC x hx) (Real.abs_cos_le_one _)
  · refine squeeze_zero_norm' (a := fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|) ?_ hg_b
    filter_upwards [hmem_b] with x hx
    rw [Real.norm_eq_abs]
    exact abs_mul_sq_div_le_aux hr hC0 (hC x hx) (Real.abs_cos_le_one _)

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.hasDerivAt_w =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

/-- The weight `w(z) = (1+z)²/z²` is differentiable at every `z ≠ 0`, with
derivative `-2(1+z)/z³`. -/
theorem hasDerivAt_w (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt Work.Spaces.w (-2 * (1 + z) / z ^ 3) z := by
  change HasDerivAt (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (-2 * (1 + z) / z ^ 3) z
  have h1 : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    have h : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h.pow 2
    convert h2 using 1
    ring
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    have h := hasDerivAt_pow 2 z
    convert h using 1
    ring
  have hd := h1.div h2 (by positivity)
  convert hd using 1
  field_simp
  ring

end Work.FTS.EpsEngine.ZTracesAux
end
-- ===== merged: Submission.Work.FTS.EpsEngine.aesm_HkIntegrand_of_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- A finite sum (evaluated pointwise) of a.e. strongly measurable real functions is a.e.
strongly measurable. -/
private lemma aesm_finsetSum_apply {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ}
    (hf : ∀ i ∈ s, MeasureTheory.AEStronglyMeasurable (f i) μ) :
    MeasureTheory.AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, f i a) μ := by
  have h := Finset.aestronglyMeasurable_sum (M := ℝ) (f := f) s hf
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  exact Finset.sum_apply a s f

theorem aesm_HkIntegrand_of_slots {μ : MeasureTheory.Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ}
    {α : ℝ} {k : ℕ} {z θ : ℝ}
    (h : ∀ j i : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (B s) z θ) μ) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) z θ) μ := by
  unfold Work.Spaces.HkIntegrand
  have hA : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (B s) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) μ :=
    aesm_finsetSum_apply (fun i _ => ((h i 0).mul_const
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))).pow 2)
  have hB : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) μ :=
    aesm_finsetSum_apply (fun i _ => aesm_finsetSum_apply (fun j _ => by
      by_cases hh : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun s : ℝ => (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun s => ite_eq_left hh
        rw [hthis]
        exact (((h j i).mul_const (Work.Spaces.Wt α z θ)).pow 2)
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun _ : ℝ => (0:ℝ) :=
          funext fun s => ite_eq_right hh
        rw [hthis]
        exact MeasureTheory.aestronglyMeasurable_const))
  exact hA.add hB

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.XferDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Work.FTS.FireFix.Clauses

/-- The point of `ℝ³` (coordinates `0,1` span the plane, coordinate `2` is the axis) with
coordinates `(a, b, t)`. -/
def pt3 (a b t : ℝ) : EuclideanSpace ℝ (Fin 3) := !₂[a, b, t]

@[simp] lemma pt3_zero (a b t : ℝ) : pt3 a b t 0 = a := by simp [pt3]
@[simp] lemma pt3_one (a b t : ℝ) : pt3 a b t 1 = b := by simp [pt3]
@[simp] lemma pt3_two (a b t : ℝ) : pt3 a b t 2 = t := by simp [pt3]

@[simp] lemma pt3_prodCongr {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (e₁ : α ≃ᵐ β) (e₂ : γ ≃ᵐ δ) (a : α) (b : γ) :
    (e₁.prodCongr e₂) (a, b) = (e₁ a, e₂ b) := rfl

/-- The coordinate equivalence `ℝ³ ≃ᵐ ℝ × (ℝ × ℝ)`: `x ↦ (x 2, (x 0, x 1))`. -/
noncomputable def cx : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.finTwoArrow (α := ℝ))))


/-- The inverse coordinate map. -/
lemma cx_symm_pt3 (a b t : ℝ) : cx.symm (t, (a, b)) = pt3 a b t := by
  rw [← cx.symm_apply_apply (pt3 a b t)]
  congr 1

lemma cx_symm_pt3' (t : ℝ) (v : ℝ × ℝ) : cx.symm (t, v) = pt3 v.1 v.2 t := by
  obtain ⟨a, b⟩ := v
  exact cx_symm_pt3 a b t

theorem measurePreserving_cx : MeasurePreserving cx MeasureTheory.volume MeasureTheory.volume := by
  refine MeasurePreserving.trans (μb := MeasureTheory.volume) ?_ ?_
  · exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (PiLp.volume_preserving_toLp (Fin 3))
  · refine MeasurePreserving.trans (μb := MeasureTheory.volume) ?_ ?_
    · exact volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
    · exact (MeasurePreserving.id MeasureTheory.volume).prod
        (volume_preserving_finTwoArrow ℝ)

/-- **Fubini in the coordinates `(t, v)`**: an integral over `ℝ³` is an iterated integral over the
axis coordinate `t` and the plane coordinates `v`. -/
theorem lintegral_eucl3_eq_prod {g : EuclideanSpace ℝ (Fin 3) → ENNReal} (hg : Measurable g) :
    ∫⁻ x : EuclideanSpace ℝ (Fin 3), g x
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, g (pt3 v.1 v.2 t) := by
  have h1 : ∫⁻ p : ℝ × (ℝ × ℝ), g (cx.symm p) = ∫⁻ x : EuclideanSpace ℝ (Fin 3), g x :=
    (MeasurePreserving.symm cx measurePreserving_cx).lintegral_comp_emb
      cx.symm.measurableEmbedding g
  have h2 : ∫⁻ p : ℝ × (ℝ × ℝ), g (cx.symm p)
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, g (cx.symm (t, v)) := by
    rw [show (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ)))
        = (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure (ℝ × ℝ))
        from rfl]
    exact lintegral_prod (fun a : ℝ × (ℝ × ℝ) => g (cx.symm a))
      (hg.comp cx.symm.measurable).aemeasurable
  rw [← h1, h2]
  exact lintegral_congr fun t => lintegral_congr fun v => congrArg g (cx_symm_pt3' t v)

end Work.FTS.FireFix.Clauses
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.GalApprox.ladder_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.GalBasis.GalApprox.ladder_bound`

The sharp Taylor ladder with Lagrange remainder:  if `H` is `C^4` at every point of `[a,b]`
and `|H⁗| ≤ M` there, then for every `i ≤ 4` and `x ∈ [a,b]` the `i`-th derivative of `H` at `x`
differs from the `i`-th derivative (at `x`) of the order-`3` Taylor polynomial of `H` at `a`
by at most `M * (b - a)^(4-i) / (4-i)!`.

The proof has three parts.

* The Taylor polynomial `T y = ∑_{k<4} H^{(k)}(a)/k! * (y-a)^k` has `i`-th derivative
  `T^{(i)} x = ∑_{s ∈ Icc i 3} H^{(s)}(a) * (x-a)^(s-i)/(s-i)!`
  (`iteratedDeriv_sum_pow_sub_gal` computes the iterated derivatives of a finite combination of
  powers and the range-`4` sum is truncated at `i` because `k.descFactorial i = 0` for `k < i`),
  and `T⁗ = 0` while `T^{(i)}(a) = H^{(i)}(a)` for `i ≤ 3`.
* `h := H - T` therefore has `h^{(i)}(a) = 0` for `i ≤ 3` and `|h⁗| ≤ M` on `[a,b]`; and the
  difference appearing in the statement is exactly `h^{(i)}(x)`.
* The sharp ladder `|h^{(i)} x| ≤ M (x-a)^(4-i)/(4-i)!` is proved one step at a time
  (`ladder_step_gen`): downward induction from `i = 4` to `i = 0`, each step being Rolle's
  theorem applied to `t ↦ h^{(i)} t - c (t-a)^n` with `c = h^{(i)} x/(x-a)^n`.
  (This is the classical "cleverly weighted Rolle" proof of the Lagrange remainder, and it is
  what gives the sharp `1/(4-i)!` factor that a naive repeated mean value bound loses.)
-/

noncomputable section

open Set Finset Filter
open scoped Topology

namespace Work.FTS.GalBasis.GalApprox

set_option linter.unnecessarySeqFocus false

/-! ## Iterated derivatives of a finite combination of powers of `(y - a)` -/


/-! ## An elementary fact about iterated derivatives on an open interval -/


/-! ## One step of the ladder: Rolle's theorem with the power weight -/


/-! ## The ladder bound -/


end Work.FTS.GalBasis.GalApprox
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.HkSq_le_of_ae_dominated =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut


end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.GalBasis.cut.SliceGammaCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cut

set_option autoImplicit false
set_option maxHeartbeats 1600000



end Work.FTS.GalBasis.cut
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.isPolySum_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

open scoped BigOperators


end Work.FTS.GalBasis
end
-- ===== merged: Submission.Work.FTS.GalBasis.isPolySum_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

open scoped BigOperators


end Work.FTS.GalBasis
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false

/-- The right end `x₁ = sin(π/4) = 1/√2` of the *near* region `(0,x₁]` (`θ ∈ (0,π/8]`), where the
substitution `x = sin(2θ)` has `κ x = √(1-x²) ≥ 1/√2`. -/
def xNear : ℝ := Real.sin (Real.pi / 4)


/-- Its inverse `x ↦ θ = arcsin(x)/2` on `(-1,1)`. -/
def thetaOf (x : ℝ) : ℝ := Real.arcsin x / 2

/-- The `x`-coordinate version of a slice `h`: `x ↦ h (arcsin(x)/2)`. -/
def sliceX (h : ℝ → ℝ) : ℝ → ℝ := fun x => h (thetaOf x)

/-- `κ x = cos(2 θ(x))`, the factor relating `D_θ = sin(2θ)∂_θ` to `x ∂_x`; on `(-1,1)` it is
`√(1-x²)`. -/
def kappa (x : ℝ) : ℝ := Real.cos (2 * thetaOf x)

/-- The operator `G u = 2κ · x ∂_x u`: the transport of `D_θ` to the `x`-variable. -/
def Gop (u : ℝ → ℝ) : ℝ → ℝ := fun x => 2 * kappa x * (x * deriv u x)

/-- The coefficients of the expansion `G^i u = Σ_{j} b i j · x^j ∂_x^j u`:
`b 0 0 = 1`, `b 0 j = 0` for `j ≠ 0`, and

  `b (i+1) j = 2κ · (x · (b i j)' + j · b i j) + (if j = 0 then 0 else 2κ · b i (j-1))`,

the first term coming from `2κ x ∂_x` acting on the coefficient and the `x^j ∂_x^j` factor, the
second from `∂_x` falling on `∂_x^j u`. -/
def bCoeff : ℕ → ℕ → ℝ → ℝ
  | 0, j => fun _ => if j = 0 then 1 else 0
  | (i + 1), j => fun x =>
      2 * kappa x * (x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x)
        + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)

/-- The coefficients of the expansion `G^i (2κ ∂_x f) = Σ_{l} a i l · x^l ∂_x^{l+1} f`; the
recursion is the same as for `bCoeff` but with the initial datum `a 0 0 = 2κ`, which is the
`x`-form of `∂_θ h = 2 cos(2θ) ∂_x (h∘thetaOf)`. -/
def aCoeff : ℕ → ℕ → ℝ → ℝ
  | 0, j => fun x => if j = 0 then 2 * kappa x else 0
  | (i + 1), j => fun x =>
      2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
        + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)

@[simp] theorem bCoeff_zero_zero : bCoeff 0 0 = fun _ => (1 : ℝ) := rfl
@[simp] theorem aCoeff_zero_zero : aCoeff 0 0 = fun x => 2 * kappa x := rfl

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.csWeightedInterval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set

/-- **Cauchy–Schwarz on `(0,x)` with the Hardy weight split.**  For `γ > -1`, `x > 0` and an
`F : ℝ → ℝ` whose weighted square and whose `k`-weighted first factor are integrable on `(0,x]`,

  `(∫_0^x s^k F(s) ds)² ≤ (∫_0^x s^γ ds) · (∫_0^x s^{2k-γ} F(s)² ds)`.

The splitting is `s^k F = s^{γ/2} · s^{k-γ/2} F`, using `(s^{γ/2})² = s^γ` and
`(s^{k-γ/2}F)² = s^{2k-γ}F²` on `s > 0`.

The proof converts the three interval integrals to set integrals over `Ioc 0 x`
(`intervalIntegral.integral_of_le`), supplies the two `MemLp 2 (volume.restrict (Ioc 0 x))`
hypotheses via `MeasureTheory.memLp_two_iff_integrable_sq` (the a.e. strong measurability of `F`
following from the integrability of `s^k F` on `Ioc 0 x`, since `s^k` is nonvanishing there),
applies `Work.Spaces.cs_integral` to `u s = s^{γ/2}` and `v s = s^{k-γ/2} F s`, and identifies the
pointwise products a.e. via `Real.rpow_add` / `Real.rpow_mul`. -/
theorem csWeightedInterval (k : ℕ) (γ x : ℝ) (hx : 0 < x) (hγ : -1 < γ) :
    ∀ F : ℝ → ℝ,
      MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) (Set.Ioc 0 x) →
      MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * F s) (Set.Ioc 0 x) →
      (∫ s in (0 : ℝ)..x, s ^ k * F s) ^ 2
        ≤ (∫ s in (0 : ℝ)..x, s ^ γ) * (∫ s in (0 : ℝ)..x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by
  intro F hF2 hF1
  have hx0 : (0 : ℝ) ≤ x := hx.le
  -- Strong measurability of `F` on `(0,x]`, from the integrability of `s^k * F s` there.
  have hFmeas : AEStronglyMeasurable F (volume.restrict (Ioc 0 x)) := by
    have hinv : AEStronglyMeasurable (fun s : ℝ => (s ^ k)⁻¹) (volume.restrict (Ioc 0 x)) := by
      fun_prop
    have h2 : AEStronglyMeasurable (fun s : ℝ => (s ^ k)⁻¹ * (s ^ k * F s))
        (volume.restrict (Ioc 0 x)) := hinv.mul hF1.aestronglyMeasurable
    refine h2.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt hs.1)), one_mul]
  -- `s^γ` is integrable on `(0,x]` because `γ > -1`.
  have hIγ : IntegrableOn (fun s : ℝ => s ^ γ) (Ioc 0 x) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx0]
    exact intervalIntegral.intervalIntegrable_rpow' hγ
  -- The three a.e. identifications on `(0,x]`.
  have hA2 : (fun s : ℝ => (s ^ (γ / 2)) ^ 2) =ᵐ[volume.restrict (Ioc 0 x)]
      (fun s : ℝ => s ^ γ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
    ring_nf
  have hB2 : (fun s : ℝ => (s ^ ((k : ℝ) - γ / 2) * F s) ^ 2)
      =ᵐ[volume.restrict (Ioc 0 x)]
      (fun s : ℝ => s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
    congr 2
    ring
  have hAB : (fun s : ℝ => s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s))
      =ᵐ[volume.restrict (Ioc 0 x)] (fun s : ℝ => s ^ k * F s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← mul_assoc, ← Real.rpow_add hs.1,
      show γ / 2 + ((k : ℝ) - γ / 2) = (k : ℝ) by ring, Real.rpow_natCast]
  -- The two `MemLp` inputs for Cauchy–Schwarz.
  have hA : MemLp (fun s : ℝ => s ^ (γ / 2)) 2 (volume.restrict (Ioc 0 x)) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · fun_prop
    · exact hIγ.congr hA2.symm
  have hB : MemLp (fun s : ℝ => s ^ ((k : ℝ) - γ / 2) * F s) 2
      (volume.restrict (Ioc 0 x)) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · have hrp : AEStronglyMeasurable (fun s : ℝ => s ^ ((k : ℝ) - γ / 2))
          (volume.restrict (Ioc 0 x)) := by fun_prop
      exact hrp.mul hFmeas
    · exact hF2.congr hB2.symm
  have key : (∫ s in Ioc 0 x, s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s)) ^ 2
      ≤ (∫ s in Ioc 0 x, s ^ γ) * (∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by
    have h := Work.Spaces.cs_integral hA hB
    have e1 : (∫ s in Ioc 0 x, (fun s : ℝ => s ^ (γ / 2)) s ^ 2) = ∫ s in Ioc 0 x, s ^ γ :=
      integral_congr_ae hA2
    have e2 : (∫ s in Ioc 0 x, (fun s : ℝ => s ^ ((k : ℝ) - γ / 2) * F s) s ^ 2)
        = ∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2 :=
      integral_congr_ae hB2
    rw [e1, e2] at h
    exact h
  have eAB : (∫ s in (0 : ℝ)..x, s ^ k * F s)
      = ∫ s in Ioc 0 x, s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s) := by
    rw [intervalIntegral.integral_of_le hx0]
    exact (integral_congr_ae hAB).symm
  have eA : (∫ s in Ioc 0 x, s ^ γ) = ∫ s in (0 : ℝ)..x, s ^ γ := by
    rw [intervalIntegral.integral_of_le hx0]
  have eB : (∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2)
      = ∫ s in (0 : ℝ)..x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2 := by
    rw [intervalIntegral.integral_of_le hx0]
  calc (∫ s in (0 : ℝ)..x, s ^ k * F s) ^ 2
      = (∫ s in Ioc 0 x, s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s)) ^ 2 := by rw [eAB]
    _ ≤ (∫ s in Ioc 0 x, s ^ γ) * (∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := key
    _ = (∫ s in (0 : ℝ)..x, s ^ γ)
          * (∫ s in (0 : ℝ)..x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by rw [eA, eB]

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.derivIntegrablePrimitive =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the derivative and the primitive form, from a `sin(2θ)^{-η}` weight

Let `h : ℝ → ℝ` be `C^∞` on `(0, π/2)`, tending to `0` at `0⁺`, and suppose
`(h')² sin(2·)^{-η}` is integrable on `Iθ = [0, π/2]`.  Then for every
`θ ∈ (0, π/2)` the derivative `h'` and its square are integrable on `(0, θ]`, and
`h θ = ∫_0^θ h'`.

The only point where the weight is used is that

`1 ≤ sin(2x)^{-η}`  for `x ∈ (0, θ]`

(since `0 < sin(2x) ≤ 1` and `η ≥ 0`), which turns the hypothesis into integrability
of `(h')²` on the (fixed, bounded) interval `(0, θ]`; the function `h'` itself is then
dominated by `(h')² + 1` and the constant `1` is integrable on a bounded interval.
The primitive form is `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`,
with the right-hand endpoint value supplied by continuity at the interior point `θ`
and the left-hand one by the hypothesis on the limit at `0`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.H2.DivQ

theorem derivIntegrablePrimitive {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hten : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc 0 θ) ∧
    MeasureTheory.IntegrableOn (deriv h) (Set.Ioc 0 θ) ∧
    IntervalIntegrable (deriv h) MeasureTheory.volume 0 θ ∧
    IntervalIntegrable (fun x : ℝ => (deriv h x) ^ 2) MeasureTheory.volume 0 θ ∧
    h θ = ∫ x in (0:ℝ)..θ, deriv h x := by
  have hθ0 : (0:ℝ) < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  -- `(0, θ] ⊆ [0, π/2]`, so the hypothesis restricts to `(0, θ]`
  have hsub : Set.Ioc 0 θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt (lt_of_le_of_lt hx.2 hθ2)⟩
  -- the key pointwise fact: `1 ≤ sin(2x)^{-η}` on `(0, θ]`, since `sin(2x) ∈ (0, 1]`
  have hone_le_rpow : ∀ x ∈ Set.Ioc 0 θ,
      (1:ℝ) ≤ (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    intro x hx
    have hsin_pos : 0 < Real.sin (2 * x) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [hx.1]
      · linarith [hx.2, hθ2]
    have heta_nn : (0:ℝ) ≤ Work.Spaces.eta := by
      unfold Work.Spaces.eta; norm_num
    have hpow_le : (Real.sin (2 * x)) ^ (Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hsin_pos) (Real.sin_le_one _) heta_nn
    rw [Real.rpow_neg (le_of_lt hsin_pos)]
    simpa [one_div] using
      one_le_one_div (Real.rpow_pos_of_pos hsin_pos Work.Spaces.eta) hpow_le
  -- integrability of `(h')²` on `(0, θ]`, dominated by the hypothesis
  have hsq : IntegrableOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc 0 θ) := by
    have hg : IntegrableOn
        (fun x : ℝ => (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)))
        (Set.Ioc 0 θ) := hint.mono_set hsub
    refine Integrable.mono' hg
      ((measurable_deriv h).pow_const 2).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hone_le_rpow x hx, sq_nonneg (deriv h x)]
  -- integrability of the constant on the bounded interval `(0, θ]`
  have hone : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioc 0 θ) := by
    apply integrableOn_const
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  -- integrability of `h'`, dominated by `(h')² + 1`
  have hd : IntegrableOn (deriv h) (Set.Ioc 0 θ) := by
    have hg : IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 + 1) (Set.Ioc 0 θ) := hsq.add hone
    refine Integrable.mono' hg ((measurable_deriv h).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (deriv h x), sq_abs (deriv h x), sq_nonneg (|deriv h x| - 1)]
  have hII : IntervalIntegrable (deriv h) MeasureTheory.volume 0 θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hθ0)).2 hd
  have hIIsq : IntervalIntegrable (fun x : ℝ => (deriv h x) ^ 2) MeasureTheory.volume 0 θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hθ0)).2 hsq
  -- the primitive form, via the fundamental theorem of calculus with limits at both ends
  have hdiffOn : DifferentiableOn ℝ h (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.differentiableOn (by simp)
  have hderiv : ∀ x ∈ Set.Ioo 0 θ, HasDerivAt h (deriv h x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hθ.2⟩
    exact (hdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hx')).hasDerivAt
  have hb : Tendsto h (𝓝[<] θ) (𝓝 (h θ)) :=
    (hdiffOn.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hθ)).mono_left nhdsWithin_le_nhds
  have hFTC : ∫ x in (0:ℝ)..θ, deriv h x = h θ - 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hθ0 hderiv hII hten hb
  exact ⟨hsq, hd, hII, hIIsq, by linarith [hFTC]⟩

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.divSinPrimitiveVanish =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Boundary vanishing of the weighted iterated derivatives (`DivQ`)

This file proves `Work.FTS.H2.DivQ.divSinPrimitiveVanish`: if `f` is `C^∞` on `(0,x₁]` and
`∫_0^{x₁} x^{2k-γ}(f^{(k+1)})² < ∞` with `γ > -1`, then `x^j f^{(j)}(x) → 0` at `0⁺` for every
`1 ≤ j ≤ k`.

The proof is a downward induction on `j`.  The base case `j = k` is the analytic heart: writing
`F = f^{(k)}`, `G = f^{(k+1)}` and using the fundamental theorem of calculus
`F(x) = F(δ) - ∫_x^δ G` together with the weighted AM–GM pointwise inequality
`|G(s)| ≤ (x^k/2) s^{γ-2k} + (1/(2x^k)) s^{2k-γ} G(s)²` (valid for every `x > 0`), one gets

  `x^k|F(x)| ≤ x^k|F(δ)| + (x^{2k}/2)∫_x^δ s^{γ-2k} ds + (1/2)∫_x^δ s^{2k-γ}G²`,

where the middle term tends to `0` (`van_powMul_rpow_integral`) and the last one is bounded by the
(small) tail `∫_{(0,δ)} s^{2k-γ}G²` of an integrable function (`hardyIter_tendsto_zero`).
The induction step `j+1 → j` only uses the *limit* form of the hypothesis at level `j+1`.
-/

namespace Work.FTS.H2.DivQ

open MeasureTheory Filter Set
open scoped Topology

/-- **Scalar weighted integral limit.**  For `x₁ > 0`, `n ≥ 1` and `n + q + 1 > 0`, the weighted
integral `x ^ n * ∫_x^{x₁} s ^ q ds` tends to `0` as `x → 0⁺` (`s ^ q` is `Real.rpow`).

For `0 < x < x₁` the primitive gives `x^n * ∫_x^{x₁} s^q = x^n (x₁^{q+1} - x^{q+1})/(q+1)` when
`q ≠ -1`, and `x^n (log x₁ - log x)` when `q = -1`; in the first case the two terms tend to `0`
because `n > 0` and `n + q + 1 > 0`, in the second because `x^n log x → 0` at `0⁺` for `n ≥ 1`. -/
theorem van_powMul_rpow_integral (n : ℕ) (q : ℝ) (hn : 1 ≤ n)
    (hq : 0 < (n : ℝ) + q + 1) {x₁ : ℝ} (hx₁ : 0 < x₁) :
    Filter.Tendsto (fun x : ℝ => x ^ n * ∫ s in x..x₁, s ^ q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hxn : Filter.Tendsto (fun x : ℝ => x ^ n) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := hid.pow n
    simpa [zero_pow (by omega : n ≠ 0)] using h
  have hzero : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) x₁ → (0 : ℝ) ∉ Set.uIcc x x₁ := by
    intro x hx
    rw [Set.uIcc_of_le hx.2.le]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hx.1)
  rcases eq_or_ne q (-1) with hq1 | hq1
  · -- the logarithmic case `q = -1`
    subst hq1
    have hkey : Filter.Tendsto (fun x : ℝ => x ^ n * (Real.log x₁ - Real.log x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h2 : Filter.Tendsto (fun x : ℝ => Real.log x * x ^ ((n : ℝ)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_log_mul_rpow_nhdsGT_zero (by positivity : (0 : ℝ) < (n : ℝ))
      have h2' : Filter.Tendsto (fun x : ℝ => x ^ n * Real.log x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine Filter.Tendsto.congr' ?_ h2
        filter_upwards with x
        rw [Real.rpow_natCast, mul_comm]
      have h1 : Filter.Tendsto (fun x : ℝ => x ^ n * Real.log x₁)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hxn.mul_const (Real.log x₁)
      simpa only [mul_sub, sub_zero] using h1.sub h2'
    refine Filter.Tendsto.congr' ?_ hkey
    filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
    have h0 := hzero x hx
    have hlogeq : (∫ s in x..x₁, s ^ (-1 : ℝ)) = Real.log x₁ - Real.log x := by
      rw [show (∫ s in x..x₁, s ^ (-1 : ℝ)) = ∫ s in x..x₁, s⁻¹ by
            simp only [Real.rpow_neg_one],
          integral_inv h0, Real.log_div (ne_of_gt hx₁) (ne_of_gt hx.1)]
    rw [hlogeq]
  · -- the power case `q ≠ -1`
    have hkey : Filter.Tendsto
        (fun x : ℝ => (x₁ ^ (q + 1) * x ^ n - x ^ ((n : ℝ) + q + 1)) / (q + 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun x : ℝ => x₁ ^ (q + 1) * x ^ n)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hxn.const_mul (x₁ ^ (q + 1))
      have h2 : Filter.Tendsto (fun x : ℝ => x ^ ((n : ℝ) + q + 1))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        Filter.Tendsto.rpow_const_nhds_zero (f := fun x : ℝ => x) hid hq
      simpa using (h1.sub h2).div_const (q + 1)
    refine Filter.Tendsto.congr' ?_ hkey
    filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
    have h0 := hzero x hx
    have hir : (∫ s in x..x₁, s ^ q) = (x₁ ^ (q + 1) - x ^ (q + 1)) / (q + 1) :=
      integral_rpow (Or.inr ⟨hq1, h0⟩)
    have hxpow : x ^ n * x ^ (q + 1) = x ^ ((n : ℝ) + q + 1) := by
      have hcast : (x : ℝ) ^ n = x ^ ((n : ℝ)) := (Real.rpow_natCast x n).symm
      rw [hcast, ← Real.rpow_add hx.1 (n : ℝ) (q + 1),
        show (n : ℝ) + (q + 1) = (n : ℝ) + q + 1 from by ring]
    rw [hir, mul_div_assoc', mul_sub, hxpow]
    ring

/-- **Weighted AM–GM on an interval.**  For `a > 0`, `0 < x ≤ σ` and `h` continuous on `[x,σ]`,
`∫_x^σ |h| ≤ (a/2)·∫_x^σ s^e + (1/(2a))·∫_x^σ s^{-e}·h(s)²` (all powers are `Real.rpow`).

Pointwise `|h s| = s^{e/2}·(s^{-e/2}|h s|)` for `s > 0`, and the elementary AM–GM
`2uv ≤ a u² + v²/a` with `u = s^{e/2}`, `v = s^{-e/2}|h s|` gives
`|h s| ≤ (a/2) s^e + (1/(2a)) s^{-e} h(s)²`; integrate over `[x,σ]`. -/
theorem van_amgm_integral (h : ℝ → ℝ) {e a x σ : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxσ : x ≤ σ) (hcont : ContinuousOn h (Set.Icc x σ)) :
    ∫ s in x..σ, |h s| ≤ (a / 2) * (∫ s in x..σ, s ^ e)
      + (1 / (2 * a)) * (∫ s in x..σ, s ^ (-e) * (h s) ^ 2) := by
  have hs0 : ∀ s ∈ Set.Icc x σ, 0 < s := fun s hs => lt_of_lt_of_le hx hs.1
  have hpt : ∀ s ∈ Set.Icc x σ,
      |h s| ≤ (a / 2) * s ^ e + (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2) := by
    intro s hs
    have hspos := hs0 s hs
    have h1 : s ^ (e / 2) * (s ^ (-e / 2) * |h s|) = |h s| := by
      rw [← mul_assoc, ← Real.rpow_add hspos,
        show e / 2 + (-e / 2) = 0 from by ring, Real.rpow_zero, one_mul]
    have h2 : (s ^ (e / 2)) ^ 2 = s ^ e := by
      rw [pow_two, ← Real.rpow_add hspos, show e / 2 + e / 2 = e from by ring]
    have h3 : (s ^ (-e / 2) * |h s|) ^ 2 = s ^ (-e) * (h s) ^ 2 := by
      rw [mul_pow, sq_abs, pow_two (s ^ (-e / 2)), ← Real.rpow_add hspos,
        show -e / 2 + -e / 2 = -e from by ring]
    have hab := two_mul_le_mul_sq_add_div_sq (a := a) (u := s ^ (e / 2))
      (v := s ^ (-e / 2) * |h s|) ha
    rw [h1, h2, h3] at hab
    calc |h s| = (1 / 2) * (2 * |h s|) := by ring
      _ ≤ (1 / 2) * (a * s ^ e + (s ^ (-e) * (h s) ^ 2) / a) :=
          mul_le_mul_of_nonneg_left hab (by norm_num)
      _ = (a / 2) * s ^ e + (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2) := by ring
  have hcont1 : ContinuousOn (fun s : ℝ => |h s|) (Set.Icc x σ) := hcont.abs
  have hcontE : ContinuousOn (fun s : ℝ => s ^ e) (Set.Icc x σ) :=
    continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt (hs0 s hs))
  have hcontE' : ContinuousOn (fun s : ℝ => s ^ (-e)) (Set.Icc x σ) :=
    continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt (hs0 s hs))
  have hcont2 : ContinuousOn
      (fun s : ℝ => (a / 2) * s ^ e + (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2))
      (Set.Icc x σ) :=
    (continuousOn_const.mul hcontE).add
      (continuousOn_const.mul (hcontE'.mul (hcont.pow 2)))
  have hmono := intervalIntegral.integral_mono_on hxσ
    (hcont1.intervalIntegrable_of_Icc (μ := volume) hxσ)
    (hcont2.intervalIntegrable_of_Icc (μ := volume) hxσ) hpt
  have hi1 : IntervalIntegrable (fun s : ℝ => (a / 2) * s ^ e) volume x σ :=
    (continuousOn_const.mul hcontE).intervalIntegrable_of_Icc (μ := volume) hxσ
  have hi2 : IntervalIntegrable
      (fun s : ℝ => (1 / (2 * a)) * (s ^ (-e) * (h s) ^ 2)) volume x σ :=
    (continuousOn_const.mul (hcontE'.mul (hcont.pow 2))).intervalIntegrable_of_Icc (μ := volume) hxσ
  rw [intervalIntegral.integral_add hi1 hi2] at hmono
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  simpa using hmono

/-- Monotonicity of the set integral in the domain, for a nonnegative integrand. -/
lemma van_setIntegral_mono_Ioc {f : ℝ → ℝ} {x δ : ℝ} (hx : 0 < x)
    (hint : IntegrableOn f (Set.Ioc 0 δ)) (hnn : ∀ y ∈ Set.Ioc 0 δ, 0 ≤ f y) :
    ∫ y in Set.Ioc x δ, f y ≤ ∫ y in Set.Ioc 0 δ, f y := by
  refine integral_mono_measure (Measure.restrict_mono ?_ le_rfl) ?_ hint
  · exact Set.Ioc_subset_Ioc (le_of_lt hx) le_rfl
  · filter_upwards [ae_restrict_mem (μ := volume) (s := Set.Ioc 0 δ) measurableSet_Ioc] with y hy
    exact hnn y hy

/-- The base case `j = k` of the downward induction: from the integrability of
`x ↦ x^{2k-γ}(f^{(k+1)}x)²` on `(0,x₁]` (and `k ≥ 1`) deduce `x^k f^{(k)}(x) → 0` at `0⁺`. -/
private lemma van_baseCase (k : ℕ) (hk : 1 ≤ k) {γ x₁ : ℝ} (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hB : IntegrableOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    Filter.Tendsto (fun x : ℝ => x ^ k * iteratedDeriv k f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the tail of the weighted integral is small for small `δ`
  have hΨ : Filter.Tendsto
      (fun δ : ℝ => ∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2)
      (nhds 0) (nhds 0) := hardyIter_tendsto_zero hx₁ hB
  have hEv₁ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 4 :=
    Filter.Tendsto.eventually_lt (hΨ.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (by linarith)
  have hEv₂ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  have hEv₃ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < x₁ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hx₁)
  obtain ⟨δ, hδpos, hδx, hδsmall⟩ := (hEv₂.and (hEv₃.and hEv₁)).exists
  -- the two decay inputs at the level of `x`
  have hq : 0 < ((2 * k : ℕ) : ℝ) + (γ - 2 * (k : ℝ)) + 1 := by
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [hcast]; linarith
  have hA : Filter.Tendsto
      (fun x : ℝ => (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := van_powMul_rpow_integral (2 * k) (γ - 2 * (k : ℝ)) (by omega) hq hδpos
    have h := h0.const_mul (1 / 2 : ℝ)
    refine Filter.Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring
  have hA' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))) < ε / 2 :=
    Filter.Tendsto.eventually_lt hA tendsto_const_nhds (by linarith)
  have hC : Filter.Tendsto (fun x : ℝ => x ^ k * |iteratedDeriv k f δ|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h := (hid.pow k).mul_const |iteratedDeriv k f δ|
    simpa [zero_pow (by omega : k ≠ 0)] using h
  have hC' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ k * |iteratedDeriv k f δ| < ε / 4 :=
    Filter.Tendsto.eventually_lt hC tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hA', hC'] with x hx hxA hxC
  have hxk : 0 < x ^ k := pow_pos hx.1 k
  have hxδ : x ≤ δ := hx.2.le
  -- fundamental theorem of calculus
  have hFTC : iteratedDeriv k f x
      = iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s := by
    have h := intervalIntegral_iteratedDeriv_succ hf k hx.1 hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (k + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (k + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv k f x|
      ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by
    have h := abs_add_le (iteratedDeriv k f δ) (-(∫ s in x..δ, iteratedDeriv (k + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s|
        ≤ |iteratedDeriv k f δ| + |∫ s in x..δ, iteratedDeriv (k + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using h
      _ ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by linarith [hI]
  -- the weighted AM–GM bound
  have hcontG : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Icc x δ) :=
    continuousOn_iteratedDeriv_Icc hf (k + 1) hx.1 hδx
  have hamgm := van_amgm_integral (iteratedDeriv (k + 1) f) (e := γ - 2 * (k : ℝ)) (a := x ^ k)
    hxk hx.1 hxδ hcontG
  simp only [show -(γ - 2 * (k : ℝ)) = 2 * (k : ℝ) - γ from by ring] at hamgm
  -- the bound on the last term of the displayed estimate
  have hTle : (1 / 2) * (∫ s in x..δ,
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      ≤ (1 / 2) * (∫ y in Set.Ioc 0 δ,
        y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [intervalIntegral.integral_of_le hxδ]
    exact van_setIntegral_mono_Ioc hx.1 (hB.mono_set (Set.Ioc_subset_Ioc le_rfl hδx.le))
      fun y hy => mul_nonneg (Real.rpow_nonneg (le_of_lt hy.1) _) (sq_nonneg _)
  -- assemble
  have hstep : x ^ k * |iteratedDeriv k f x|
      ≤ x ^ k * |iteratedDeriv k f δ|
        + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
        + (1 / 2) * (∫ s in x..δ,
            s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
    have h1 : x ^ k * |iteratedDeriv k f x|
        ≤ x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|) :=
      mul_le_mul_of_nonneg_left hFx (le_of_lt hxk)
    have h2 : x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|)
        ≤ x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hxk)
      linarith [hamgm]
    have h3 : x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)))
        = x ^ k * |iteratedDeriv k f δ|
          + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
          + (1 / 2) * (∫ s in x..δ,
              s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
      have hkk : x ^ (2 * k) = x ^ k * x ^ k := by
        rw [show 2 * k = k + k by omega, pow_add]
      rw [hkk]
      have hxne : x ^ k ≠ 0 := ne_of_gt hxk
      field_simp
      ring
    linarith [h1, h2, le_of_eq h3]
  have hTsmall : (1 / 2) * (∫ y in Set.Ioc 0 δ,
      y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 8 := by
    linarith
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (le_of_lt hxk)]
  linarith [hstep, hxA, hxC, hTle, hTsmall]

/-- The induction step `j+1 → j` of the downward induction. -/
private lemma van_step (j : ℕ) (hj : 1 ≤ j) {f : ℝ → ℝ} {x₁ : ℝ} (hx₁ : 0 < x₁)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (h : Filter.Tendsto (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hjn : ((j : ℝ) ≠ 0) := by positivity
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the limit hypothesis, in interval form
  have hεj : (0 : ℝ) < ε * (j : ℝ) / 2 := by positivity
  have hev := Metric.tendsto_nhds.mp h (ε * (j : ℝ) / 2) hεj
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (x₁ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδlt₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδx : δ < x₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- the tail bound against the model integral `∫_x^δ t^{-(j+1)}`
  have htail : ∀ x : ℝ, 0 < x → x ≤ δ →
      x ^ j * (∫ s in x..δ, |iteratedDeriv (j + 1) f s|) ≤ ε / 2 := by
    intro x hxpos hxδ
    have hxj : 0 < x ^ j := pow_pos hxpos j
    -- pointwise bound from the limit hypothesis
    have hbd : ∀ t ∈ Set.Icc x δ,
        |iteratedDeriv (j + 1) f t| ≤ (ε * (j : ℝ) / 2) * (t : ℝ) ^ (-((j : ℝ) + 1)) := by
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hxpos ht.1
      have htδ₀ : t ∈ Set.Ioo (0 : ℝ) δ₀ := ⟨htpos, lt_of_le_of_lt ht.2 hδlt₀⟩
      have h1 := hδ₀ htδ₀
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : |iteratedDeriv (j + 1) f t| * (t : ℝ) ^ (j + 1) < ε * (j : ℝ) / 2 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt htpos) (j + 1)),
          mul_comm ((t : ℝ) ^ (j + 1))] at h1
        exact h1
      have h3 := mul_lt_mul_of_pos_right h2 (inv_pos.mpr (pow_pos htpos (j + 1)))
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos htpos (j + 1))), mul_one] at h3
      have hbase : (t : ℝ) ^ ((j : ℝ) + 1) = (t : ℝ) ^ (j + 1) := by
        have hcast : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, Real.rpow_natCast]
      have hpow : (t : ℝ) ^ (-((j : ℝ) + 1)) = ((t : ℝ) ^ (j + 1))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt htpos) ((j : ℝ) + 1), hbase]
      rw [hpow]
      exact h3.le
    have hint1 : IntervalIntegrable (fun s : ℝ => |iteratedDeriv (j + 1) f s|) volume x δ :=
      ((continuousOn_iteratedDeriv_Icc hf (j + 1) hxpos hδx).abs).intervalIntegrable_of_Icc
        (μ := volume) hxδ
    have hcontw : ContinuousOn (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        (Set.Icc x δ) :=
      continuousOn_const.mul (continuousOn_id.rpow_const fun s hs =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hxpos hs.1)))
    have hint2 : IntervalIntegrable (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        volume x δ := hcontw.intervalIntegrable_of_Icc (μ := volume) hxδ
    have hmono := intervalIntegral.integral_mono_on hxδ hint1 hint2 hbd
    rw [intervalIntegral.integral_const_mul] at hmono
    -- evaluate the model integral
    have hnozero : (0 : ℝ) ∉ Set.uIcc x δ := by
      rw [Set.uIcc_of_le hxδ]
      intro hmem
      exact absurd hmem.1 (not_le.mpr hxpos)
    have hne : -((j : ℝ) + 1) ≠ -1 := by
      intro hc
      exact hjn (by linarith)
    have hval : (∫ s in x..δ, s ^ (-((j : ℝ) + 1)))
        = ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) / (j : ℝ) := by
      rw [integral_rpow (Or.inr ⟨hne, hnozero⟩)]
      have hr : (-((j : ℝ) + 1) + 1) = -(j : ℝ) := by ring
      rw [hr]
      ring
    rw [hval] at hmono
    -- multiply by `x ^ j`
    have hxd : x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) ≤ 1 := by
      rw [Real.rpow_neg (le_of_lt hxpos) (j : ℝ), Real.rpow_neg (le_of_lt hδpos) (j : ℝ),
        Real.rpow_natCast, Real.rpow_natCast]
      have hδj : 0 < δ ^ j := pow_pos hδpos j
      have hxinv : x ^ j * (x ^ j)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hxj)
      have hnonneg : 0 ≤ x ^ j * (δ ^ j)⁻¹ := mul_nonneg hxj.le (inv_nonneg.mpr hδj.le)
      nlinarith [hxinv, hnonneg]
    have hstep1 : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
        / (j : ℝ))) ≤ ε / 2 := by
      have hrw : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
          / (j : ℝ))) = (ε / 2) * (x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))) := by
        field_simp
      rw [hrw]
      nlinarith [hxd, hε]
    exact (mul_le_mul_of_nonneg_left hmono hxj.le).trans hstep1
  -- eventually the `δ`-term is small
  have hfin : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ j * |iteratedDeriv j f δ| < ε / 2 := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hh := (hid.pow j).mul_const |iteratedDeriv j f δ|
    have hh' : Filter.Tendsto (fun x : ℝ => x ^ j * |iteratedDeriv j f δ|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [zero_pow (by omega : j ≠ 0)] using hh
    exact Filter.Tendsto.eventually_lt hh' tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hfin] with x hx hxfin
  have hxpos : 0 < x := hx.1
  have hxδ : x ≤ δ := hx.2.le
  have hxj : 0 < x ^ j := pow_pos hxpos j
  have hFTC : iteratedDeriv j f x
      = iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s := by
    have hh := intervalIntegral_iteratedDeriv_succ hf j hxpos hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (j + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (j + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv j f x|
      ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by
    have hh := abs_add_le (iteratedDeriv j f δ) (-(∫ s in x..δ, iteratedDeriv (j + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s|
        ≤ |iteratedDeriv j f δ| + |∫ s in x..δ, iteratedDeriv (j + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using hh
      _ ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by linarith [hI]
  have htail' := htail x hxpos hxδ
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hxj.le]
  linarith [mul_le_mul_of_nonneg_left hFx hxj.le, htail', hxfin]

/-- **Boundary vanishing of the weighted iterated derivatives.**  If `f` is `C^∞` on `(0,x₁]` and
`∫_0^{x₁} x^{2k-γ}(f^{(k+1)}(x))² dx < ∞` with `γ > -1`, then for every `1 ≤ j ≤ k`
`x^j·f^{(j)}(x) → 0` as `x → 0⁺`.

This is the analytic heart of the primitive formula for `∂_x^k(f/x)`.  Route (downward induction on `j`,
starting from `j = k`; the sharp rate is `x^{min(j,(1+γ)/2)}`):

* `f^{(k)}(x) = f^{(k)}(x₁) − ∫_x^{x₁} f^{(k+1)}` (FTC on `(0,x₁]`, and `k ≥ 1` in this case), and
  Cauchy–Schwarz with the two factors `s^{γ/2}` and `s^{k-γ/2}f^{(k+1)}(s)` over `(x,x₁)` gives
  `|∫_x^{x₁} f^{(k+1)}| ≤ B^{1/2}·(∫_x^{x₁} s^{γ-2k} ds)^{1/2}` with `B := ∫_0^{x₁} s^{2k-γ}(f^{(k+1)})²`;
  `x^{2k}∫_x^{x₁}s^{γ-2k}ds → 0` (three cases: `γ-2k ≥ -1`, `= -1` i.e. a log, or `< -1`) gives
  `x^k f^{(k)}(x) → 0`.
* Step: from `t^{j+1} f^{(j+1)}(t) → 0` (limit form, no uniform rate available) deduce `x^j f^{(j)}(x) → 0`:
  `f^{(j)}(x) = f^{(j)}(x₁) − ∫_x^{x₁} f^{(j+1)}`, split `∫_x^{x₁} = ∫_x^δ + ∫_δ^{x₁}` where δ is chosen so
  that `|f^{(j+1)}(t)| ≤ ε t^{-(j+1)}` on `(0,δ)`: then `x^j∫_x^δ t^{-(j+1)}dt ≤ ε/j` and
  `x^j∫_δ^{x₁}|f^{(j+1)}| ≤ x^j·(finite) → 0`.
  (Equivalently: carry the quantitative bound `|f^{(j)}(s)| ≤ C s^{d_j}` with `d_j = min(d_{j+1}+1, 0)`,
  which preserves `j + d_j > 0`.)

The hypothesis `f(x) → 0` at `0⁺` is *not* needed here (only `j ≥ 1` is asked about), and the case
`k = 0` makes the statement vacuous. -/
theorem divSinPrimitiveVanish (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro f hf hB j hj1 hjk
  have key : ∀ n : ℕ, ∀ j : ℕ, k - j ≤ n → 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro n
    induction n with
    | zero =>
      intro j hle hj1 hjk
      have hjk' : j = k := by omega
      subst j
      exact van_baseCase k hj1 hx₁ hγ hf hB
    | succ n ih =>
      intro j hle hj1 hjk
      rcases Nat.lt_or_ge (k - j) (n + 1) with hlt | hge
      · exact ih j (Nat.lt_succ_iff.mp hlt) hj1 hjk
      · exact van_step j hj1 hx₁ hf (ih (j + 1) (by omega) (by omega) (by omega))
  exact key k j (Nat.sub_le k j) hj1 hjk

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.powerHardyBoundary =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology



end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.primitiveDerivData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.H2.DivQ

/-- The `(k+1)`-st derivative of `f` is continuous on the *open* interval `(0,x₁)`, from
`ContDiffOn ℝ ⊤ f (Ioc 0 x₁)` (via `iteratedDerivWithin`). -/
private lemma continuousOn_iteratedDeriv_Ioo_prv (k : ℕ) (x₁ : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) :
    ContinuousOn (iteratedDeriv (k + 1) f) (Set.Ioo 0 x₁) := by
  have hIoo : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 x₁) := hf.mono Set.Ioo_subset_Ioc_self
  have hcW : ContinuousOn (iteratedDerivWithin (k + 1) f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    hIoo.continuousOn_iteratedDerivWithin (by simp) (uniqueDiffOn_Ioo 0 x₁)
  exact hcW.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm)

theorem primitiveDerivData (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Ioc 0 x₁) ∧
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Icc 0 x₁) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) x₁,
        HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
          (t ^ k * iteratedDeriv (k + 1) f t) t) := by
  -- `f` is `C^∞` on the open interval `(0,x₁)`, so `s ↦ s^k·f^{(k+1)}(s)` is continuous there.
  have hc : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Ioo 0 x₁) :=
    continuousOn_iteratedDeriv_Ioo_prv k x₁ f hf
  have hcont : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
    (continuousOn_id.pow k).mul hc
  -- First conjunct: the AM–GM/Cauchy–Schwarz argument of `primIntegrable`.
  have hIoc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x₁) :=
    primIntegrable k γ x₁ hx₁ hγ f hf hint
  -- The same integrability on the closed interval `[0,x₁]` (the two differ by the null set `{0}`).
  have hIcc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Icc 0 x₁) :=
    hIoc.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := x₁)).symm
  refine ⟨hIoc, ?_, ?_⟩
  · -- Second conjunct: continuity of the primitive on `[0,x₁]`.
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := x₁)
      (μ := volume) (f := fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
      (by rwa [Set.uIcc_of_le hx₁.le])
    simpa [Set.uIcc_of_le hx₁.le] using h
  · -- Third conjunct: the fundamental theorem of calculus at an interior point.
    intro t ht
    have ht0 : 0 < t := ht.1
    have htx : t < x₁ := ht.2
    -- `IntervalIntegrable` on `0..t` reduces to `IntegrableOn (Ioc 0 t)`, which is contained in
    -- `Ioc 0 x₁`; the other half of the definition is an empty interval.
    have hII : IntervalIntegrable (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        volume 0 t := by
      refine ⟨hIoc.mono_set (Set.Ioc_subset_Ioc_right htx.le), ?_⟩
      refine MeasureTheory.IntegrableOn.of_measure_zero ?_
      rw [Set.Ioc_eq_empty (not_lt.mpr ht0.le)]
      exact measure_empty
    -- Continuity of the integrand at `t`.
    have hcat : ContinuousAt (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) t :=
      ((continuous_pow k).continuousAt).mul
        (hc.continuousAt (isOpen_Ioo.mem_nhds ⟨ht0, htx⟩))
    -- Local strong measurability, from continuity on a small subinterval of `(0,x₁)`.
    have hsl : StronglyMeasurableAtFilter (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (nhds t) volume := by
      refine ⟨Set.Ioo (t / 2) ((t + x₁) / 2), ?_, ?_⟩
      · exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
      · refine (hcont.mono ?_).aestronglyMeasurable measurableSet_Ioo
        intro y hy
        exact ⟨by linarith [hy.1, ht0], by linarith [hy.2, htx]⟩
    exact intervalIntegral.integral_hasDerivAt_right hII hsl hcat

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.sqIntegral_le_weightedIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set

/-- On `Iθ = [0, π/2]` the weight `sin(2x)^{-η}` dominates `1` pointwise (except at the two
endpoints, which are null): `sin(2x) ∈ (0,1]` for `x ∈ (0,π/2)` and `η ≥ 0`.

Consequently the weighted `L²` integral of `(∂ₓh)²` over the full angular interval dominates
the integral over any initial segment `(0,θ]`, `θ < π/2`. -/
theorem sqIntegral_le_weightedIntegral {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (hint2 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc 0 θ)) :
    (∫ x in (0:ℝ)..θ, (deriv h x) ^ 2)
      ≤ ∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
  have hθ0 : (0 : ℝ) ≤ θ := le_of_lt hθ.1
  have hθ2 : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  -- `(0,θ] ⊆ Iθ = [0,π/2]`
  have hsub : Set.Ioc (0 : ℝ) θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2.trans hθ2⟩
  -- on `(0,θ]` the sine is positive, hence `sin(2x)^{-η} ≥ 1` because `sin(2x) ≤ 1` and `η ≥ 0`
  have hsinpos : ∀ x ∈ Set.Ioc (0 : ℝ) θ, 0 < Real.sin (2 * x) := by
    intro x hx
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hx.1]
    · linarith [hx.2, hθ.2]
  have hw1 : ∀ x ∈ Set.Ioc (0 : ℝ) θ, 1 ≤ (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    intro x hx
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hsinpos x hx) (Real.sin_le_one _) (by
      have heta : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
      linarith)
  have hfg : ∀ x ∈ Set.Ioc (0 : ℝ) θ,
      (deriv h x) ^ 2 ≤ (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    intro x hx
    have h1 := hw1 x hx
    nlinarith [sq_nonneg (deriv h x)]
  -- Step 1: monotonicity of the integral on `(0,θ]` (both sides integrable there).
  have step1 : ∫ x in Set.Ioc (0 : ℝ) θ, (deriv h x) ^ 2
      ≤ ∫ x in Set.Ioc (0 : ℝ) θ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.integral_mono_ae (μ := volume.restrict (Set.Ioc (0 : ℝ) θ)) hint2 ?_ ?_
    · exact hint.mono_set hsub
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact hfg x hx
  -- Step 2: enlarging the set `(0,θ] ↦ Iθ` for a nonnegative integrand.
  have step2 : ∫ x in Set.Ioc (0 : ℝ) θ,
        (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
      ≤ ∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.setIntegral_mono_set (μ := volume) hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Icc)] with x hx
      have hs : 0 ≤ Real.sin (2 * x) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith [hx.1]
        · linarith [hx.2]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
    · filter_upwards with x hx
      exact hsub hx
  rw [intervalIntegral.integral_of_le hθ0]
  exact le_trans step1 step2

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.sqIntervalIntegralLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set

/-- **Cauchy–Schwarz (Bunyakovsky) for the interval integral.**  For `a ≤ b` and `f` with `f`
and `f²` interval-integrable on `[a,b]`,

  `(∫_a^b f)² ≤ (b - a) · ∫_a^b f²`.

The proof rewrites both sides as set integrals over `Ioc a b`
(`intervalIntegral.integral_of_le`), notes that `f` is square integrable there
(`intervalIntegrable_iff_integrableOn_Ioc_of_le` + `memLp_two_iff_integrable_sq`) and that the
constant function `1` is too (`intervalIntegrable_const` + `memLp_two_iff_integrable_sq`), applies
the abstract Cauchy–Schwarz inequality `Work.Spaces.cs_integral` to `u = f`, `v = 1`, and evaluates
`∫ x in a..b, 1 = b - a` with `intervalIntegral.integral_const`. -/
theorem sqIntervalIntegralLe (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) MeasureTheory.volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  have hF1 : Integrable f (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf
  have hF2 : Integrable (fun x : ℝ => f x ^ 2) (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf2
  have hmf : MemLp f 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq hF1.aestronglyMeasurable).mpr hF2
  have hm1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioc a b)) := by
    refine (memLp_two_iff_integrable_sq (f := fun _ : ℝ => (1 : ℝ)) aestronglyMeasurable_const).mpr ?_
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp intervalIntegrable_const
  have h := Work.Spaces.cs_integral hmf hm1
  have e1 : (∫ x in Ioc a b, f x * (fun _ : ℝ => (1 : ℝ)) x) = ∫ x in a..b, f x := by
    rw [← intervalIntegral.integral_of_le hab]
    simp
  have e2 : (∫ x in Ioc a b, f x ^ 2) = ∫ x in a..b, f x ^ 2 := by
    rw [← intervalIntegral.integral_of_le (f := fun x : ℝ => f x ^ 2) hab]
  have e3 : (∫ x in Ioc a b, (fun _ : ℝ => (1 : ℝ)) x ^ 2) = b - a := by
    have hpt : (fun x : ℝ => (fun _ : ℝ => (1 : ℝ)) x ^ 2) = fun _ : ℝ => (1 : ℝ) := by
      funext x
      norm_num
    rw [hpt, ← intervalIntegral.integral_of_le (f := fun _ : ℝ => (1 : ℝ)) hab,
      intervalIntegral.integral_const]
    simp
  rw [e1, e2, e3] at h
  calc (∫ x in a..b, f x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (b - a) := h
    _ = (b - a) * ∫ x in a..b, f x ^ 2 := by ring

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.HardSlotDBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false


/-- The triangle-type bound `|a - b| ≤ |a| + |b|`. -/
private theorem abs_sub_le_abs_add_aux (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  exact ⟨by linarith [le_abs_self a, neg_le_abs b], by linarith [le_abs_self b, neg_le_abs a]⟩




end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.MinLeAvg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.SourceSide.integrableOn_sq_mul_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.H2.ModalSolR.SourceSide

theorem integrableOn_sq_mul_continuousOn {c : ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun z => c z ^ 2) (Set.Ioi 0))
    {a b c₀ d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c₀) (hcd : c₀ ≤ d)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b ×ˢ Set.Icc c₀ d)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => c p.1 ^ 2 * g p)
      (Set.Icc a b ×ˢ Set.Icc c₀ d) := by
  -- `[a,b] ⊆ (0,∞)`, so the hypothesis on `c ^ 2` restricts to `[a,b]`.
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  -- `volume` on `ℝ × ℝ` restricted to the rectangle is the product of the two restrictions.
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Set.Icc c₀ d)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d)) :=
    (Measure.prod_restrict (Set.Icc a b) (Set.Icc c₀ d)).symm
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc c₀ d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact isCompact_Icc.measure_lt_top⟩
  -- `p ↦ c p.1 ^ 2 = d p.1` is integrable on the rectangle (Fubini-trivial), and `g` is
  -- continuous hence bounded there: `IntegrableOn.mul_continuousOn` finishes.
  refine MeasureTheory.IntegrableOn.mul_continuousOn ?_ hg (isCompact_Icc.prod isCompact_Icc)
  rw [MeasureTheory.IntegrableOn, hprod]
  exact (hc2.mono_set hsub).comp_fst _

end Work.FTS.H2.ModalSolR.SourceSide
end
-- ===== merged: Submission.Work.FTS.H2.SliceFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.ZibpUConcl =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
## The convergence of the primitive forces the total integral to vanish

If a function `u` satisfies the finite-increment relation
`u b - u a = ∫_a^b ψ + ∫_a^b gE` for all `0 < a < b`, and both limits of `u`
(at `0⁺` and at `+∞`) are forced to be `0` (the hypotheses `hL0`, `hLinf`),
then the total integral of `ψ + gE` over `[0,∞)` vanishes.

The proof identifies `u` as a primitive of `f = ψ + gE`.  For `0 < a < b` the
splitting `Ioi a = Ioc a b ∪ Ioi b` gives
`u b = (u a + ∫_{Ioi a} f) - ∫_{Ioi b} f`; since the tail integral tends to `0`
along `atTop`, `u` has the limit `u a + ∫_{Ioi a} f` at `+∞`, which is therefore
`0`.  Feeding `u = -∫_{Ioi ·} f` into the limit at `0⁺` (where `∫_{Ioi ε} f`
tends to `∫_{Ioi 0} f`, by the a.e.-cover machinery for `Ioi ε ↑ Ioi 0`)
gives `∫_{Ioi 0} f = 0`, and `{0}` is a null set.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.LocData.FstarAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **The closed form of the `k`-th derivative of the profile** `F_* (z) = 2z/(1+z)²`:

  `Gker k z = 2·(-1)^k·k!·(z - k)/(1+z)^(k+2)`.

For `k = 0` this is `F_*` itself; in general `deriv^[k] F_* = Gker k` off `z = -1`. -/
noncomputable def Gker (k : ℕ) (z : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2)

/-- The action of `D_z = z ∂_z` on a function of `z` alone: `T1F u z = z * deriv u z`. (Renamed from `T1` on 2026-10-10: `LocData.DzIter_bumpZ_bound` declares the same `Work.FTS.LocData.T1`, and the two clashed on import.) -/
noncomputable def T1F (u : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv u z

@[simp] theorem Gker_apply (k : ℕ) (z : ℝ) :
    Gker k z = 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2) := rfl

@[simp] theorem T1_apply (u : ℝ → ℝ) (z : ℝ) : T1F u z = z * deriv u z := rfl


end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.AkRhoJetBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.FTS.NonlinRows.AkRhoJetBasic

/-! ## The radial jet bound for `2z^2/(1+z)^3`

Extracted from `Work.FTS.Nonlinear.Pieces` (where it is `private`) as the standalone
input of the `rak` row: the `D_z^j`-jets (`j <= 4`) of `2z^2/(1+z)^3` weighted by the
Hardy weight `w z = (1+z)^2/z^2` are bounded by `720/(1+z)`. -/

/-- The `j`-th `D_z`-jet of `2z²/(1+z)³` weighted by the Hardy weight `w`. -/
noncomputable def akRho (j : ℕ) (z : ℝ) : ℝ :=
  match j with
  | 0 => 2 / (1 + z)
  | 1 => 2 * (2 - z) / (1 + z) ^ 2
  | 2 => 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 3
  | 3 => 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 4
  | _ => (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 5

def akNum : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 2 else 0
  | 1, i => if i = 0 then 4 else if i = 1 then -2 else 0
  | 2, i => if i = 0 then 8 else if i = 1 then -14 else if i = 2 then 2 else 0
  | 3, i => if i = 0 then 16 else if i = 1 then -66 else if i = 2 then 36
              else if i = 3 then -2 else 0
  | _, i => if i = 0 then 32 else if i = 1 then -262 else if i = 2 then 342
              else if i = 3 then -82 else if i = 4 then 2 else 0

lemma akRho_eq (j : ℕ) (hj : j ≤ 4) (z : ℝ) :
    akRho j z = (∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i) / (1 + z) ^ (j + 1) := by
  interval_cases j <;>
    · simp only [akRho, akNum]
      norm_num [Finset.sum_range_succ]
      try ring

lemma akNum_sum_le (j : ℕ) (hj : j ≤ 4) :
    (∑ i ∈ Finset.range (j + 1), |akNum j i|) ≤ 720 := by
  interval_cases j <;> simp [akNum, Finset.sum_range_succ] <;> norm_num

lemma akRho_abs_le (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 ≤ z) :
    |akRho j z| ≤ 720 / (1 + z) := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h1' : (1 : ℝ) ≤ 1 + z := by linarith
  have hsum : |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i| ≤ 720 * (1 + z) ^ j := by
    calc |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i|
        ≤ ∑ i ∈ Finset.range (j + 1), |akNum j i * z ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), |akNum j i| * (1 + z) ^ j := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h2 : |z| ^ i ≤ (1 + z) ^ i := by
            refine pow_le_pow_left₀ (abs_nonneg z) ?_ i
            rw [abs_of_nonneg hz]; linarith
          have h3 : (1 + z) ^ i ≤ (1 + z) ^ j := pow_le_pow_right₀ h1' (by omega)
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (le_trans h2 h3) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (j + 1), |akNum j i|) * (1 + z) ^ j := by rw [Finset.sum_mul]
      _ ≤ 720 * (1 + z) ^ j := mul_le_mul_of_nonneg_right (akNum_sum_le j hj) (by positivity)
  rw [akRho_eq j hj z, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + z) ^ (j + 1))]
  rw [div_le_div_iff₀ (by positivity) h1]
  calc |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i| * (1 + z)
      ≤ (720 * (1 + z) ^ j) * (1 + z) := mul_le_mul_of_nonneg_right hsum h1.le
    _ = 720 * (1 + z) ^ (j + 1) := by rw [mul_assoc, ← pow_succ]

lemma hasDerivAt_one_add_pow (n : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ n) (n * (1 + z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (1 + z)).comp z
    ((hasDerivAt_const (x := z) 1).add (hasDerivAt_id z))
  simpa [Function.comp_def] using h

lemma hasDerivAt_akPsi {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3)
      (2 * z * (2 - z) / (1 + z) ^ 4) z := by
  have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2) (4 * z) z := by
    have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
    convert h using 1
    push_cast
    ring
  have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 3) (3 * (1 + z) ^ 2) z := by
    simpa using hasDerivAt_one_add_pow 3 z
  have h3 : (1 + z) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (by intro hc; exact hz (by linarith))
  have hd := h1.div h2 h3
  convert hd using 1
  field_simp <;> ring_nf <;> norm_num

lemma akJet1 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 1 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
  have h : (fun z' : ℝ => (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 : ℝ → ℝ → ℝ) z' θ)
      = fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 := rfl
  rw [h, (hasDerivAt_akPsi hz).deriv]
  ring

lemma akJet2 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 2 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 1 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (2 - z') / (1 + z') ^ 4 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet1 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (2 - z') / (1 + z') ^ 4)
      (2 * z * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (2 - z')) (2 * z * (4 - 3 * z)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h' := h.mul ((hasDerivAt_const (x := z) (c := (2 : ℝ))).sub (hasDerivAt_id z))
      convert h' using 1
      · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 4) (4 * (1 + z) ^ 3) z := by
      simpa using hasDerivAt_one_add_pow 4 z
    have h3 : (1 + z) ^ 4 ≠ 0 :=
      pow_ne_zero 4 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

lemma akJet3 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 3 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 2 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4) / (1 + z') ^ 5 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet2 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4) / (1 + z') ^ 5)
      (2 * z * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4))
        (2 * z * (8 - 21 * z + 4 * z ^ 2)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun z' : ℝ => z' ^ 2 - 7 * z' + 4) (2 * z - 7) z := by
        have a := (hasDerivAt_pow 2 z)
        have b := (hasDerivAt_id z).const_mul (7 : ℝ)
        have c := (a.sub b).add_const 4
        convert c using 1
        · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
        · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
      have h' := h.mul h2
      convert h' using 1
      simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      ; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 5) (5 * (1 + z) ^ 4) z := by
      simpa using hasDerivAt_one_add_pow 5 z
    have h3 : (1 + z) ^ 5 ≠ 0 :=
      pow_ne_zero 5 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

lemma akJet4 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 4 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = z ^ 2 * (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 7 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 3 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8) / (1 + z') ^ 6 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet3 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt
      (fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8) / (1 + z') ^ 6)
      (z * (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 7) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8))
        (2 * z * (-5 * z ^ 3 + 72 * z ^ 2 - 99 * z + 16)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun z' : ℝ => -z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8)
          (-3 * z ^ 2 + 36 * z - 33) z := by
        have a := (hasDerivAt_pow 3 z).neg
        have b := (hasDerivAt_pow 2 z).const_mul (18 : ℝ)
        have c := (hasDerivAt_id z).const_mul (33 : ℝ)
        have h' := ((a.add b).sub c).add_const 8
        convert h' using 1
        · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
        · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
      have h' := h.mul h2
      convert h' using 1
      simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      ; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 6) (6 * (1 + z) ^ 5) z := by
      simpa using hasDerivAt_one_add_pow 6 z
    have h3 : (1 + z) ^ 6 ≠ 0 :=
      pow_ne_zero 6 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

lemma akJet_mul_w (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz0 : z ≠ 0) (hz1 : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z
      = akRho j z := by
  have h1z : (1 : ℝ) + z ≠ 0 := by intro hc; exact hz1 (by linarith)
  interval_cases j
  · simp only [akRho, Work.Spaces.DzIter_zero]
    rw [Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet1 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet2 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet3 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet4 hz1 θ, akRho, Work.Spaces.w] <;> try norm_num
    field_simp <;> ring_nf <;> norm_num

lemma akJet_bound (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
      ≤ 720 ^ 2 / (1 + z) ^ 2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z ≠ -1 := by intro hc; linarith
  rw [akJet_mul_w j hj hz0 hz1 θ]
  have h := akRho_abs_le j hj hz.le
  have h2 : akRho j z ^ 2 ≤ (720 / (1 + z)) ^ 2 := by
    have h3 := pow_le_pow_left₀ (abs_nonneg (akRho j z)) h 2
    rwa [sq_abs] at h3
  calc akRho j z ^ 2 ≤ (720 / (1 + z)) ^ 2 := h2
    _ = 720 ^ 2 / (1 + z) ^ 2 := by rw [div_pow]

/-- **The radial jet bound** for the profile `z ↦ 2z^2/(1+z)^3` (the radial factor of
`AK α`), in the form needed by `Work.FTS.LocDataExt.HkIntegrand_sepGam_le`. -/
theorem akRho_jet_bound :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j : ℕ, j ≤ 4 → ∀ {z : ℝ}, 0 < z → ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 :=
  ⟨720 ^ 2, by norm_num, fun j hj z hz θ => akJet_bound j hj hz θ⟩

end Work.FTS.NonlinRows.AkRhoJetBasic
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.mvt_tendsto_of_deriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.notIntegrableOn_Itheta_of_rpow_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The three-term recurrence -/

/-- The recurrence for `gC`, multiplied out by `n+2`:
`(n+2) C_{n+2} = (2n+5) x C_{n+1} - (n+3) C_n`. -/
lemma gC_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * gC (n + 2) x
      = (2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [show gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x * gC (n + 1) x
      - ((n : ℝ) + 3) * gC n x) / ((n : ℝ) + 2)) from rfl]
  field_simp

/-! ## Smoothness -/

lemma contDiff_gC : ∀ n : ℕ, ContDiff ℝ 3 (gC n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
    rw [show gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x * gC (n + 1) x
      - ((n : ℝ) + 3) * gC n x) / ((n : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul ih2).sub (contDiff_const.mul ih1)).div_const _

/-! ## The first and second derivatives of the recurrence -/

/-- First derivative of the recurrence, divided form. -/
lemma gC_rec_deriv_div (n : ℕ) :
    deriv (gC (n + 2)) = fun x => (2 * ((n : ℝ) + 5 / 2) * gC (n + 1) x
      + 2 * ((n : ℝ) + 5 / 2) * x * deriv (gC (n + 1)) x
      - ((n : ℝ) + 3) * deriv (gC n) x) / ((n : ℝ) + 2) := by
  funext x
  have hd1 : DifferentiableAt ℝ (gC (n + 1)) x :=
    ((contDiff_gC (n + 1)).differentiable (by norm_num)).differentiableAt
  have hd0 : DifferentiableAt ℝ (gC n) x :=
    ((contDiff_gC n).differentiable (by norm_num)).differentiableAt
  rw [show gC (n + 2) = (fun y => (2 * ((n : ℝ) + 5 / 2) * y * gC (n + 1) y
      - ((n : ℝ) + 3) * gC n y) / ((n : ℝ) + 2)) from rfl]
  rw [deriv_div_const]
  change (deriv ((fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y * gC (n + 1) y)
      - (fun y : ℝ => ((n : ℝ) + 3) * gC n y)) x) / ((n : ℝ) + 2) = _
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  change (deriv ((fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) * gC (n + 1)) x
      - deriv (fun y : ℝ => ((n : ℝ) + 3) * gC n y) x) / ((n : ℝ) + 2) = _
  rw [deriv_mul (by fun_prop) hd1]
  change (deriv (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) x * gC (n + 1) x
      + (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) x * deriv (gC (n + 1)) x
      - deriv (fun y : ℝ => ((n : ℝ) + 3) * gC n y) x) / ((n : ℝ) + 2) = _
  rw [deriv_const_mul _ hd0]
  rw [show deriv (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) x = 2 * ((n : ℝ) + 5 / 2) from by
    rw [deriv_const_mul_field]; simp]

/-- First derivative of the recurrence, multiplied form. -/
lemma gC_rec_deriv (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * deriv (gC (n + 2)) x = (2 * (n : ℝ) + 5) * gC (n + 1) x
      + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
      - ((n : ℝ) + 3) * deriv (gC n) x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hd := congrFun (gC_rec_deriv_div n) x
  rw [hd]
  field_simp

/-- Second derivative of the recurrence, divided form. -/
lemma gC_rec_deriv2_div (n : ℕ) :
    deriv (deriv (gC (n + 2))) = fun x =>
      (2 * (2 * ((n : ℝ) + 5 / 2)) * deriv (gC (n + 1)) x
        + 2 * ((n : ℝ) + 5 / 2) * x * deriv (deriv (gC (n + 1))) x
        - ((n : ℝ) + 3) * deriv (deriv (gC n)) x) / ((n : ℝ) + 2) := by
  rw [gC_rec_deriv_div n]
  funext x
  have hdd1 : DifferentiableAt ℝ (deriv (gC (n + 1))) x :=
    (((ContDiff.deriv' (n := 2) (contDiff_gC (n + 1)))).differentiable
      (by norm_num)).differentiableAt
  have hdd0 : DifferentiableAt ℝ (deriv (gC n)) x :=
    (((ContDiff.deriv' (n := 2) (contDiff_gC n))).differentiable
      (by norm_num)).differentiableAt
  have hcg : HasDerivAt (gC (n + 1)) (deriv (gC (n + 1)) x) x :=
    (((contDiff_gC (n + 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hlin : HasDerivAt (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y)
      (2 * ((n : ℝ) + 5 / 2)) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * ((n : ℝ) + 5 / 2))
  have h1 : HasDerivAt (fun y : ℝ => (2 * ((n : ℝ) + 5 / 2) * y) * deriv (gC (n + 1)) y)
      (2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x
        + (2 * ((n : ℝ) + 5 / 2) * x) * deriv (deriv (gC (n + 1))) x) x :=
    hlin.mul hdd1.hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * gC (n + 1) y)
      (2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x) x :=
    hcg.const_mul (2 * ((n : ℝ) + 5 / 2))
  have h3 : HasDerivAt (fun y : ℝ => ((n : ℝ) + 3) * deriv (gC n) y)
      (((n : ℝ) + 3) * deriv (deriv (gC n)) x) x :=
    hdd0.hasDerivAt.const_mul ((n : ℝ) + 3)
  have h4 : HasDerivAt (fun y : ℝ =>
      (2 * ((n : ℝ) + 5 / 2) * gC (n + 1) y + (2 * ((n : ℝ) + 5 / 2) * y)
        * deriv (gC (n + 1)) y - ((n : ℝ) + 3) * deriv (gC n) y) / ((n : ℝ) + 2))
      ((2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x
        + (2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x
          + (2 * ((n : ℝ) + 5 / 2) * x) * deriv (deriv (gC (n + 1))) x)
        - ((n : ℝ) + 3) * deriv (deriv (gC n)) x) / ((n : ℝ) + 2)) x :=
    ((h2.add h1).sub h3).div_const _
  rw [h4.deriv]
  ring

/-- Second derivative of the recurrence, multiplied form. -/
lemma gC_rec_deriv2 (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * deriv (deriv (gC (n + 2))) x = 2 * (2 * (n : ℝ) + 5) * deriv (gC (n + 1)) x
      + (2 * (n : ℝ) + 5) * x * deriv (deriv (gC (n + 1))) x
      - ((n : ℝ) + 3) * deriv (deriv (gC n)) x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hd := congrFun (gC_rec_deriv2_div n) x
  rw [hd]
  field_simp

/-! ## The two families of relations -/

/-- The first-order ("ladder") relation `D_k`:
`(1-x²) C_k' + k x C_k - (k+2) C_{k-1}`. -/
def Drel (k : ℕ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * deriv (gC k) x + (k : ℝ) * x * gC k x - ((k : ℝ) + 2) * gC (k - 1) x

/-- The Gegenbauer operator applied to `C_k`:
`(1-x²) C_k'' - 4x C_k' + k(k+3) C_k`. -/
def Mrel (k : ℕ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * deriv (deriv (gC k)) x - 4 * x * deriv (gC k) x
    + (k : ℝ) * ((k : ℝ) + 3) * gC k x

/-- `D_{m+3}` follows from `D_{m+1}`, `D_{m+2}` and the recurrences. -/
lemma Drel_step (m : ℕ) (x : ℝ) (h1 : Drel (m + 1) x = 0) (h2 : Drel (m + 2) x = 0) :
    Drel (m + 3) x = 0 := by
  have hR1 : ((m : ℝ) + 3) * gC (m + 3) x
      = (2 * (m : ℝ) + 7) * x * gC (m + 2) x - ((m : ℝ) + 4) * gC (m + 1) x := by
    have h := gC_rec (m + 1) x
    push_cast at h
    rw [show (m + 1) + 2 = m + 3 from rfl, show (m + 1) + 1 = m + 2 from rfl] at h
    linear_combination h
  have hR1' : ((m : ℝ) + 3) * deriv (gC (m + 3)) x = (2 * (m : ℝ) + 7) * gC (m + 2) x
      + (2 * (m : ℝ) + 7) * x * deriv (gC (m + 2)) x
      - ((m : ℝ) + 4) * deriv (gC (m + 1)) x := by
    have h := gC_rec_deriv (m + 1) x
    push_cast at h
    rw [show (m + 1) + 2 = m + 3 from rfl, show (m + 1) + 1 = m + 2 from rfl] at h
    linear_combination h
  have hR0 : ((m : ℝ) + 2) * gC (m + 2) x
      = (2 * (m : ℝ) + 5) * x * gC (m + 1) x - ((m : ℝ) + 3) * gC m x := gC_rec m x
  have hkey : ((m : ℝ) + 3) * Drel (m + 3) x = 0 := by
    simp only [Drel, show m + 1 - 1 = m from rfl, show m + 2 - 1 = m + 1 from rfl,
      show m + 3 - 1 = m + 2 from rfl] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    linear_combination (1 - x ^ 2) * hR1' + (2 * (m : ℝ) + 7) * x * h2 - ((m : ℝ) + 4) * h1
      - ((m : ℝ) + 4) * hR0 + ((m : ℝ) + 3) * x * hR1
  have hpos : ((m : ℝ) + 3) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hkey).resolve_left hpos

/-- `M_{n+2}` follows from `M_n`, `M_{n+1}`, `D_{n+1}` and the recurrences. -/
lemma Mrel_step (n : ℕ) (x : ℝ) (h1 : Mrel (n + 1) x = 0) (h0 : Mrel n x = 0)
    (hd : Drel (n + 1) x = 0) : Mrel (n + 2) x = 0 := by
  have hA1 := gC_rec n x
  have hA2 := gC_rec_deriv n x
  have hA3 := gC_rec_deriv2 n x
  have hkey2 : ((n : ℝ) + 2) * Mrel (n + 2) x - (2 * (n : ℝ) + 5) * x * Mrel (n + 1) x
      + ((n : ℝ) + 3) * Mrel n x - 2 * (2 * (n : ℝ) + 5) * Drel (n + 1) x = 0 := by
    simp only [Mrel, Drel, show n + 1 - 1 = n from rfl] at h1 h0 hd ⊢
    push_cast at h1 h0 hd ⊢
    linear_combination (1 - x ^ 2) * hA3 - 4 * x * hA2 + ((n : ℝ) + 2) * ((n : ℝ) + 5) * hA1
  have hkey : ((n : ℝ) + 2) * Mrel (n + 2) x = 0 := by
    rw [h1, h0, hd] at hkey2
    simpa using hkey2
  exact (mul_eq_zero.mp hkey).resolve_left (by positivity)

/-! ## The two inductions -/

/-- `D_1`: `(1-x²)·3 + x·3x - 3 = 0`. -/
lemma Drel_one (x : ℝ) : Drel 1 x = 0 := by
  have hd1 : deriv (gC 1) x = 3 := by
    rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
    simp
  simp only [Drel]
  push_cast
  rw [hd1, show gC 1 x = 3 * x from rfl, show gC 0 x = 1 from rfl]
  ring

/-- `D_2`: `(1-x²)·15x + 2x·(15x²-3)/2 - 4·3x = 0`. -/
lemma Drel_two (x : ℝ) : Drel 2 x = 0 := by
  have hd1 : deriv (gC 1) x = 3 := by
    rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
    simp
  have hd0 : deriv (gC 0) x = 0 := by
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  have hd2 : deriv (gC 2) x = 15 * x := by
    have h := congrFun (gC_rec_deriv_div 0) x
    rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl] at h
    rw [h, hd1, hd0]
    simp only [show gC 1 x = 3 * x from rfl]
    norm_num
    ring
  have h2 : gC 2 x = (15 * x ^ 2 - 3) / 2 := by
    simp only [gC]
    norm_num
    ring
  simp only [Drel]
  push_cast
  rw [hd2, h2, show gC 1 x = 3 * x from rfl]
  ring

/-- `Erel m := D_{m+1}`; all of them vanish. -/
def Erel (m : ℕ) (x : ℝ) : ℝ := Drel (m + 1) x

lemma Erel_all : ∀ m : ℕ, ∀ x : ℝ, Erel m x = 0 := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => intro x; exact Drel_one x
  | one => intro x; exact Drel_two x
  | more m ih1 ih2 => intro x; exact Drel_step m x (ih1 x) (ih2 x)

/-- `M_0`: `C_0 = 1` is constant, so everything but the vanishing terms is `0`. -/
lemma Mrel_zero (x : ℝ) : Mrel 0 x = 0 := by
  have hd0 : deriv (gC 0) x = 0 := by
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  have hdd0 : deriv (deriv (gC 0)) x = 0 := by
    rw [show deriv (gC 0) = (fun _ : ℝ => (0 : ℝ)) from by
      rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
      simp]
    simp
  simp only [Mrel]
  push_cast
  rw [hdd0, hd0, show gC 0 x = 1 from rfl]
  ring

/-- `M_1`: `C_1 = 3x` is linear, giving `-12x + 4·3x = 0`. -/
lemma Mrel_one (x : ℝ) : Mrel 1 x = 0 := by
  have hd1 : deriv (gC 1) x = 3 := by
    rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
    simp
  have hdd1 : deriv (deriv (gC 1)) x = 0 := by
    rw [show deriv (gC 1) = (fun _ : ℝ => (3 : ℝ)) from by
      funext y
      rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
      simp]
    simp
  simp only [Mrel]
  push_cast
  rw [hdd1, hd1, show gC 1 x = 3 * x from rfl]
  ring

lemma Mrel_all : ∀ n : ℕ, ∀ x : ℝ, Mrel n x = 0 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro x; exact Mrel_zero x
  | one => intro x; exact Mrel_one x
  | more n ih1 ih2 => intro x; exact Mrel_step n x (ih2 x) (ih1 x) (Erel_all n x)

/-! ## The target -/

theorem gC_ode (n : ℕ) :
    ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.gC n) ∧ ∀ x : ℝ,
      (1 - x ^ 2) * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.gC n)) x
        - 4 * x * deriv (Work.FTS.PhiStar.Gegenbauer.gC n) x
        + (n : ℝ) * ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x = 0 := by
  refine ⟨contDiff_gC n, fun x => ?_⟩
  simpa only [Mrel] using Mrel_all n x

end Work.FTS.PhiStar.Gegenbauer
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CSTools.abs_intervalIntegral_le_abs_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CSTools


end Work.FTS.PhiStar.Honesty.CSTools
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_interval_le_tail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.PhiStar.Honesty.CSTools

/-- If the quadratic `s ↦ A + 2sB + s²C` is nonnegative for every real `s` and `C ≥ 0`, then
`B² ≤ A·C`: for `C > 0` evaluate at `s = -B/C`, and for `C = 0` the quadratic can only stay
nonnegative on both half-lines when `B = 0`. -/
theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s : ℝ, 0 ≤ A + 2 * s * B + s ^ 2 * C) : B ^ 2 ≤ A * C := by
  rcases lt_or_eq_of_le hC with hCpos | hCzero
  · have hCne : C ≠ 0 := ne_of_gt hCpos
    have hkey : A + 2 * (-(B / C)) * B + (-(B / C)) ^ 2 * C = A - B ^ 2 / C := by
      field_simp
      ring
    have h1 := h (-(B / C))
    rw [hkey] at h1
    have h2 : B ^ 2 / C ≤ A := by linarith
    exact (div_le_iff₀ hCpos).mp h2
  · have hC0 : C = 0 := hCzero.symm
    have hB0 : B = 0 := by
      by_contra hne
      have hBne : B ≠ 0 := hne
      have hkey : A + 2 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * C = -1 := by
        rw [hC0]
        field_simp
        ring
      have h1 := h (-(A + 1) / (2 * B))
      rw [hkey] at h1
      linarith
    rw [hB0, hC0]
    norm_num

/-- Cauchy–Schwarz for the Bochner integral of real functions, in the `L²` form used by
`sq_interval_le_tail`. The proof is the discriminant argument applied to the nonnegative
quadratic `s ↦ ∫ t, (f t + s·g t)²`; note that no measurability of `f` or `g` themselves is
required. -/
theorem sq_integral_mul_le {μ : MeasureTheory.Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable (fun t => (f t) ^ 2) μ) (hg : Integrable (fun t => (g t) ^ 2) μ)
    (hfg : Integrable (fun t => f t * g t) μ) :
    (∫ t, f t * g t ∂μ) ^ 2 ≤ (∫ t, (f t) ^ 2 ∂μ) * (∫ t, (g t) ^ 2 ∂μ) := by
  have hquad : ∀ s : ℝ, 0 ≤ (∫ t, (f t) ^ 2 ∂μ) + 2 * s * (∫ t, f t * g t ∂μ)
      + s ^ 2 * (∫ t, (g t) ^ 2 ∂μ) := by
    intro s
    have h1 : Integrable (fun t => 2 * s * (f t * g t)) μ := hfg.const_mul _
    have h2 : Integrable (fun t => s ^ 2 * (g t) ^ 2) μ := hg.const_mul _
    have e1 : ∫ t, (f t + s * g t) ^ 2 ∂μ
        = ∫ t, (f t) ^ 2 + 2 * s * (f t * g t) + s ^ 2 * (g t) ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    have e2 : ∫ t, (f t) ^ 2 + 2 * s * (f t * g t) + s ^ 2 * (g t) ^ 2 ∂μ
        = (∫ t, (f t) ^ 2 + 2 * s * (f t * g t) ∂μ) + (∫ t, s ^ 2 * (g t) ^ 2 ∂μ) :=
      integral_add (f := fun t : ℝ => (f t) ^ 2 + 2 * s * (f t * g t))
        (g := fun t : ℝ => s ^ 2 * (g t) ^ 2) (hf.add h1) h2
    have e3 : ∫ t, (f t) ^ 2 + 2 * s * (f t * g t) ∂μ
        = (∫ t, (f t) ^ 2 ∂μ) + (∫ t, 2 * s * (f t * g t) ∂μ) :=
      integral_add (f := fun t : ℝ => (f t) ^ 2) (g := fun t : ℝ => 2 * s * (f t * g t)) hf h1
    have e4 : (∫ t, 2 * s * (f t * g t) ∂μ) = 2 * s * (∫ t, f t * g t ∂μ) :=
      integral_const_mul (2 * s) (fun t : ℝ => f t * g t)
    have e5 : (∫ t, s ^ 2 * (g t) ^ 2 ∂μ) = s ^ 2 * (∫ t, (g t) ^ 2 ∂μ) :=
      integral_const_mul (s ^ 2) (fun t : ℝ => (g t) ^ 2)
    have hcalc : ∫ t, (f t + s * g t) ^ 2 ∂μ
        = (∫ t, (f t) ^ 2 ∂μ) + 2 * s * (∫ t, f t * g t ∂μ)
          + s ^ 2 * (∫ t, (g t) ^ 2 ∂μ) := by
      linarith [e1, e2, e3, e4, e5]
    have h0 : 0 ≤ ∫ t, (f t + s * g t) ^ 2 ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => sq_nonneg _)
    rw [hcalc] at h0
    exact h0
  exact sq_le_mul_of_quadratic_nonneg
    (integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => sq_nonneg _)) hquad



end Work.FTS.PhiStar.Honesty.CSTools
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_near_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.CSTools


end Work.FTS.PhiStar.Honesty.CSTools
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.DthIter_angular_z_indep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

/-- Every iterate `D_θ^a f` of a function `f z θ = g θ` independent of `z` stays
independent of `z`. -/
theorem DthIter_angular_z_indep_aux (a : ℕ) (g : ℝ → ℝ) (z z' θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
      = Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z' θ := by
  induction a generalizing z z' θ with
  | zero => rfl
  | succ n ih =>
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    congr 1
    congr 1
    funext θ'
    exact ih z z' θ'

theorem DthIter_angular_z_indep (a : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
      = Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) 0 θ :=
  DthIter_angular_z_indep_aux a g z 0 θ

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.DzIter_radial_theta_indep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

/-- The `θ`-variable is a dummy for a function of `z` alone: every `D_z`-iterate of
`fun z _ => Φ z` is independent of `θ`.

`D_z = z ∂_z` and its iterates see only the `z`-variable, so applying `D_z^b` to a function
which does not depend on `θ` again produces a function which does not depend on `θ`.  The
proof is the immediate induction on `b`: at each step `deriv` is applied to the slice
`fun z' => DzIter b (fun z _ => Φ z) z' θ`, which by the induction hypothesis is independent
of `θ`. -/
theorem DzIter_zonly_theta_indep (Φ : ℝ → ℝ) (b : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z θ' := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z' θ)
          = (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z' θ') from
        funext fun z' => ih z']

theorem DzIter_radial_theta_indep (b : ℕ) (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => f z) z 0 :=
  DzIter_zonly_theta_indep f b z θ 0

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.mixed_sep_product =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

/-! ## Splitting a separated product under the mixed operator

If the first factor of a product depends only on `z` and the second only on `θ`,
then the two operators `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` act on their own
factor:

`D_θ^a (F · G) = F · D_θ^a G`   (when `F` is constant in `θ`),
`D_z^b (F · H) = D_z^b F · H`   (when `H` is constant in `z`).

Both are iterated forms of the elementary fact that the derivative of a product
one of whose factors is *constant in the differentiation variable* is the
derivative of the other factor times that constant
(`deriv_const_mul_field` / `deriv_mul_const_field`), and in particular no
smoothness hypothesis at all is needed. -/

/-- `D_θ^a` of a product whose first factor depends only on `z`. -/
private theorem DthIter_mul_z_only (f : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (a : ℕ) :
    Work.Spaces.DthIter a (fun z θ => f z * H z θ)
      = fun z θ => f z * Work.Spaces.DthIter a H z θ := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field (f z)]
      ring

/-- `D_z^b` of a product whose second factor does not depend on `z`. -/
private theorem DzIter_mul_zIndep {Φ : ℝ → ℝ → ℝ} (hΦ : ∀ z z' θ, Φ z θ = Φ z' θ)
    (H : ℝ → ℝ → ℝ) (b : ℕ) :
    Work.Spaces.DzIter b (fun z θ => H z θ * Φ z θ)
      = fun z θ => Work.Spaces.DzIter b H z θ * Φ z θ := by
  induction b with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      have hφc : ∀ z' : ℝ, Φ z' θ = Φ z θ := fun z' => hΦ z' z θ
      have hfun : (fun z' => Work.Spaces.DzIter n H z' θ * Φ z' θ)
          = fun z' => Work.Spaces.DzIter n H z' θ * Φ z θ := by
        funext z'
        rw [hφc z']
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [hfun, deriv_mul_const_field]
      ring

/-- `D_θ^a` preserves independence of `z`. -/
private theorem DthIter_zIndep {G : ℝ → ℝ → ℝ} (hG : ∀ z z' θ, G z θ = G z' θ) (a : ℕ) :
    ∀ z z' θ, Work.Spaces.DthIter a G z θ = Work.Spaces.DthIter a G z' θ := by
  induction a with
  | zero => exact hG
  | succ n ih =>
      intro z z' θ
      rw [Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [show (fun θ' => Work.Spaces.DthIter n G z θ')
            = fun θ' => Work.Spaces.DthIter n G z' θ' from funext fun θ' => ih z z' θ']

theorem mixed_sep_product (b a : ℕ) (f g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun z θ : ℝ => f z * g θ) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ := by
  have hA : Work.Spaces.DthIter a (fun z θ : ℝ => f z * g θ)
      = fun z θ => f z * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ :=
    DthIter_mul_z_only f (fun _ θ : ℝ => g θ) a
  have hΦ : ∀ z z' θ, Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
      = Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z' θ :=
    DthIter_zIndep (fun z z' θ => rfl) a
  have hB : Work.Spaces.DzIter b
        (fun z θ => f z * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ)
      = fun z θ => Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
          * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ :=
    DzIter_mul_zIndep hΦ (fun z _ : ℝ => f z) b
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (fun z θ : ℝ => f z * g θ)) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
  simp only [hA, hB]

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.reflect_hardyLocRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.CptApp

/-- The reflection `φ ↦ b - φ` sends the one-sided neighbourhood `0⁺` to `b⁻`. -/
private lemma tendsto_const_sub_nhdsWithin_right (b : ℝ) :
    Filter.Tendsto (fun φ : ℝ => b - φ) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin b (Set.Iio b)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun φ : ℝ => b - φ) := continuous_const.sub continuous_id
    have hbase : Filter.Tendsto (fun φ : ℝ => b - φ) (nhds (0 : ℝ)) (nhds b) := by
      have h := hcont.tendsto 0
      simpa using h
    exact hbase.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with φ hφ
    simpa using hφ

/-- The weight `sin (2 ·)` is invariant under the reflection `θ = π/2 - φ`. -/
private lemma sin_two_reflect (φ : ℝ) :
    Real.sin (2 * (Real.pi / 2 - φ)) = Real.sin (2 * φ) := by
  rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub]

theorem reflect_hardyLocRight (c θ₁ : ℝ) (hθ : θ₁ < Real.pi / 2) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Ioo θ₁ (Real.pi / 2)))
    (h1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ContDiffOn ℝ 1 (fun φ => u (Real.pi / 2 - φ)) (Set.Ioo 0 (Real.pi / 2 - θ₁)) ∧
    Filter.Tendsto (fun φ => u (Real.pi / 2 - φ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∫⁻ θ in Set.Ioo θ₁ (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = (∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 2 - θ₁),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (-c)
            * ((fun ψ => u (Real.pi / 2 - ψ)) φ) ^ 2)) ∧
    (∫⁻ θ in Set.Ioo θ₁ (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = (∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 2 - θ₁),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (2 - c)
            * (deriv (fun ψ => u (Real.pi / 2 - ψ)) φ) ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the reflected function is `C¹` on the reflected interval
    have hf : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi / 2 - φ)
        (Set.Ioo 0 (Real.pi / 2 - θ₁)) :=
      (contDiffOn_const (c := Real.pi / 2)).sub contDiffOn_id
    have hmaps : Set.MapsTo (fun φ : ℝ => Real.pi / 2 - φ) (Set.Ioo 0 (Real.pi / 2 - θ₁))
        (Set.Ioo θ₁ (Real.pi / 2)) := by
      intro φ hφ
      simp only [Set.mem_Ioo] at hφ ⊢
      constructor <;> linarith [hφ.1, hφ.2, hθ]
    exact hu.comp hf hmaps
  · -- the reflected function still vanishes at the left endpoint
    exact h1.comp (tendsto_const_sub_nhdsWithin_right (Real.pi / 2))
  · -- the weighted `L²` integrals coincide
    have h := Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
      (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)) θ₁ (Real.pi / 2)
    rw [h]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    rw [sin_two_reflect]
  · -- the weighted `L²` integrals of the derivatives coincide
    have h := Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
      (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      θ₁ (Real.pi / 2)
    rw [h]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    have hd : (deriv (fun ψ : ℝ => u (Real.pi / 2 - ψ)) φ) ^ 2
        = (deriv u (Real.pi / 2 - φ)) ^ 2 := by
      rw [deriv_comp_const_sub u (Real.pi / 2) φ]
      ring
    rw [sin_two_reflect, hd]

end Work.FTS.PhiStar.Honesty.CptApp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.cs_limit_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Filter

theorem cs_limit_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {h w : α → ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x)
    (hA : ∀ k, AEStronglyMeasurable (fun x => f k x * w x) μ)
    (hB : AEStronglyMeasurable (fun x => h x / w x) μ)
    (hAint : ∀ k, Integrable (fun x => (f k x * w x) ^ 2) μ)
    (hBint : Integrable (fun x => (h x / w x) ^ 2) μ)
    (hlim : Filter.Tendsto (fun k => ∫ x, (f k x * w x) ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x, f k x * h x ∂μ) Filter.atTop (nhds 0) := by
  -- Off the null set where `w = 0` the two products `f k * h` and `(f k * w) * (h / w)` agree.
  have h_ae : ∀ᵐ x ∂μ, ∀ k, (f k x * w x) * (h x / w x) = f k x * h x := by
    filter_upwards [hwpos] with x hx k
    have hx0 : w x ≠ 0 := ne_of_gt hx
    field_simp
  have h_int_eq : ∀ k, (∫ x, f k x * h x ∂μ)
      = ∫ x, (f k x * w x) * (h x / w x) ∂μ := fun k =>
    integral_congr_ae (h_ae.mono fun _ hx => (hx k).symm)
  -- Cauchy–Schwarz (Hölder with `p = q = 2`).
  have h_bound : ∀ k, |∫ x, f k x * h x ∂μ|
      ≤ Real.sqrt (∫ x, (f k x * w x) ^ 2 ∂μ) * Real.sqrt (∫ x, (h x / w x) ^ 2 ∂μ) := by
    intro k
    rw [h_int_eq k]
    exact Work.Blocks.IMC.cs_integral_mul_le μ (hA k) hB (hAint k) hBint
  -- The dominating sequence tends to zero: the first factor does, the second is constant.
  have h_g : Tendsto (fun k => Real.sqrt (∫ x, (f k x * w x) ^ 2 ∂μ)
      * Real.sqrt (∫ x, (h x / w x) ^ 2 ∂μ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k => Real.sqrt (∫ x, (f k x * w x) ^ 2 ∂μ)) atTop (nhds 0) := by
      have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
      simpa only [Function.comp_def, Real.sqrt_zero] using hcomp
    simpa using h1.mul_const (Real.sqrt (∫ x, (h x / w x) ^ 2 ∂μ))
  exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact h_bound k) h_g

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_mul_rpow_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- AM–GM in the form used below: `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- The elementary power comparison behind the lemma: for `0 < t ≤ 1` and `-2 ≤ r`,
`t ^ r ≤ (t²)⁻¹`. -/
private lemma rpow_le_inv_sq {t r : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hr : -2 ≤ r) :
    t ^ r ≤ (t ^ 2)⁻¹ := by
  calc t ^ r ≤ t ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hr
    _ = (t ^ (2 : ℝ))⁻¹ := Real.rpow_neg ht0.le 2
    _ = (t ^ 2)⁻¹ := by rw [Real.rpow_two]

/-- If `(c t)²/t⁴` is integrable on `(0,1)` then `c t · t^r` is integrable there for every
`r ≥ -2`: on `(0,1)` one has `|c t · t^r| ≤ |c t/t²|`, i.e. `c · t^r` is dominated by the `L²`
function `c/t²`, and `L² ⊆ L¹` on the finite measure space `(0,1)`.  The endpoints `0` and `1`
contribute nothing.  Unlike `integrableOn_mul_rpow`, only a.e.-measurability of `c` is needed:
the dominating function is built from `c` itself, so no continuity of `c` enters. -/
theorem integrableOn_mul_rpow_ae {c : ℝ → ℝ} {r : ℝ} (hr : -2 ≤ r)
    (hc : AEMeasurable c)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Icc 0 1) := by
  -- Work on the open interval first; the endpoints `0` and `1` are null.
  have keyI : MeasureTheory.Integrable (fun t : ℝ => c t * t ^ r)
      (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
    -- An integrable dominating function: `(c t)²/t⁴/2 + 1/2`.
    have hg : MeasureTheory.Integrable
        (fun t : ℝ => ((c t) ^ 2 / t ^ 4) / 2 + 1 / 2)
        (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
      have h1 : MeasureTheory.Integrable (fun t : ℝ => ((c t) ^ 2 / t ^ 4) / 2)
          (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := hint.integrable.div_const 2
      have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ) / 2)
          (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := MeasureTheory.integrable_const _
      exact h1.add h2
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · -- almost everywhere strong measurability: `c` is a.e. measurable, `t ↦ t^r` is
      -- continuous (hence a.e. strongly measurable) on `(0,1)`
      have h1 : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
        (hc.mono_measure MeasureTheory.Measure.restrict_le_self).aestronglyMeasurable
      have h2 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ r)
          (MeasureTheory.volume.restrict (Set.Ioo 0 1)) := by
        have hcont : ContinuousOn (fun t : ℝ => t ^ r) (Set.Ioo 0 1) :=
          fun x hx =>
            (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx.1))).continuousWithinAt
        exact hcont.aestronglyMeasurable measurableSet_Ioo
      exact h1.mul h2
    · -- the pointwise bound on `(0,1)`
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Set.mem_Ioo] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have htnn : 0 ≤ t := ht0.le
      have hpownn : 0 ≤ t ^ r := Real.rpow_nonneg htnn r
      have hle : t ^ r ≤ (t ^ 2)⁻¹ := rpow_le_inv_sq ht0 (le_of_lt ht1) hr
      have hA : |c t| * t ^ r ≤ |c t| * (t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg (c t))
      have hB : |c t| * (t ^ 2)⁻¹ = |c t * (t ^ 2)⁻¹| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
      have hC : |c t * (t ^ 2)⁻¹| ≤ ((c t * (t ^ 2)⁻¹) ^ 2 + 1) / 2 :=
        abs_le_sq_add_one_div_two _
      have hD : (c t * (t ^ 2)⁻¹) ^ 2 = (c t) ^ 2 / t ^ 4 := by
        rw [div_eq_mul_inv, mul_pow, inv_pow]
        rw [show (t ^ 2) ^ 2 = t ^ 4 by ring]
      calc
        ‖c t * t ^ r‖ = |c t| * t ^ r := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpownn]
        _ ≤ |c t| * (t ^ 2)⁻¹ := hA
        _ = |c t * (t ^ 2)⁻¹| := hB
        _ ≤ ((c t * (t ^ 2)⁻¹) ^ 2 + 1) / 2 := hC
        _ = ((c t) ^ 2 / t ^ 4) / 2 + 1 / 2 := by rw [hD]; ring
  have key : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Ioo 0 1) := keyI
  exact MeasureTheory.IntegrableOn.congr_set_ae key
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))).symm

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the `cos θ`-weighted `θ`-slice of `HkMem α 0 F`

At level `0` the `H^k`-integrand collapses to a single square,

    `HkIntegrand α 0 F z θ = (F z θ · w z / sin(2θ)^{η/2})²`,

whose `θ`-integral is honest at every `z ∈ [0,∞)` by `HkMem α 0 F`.  On `Iθ` and away from
the two endpoints `θ = 0, π/2` this square is `(F z θ)² · w z² · sin(2θ)^{-η}`, and
`cos θ · sin(2θ)^{η}` is bounded by `1` there.  Hence

    `(F z θ)² · cos θ = HkIntegrand α 0 F z θ · (cos θ · sin(2θ)^η / w z²)`

holds almost everywhere on `Iθ` for `z > 0`, with a multiplier bounded by the constant
`1 / w z²`; multiplying an integrable function by such a multiplier preserves integrability.

The two endpoints `{0, π/2}` (where `sin(2θ) = 0` and the identity above fails) are a null set,
which is the only source of the "almost everywhere" caveat.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

theorem integrableOn_sq_cos_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ := by
  classical
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  -- The `H^k`-slice at `z` is honest (this is the only content of `HkMem α 0 F` that is used).
  have hB : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 F z θ) Work.Spaces.Iθ :=
    hF.1 z hzIz
  -- The bounded multiplier `cos θ · sin(2θ)^η / w z²`.
  set c : ℝ → ℝ := fun θ => Real.cos θ * (Real.sin (2 * θ)) ^ Work.Spaces.eta
      / (Work.Spaces.w z) ^ 2 with hcdef
  have hcont_c : Continuous c := by
    rw [hcdef]
    have h1 : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun _ => Or.inr Work.Spaces.eta_nonneg)
    exact (Real.continuous_cos.mul h1).div_const _
  have hc_aesm : AEStronglyMeasurable c (volume.restrict Work.Spaces.Iθ) :=
    hcont_c.aestronglyMeasurable
  -- **Pointwise identity** on `Iθ` away from the endpoints.
  have key : ∀ θ, θ ∈ Work.Spaces.Iθ → Real.sin (2 * θ) ≠ 0 →
      (F z θ) ^ 2 * Real.cos θ = Work.Spaces.HkIntegrand α 0 F z θ * c θ := by
    intro θ hθI hsinθ
    have hsp : 0 < Real.sin (2 * θ) :=
      lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
        (by linarith [hθI.2, Real.pi_pos])) (Ne.symm hsinθ)
    rw [hcdef]
    rw [show Work.Spaces.HkIntegrand α 0 F z θ
        = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by
          simp [Work.Spaces.HkIntegrand]]
    -- `(sin(2θ)^{η/2})² = sin(2θ)^η`
    have hqssq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add hsp]
      congr 1
      rw [Work.Spaces.eta]; ring
    rw [mul_pow, div_pow, hqssq]
    have hse : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hsp _)
    have hwne : Work.Spaces.w z ≠ 0 := ne_of_gt hwpos
    field_simp
  -- The endpoint set where `sin(2θ)` vanishes is contained in `{0, π/2}`.
  have hsub : {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0} ⊆
      ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    obtain ⟨hθI, hθ0⟩ := hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h0, hpi⟩ := hcon
    have hθpos : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm h0)
    have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 hpi
    have h1 : 0 < 2 * θ := by linarith
    have h2 : 2 * θ < Real.pi := by linarith [Real.pi_pos]
    have h3 := Real.sin_pos_of_pos_of_lt_pi h1 h2
    rw [hθ0] at h3
    exact lt_irrefl 0 h3
  have hnull : volume {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) = 0} = 0 := by
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  -- Hence `sin(2θ) ≠ 0` almost everywhere on `Iθ`.
  have hsin : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), Real.sin (2 * θ) ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : ℝ | ¬ Real.sin (2 * a) ≠ 0} = {a : ℝ | Real.sin (2 * a) = 0} := by
      ext a; simp
    rw [hset]
    rw [MeasureTheory.Measure.restrict_apply
      (by measurability : MeasurableSet {a : ℝ | Real.sin (2 * a) = 0})]
    refine measure_mono_null ?_ hnull
    intro θ hθ
    exact ⟨hθ.2, hθ.1⟩
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      θ ∈ Work.Spaces.Iθ ∧ Real.sin (2 * θ) ≠ 0 :=
    (ae_restrict_mem hIθ).and hsin
  -- The two functions agree almost everywhere on `Iθ`.
  have hfun : (fun θ : ℝ => (F z θ) ^ 2 * Real.cos θ) =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 0 F z θ * c θ) := by
    filter_upwards [hae] with θ hθ
    exact key θ hθ.1 hθ.2
  -- `HkIntegrand · c` is integrable: `|c|` is bounded by the constant `(w z²)⁻¹` on `Iθ`.
  have hInt : Integrable (fun θ => Work.Spaces.HkIntegrand α 0 F z θ * c θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.mono' ((hB.norm).const_mul (((Work.Spaces.w z) ^ 2)⁻¹)) ?_ ?_
    · exact hB.aestronglyMeasurable.mul hc_aesm
    · filter_upwards [hae] with θ hθ
      obtain ⟨hθI, hsinθ⟩ := hθ
      have hsp : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
          (by linarith [hθI.2, Real.pi_pos])) (Ne.symm hsinθ)
      rw [norm_mul]
      have hcn : ‖c θ‖ ≤ ((Work.Spaces.w z) ^ 2)⁻¹ := by
        rw [hcdef]
        simp only
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hwpos 2)]
        rw [div_le_iff₀ (pow_pos hwpos 2), inv_mul_cancel₀ (ne_of_gt (pow_pos hwpos 2))]
        rw [abs_mul]
        have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
        have h2 : |(Real.sin (2 * θ)) ^ Work.Spaces.eta| ≤ 1 := by
          rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsp) _)]
          exact Real.rpow_le_one (le_of_lt hsp) (Real.sin_le_one _) Work.Spaces.eta_nonneg
        simpa using mul_le_mul h1 h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      calc ‖Work.Spaces.HkIntegrand α 0 F z θ‖ * ‖c θ‖
          ≤ ‖Work.Spaces.HkIntegrand α 0 F z θ‖ * ((Work.Spaces.w z) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hcn (norm_nonneg _)
        _ = ((Work.Spaces.w z) ^ 2)⁻¹ * ‖Work.Spaces.HkIntegrand α 0 F z θ‖ := by ring
  exact hInt.congr hfun.symm

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_mul_rpow_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- On `(0,1]` the weight `t ^ r` is dominated by `t ^ (-4)` whenever `r ≥ -4`; hence
`(c t)^2 * t ^ r` is controlled by the integrand `(c t)^2 / t^4` and is integrable on
`Icc 0 1` (the endpoints form a null set).  Only a.e.-measurability of `c` is needed. -/
theorem integrableOn_sq_mul_rpow_ae {c : ℝ → ℝ} {r : ℝ} (hr : -4 ≤ r)
    (hc : AEMeasurable c)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ r) (Set.Icc 0 1) := by
  have hmono : Integrable (fun t : ℝ => (c t) ^ 2 * t ^ r) (volume.restrict (Ioo 0 1)) := by
    refine Integrable.mono' hint.norm ?_ ?_
    · have h1 : AEStronglyMeasurable c (volume.restrict (Ioo 0 1)) :=
        (hc.mono_measure Measure.restrict_le_self).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ r) (volume.restrict (Ioo 0 1)) :=
        (ContinuousOn.rpow_const continuousOn_id
          (fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable measurableSet_Ioo
      exact (h1.pow 2).mul h2
    · rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2.le
      have hpow : t ^ r ≤ (t ^ (4:ℕ))⁻¹ := by
        have h := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hr
        rw [Real.rpow_neg (le_of_lt ht0)] at h
        simpa using h
      have h4 : (0:ℝ) < t^4 := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le r)),
        abs_of_nonneg (div_nonneg (sq_nonneg _) h4.le), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  rw [MeasureTheory.IntegrableOn,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0:ℝ)) (b := 1))]
  exact hmono

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_mul_w_sq_of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Topology

theorem integrableOn_sq_mul_w_sq_of {u : ℝ → ℝ}
    (h1 : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (h2 : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) := by
  have hw : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    intro z
    unfold Work.Spaces.w
    rw [div_pow, show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring,
      show (z ^ 2) ^ 2 = z ^ 4 by ring]
  -- **Near `0`**: `(1+z)⁴ ≤ 16` on `(0,1)`, so the weight is a bounded multiple of `1/z⁴`.
  have hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioo (0 : ℝ) 1) := by
    have hbdd : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ‖(fun z : ℝ => (1 + z) ^ 4) z‖ ≤ 16 := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine ae_of_all _ fun z hz => ?_
      have h0 : (0 : ℝ) ≤ 1 + z := by linarith [hz.1]
      have h2' : 1 + z ≤ 2 := by linarith [hz.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h2' 4
        _ = 16 := by norm_num
    have hmeas : AEStronglyMeasurable (fun z : ℝ => (1 + z) ^ 4)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      ((continuous_const.add continuous_id).pow 4).continuousOn.aestronglyMeasurable
        measurableSet_Ioo
    have h := Integrable.bdd_mul h1 hmeas hbdd
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioo
    intro z _
    show (1 + z) ^ 4 * ((u z) ^ 2 / z ^ 4) = (u z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [hw z]; ring
  -- **Far `∞`**: `(1+z)⁴/z⁴ ≤ 16` on `(1,∞)`, so the weight is a bounded factor.
  have hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi (1 : ℝ)) := by
    have hw2 : ∀ z : ℝ, 1 < z → (Work.Spaces.w z) ^ 2 ≤ 16 := by
      intro z hz
      rw [hw z, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 4)]
      have h0 : (0 : ℝ) ≤ 1 + z := by linarith
      have hle : 1 + z ≤ 2 * z := by linarith
      calc (1 + z) ^ 4 ≤ (2 * z) ^ 4 := pow_le_pow_left₀ h0 hle 4
        _ = 16 * z ^ 4 := by ring
    have hbdd : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖(fun z : ℝ => (Work.Spaces.w z) ^ 2) z‖ ≤ 16 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact ae_of_all _ fun z hz => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hw2 z hz
    have hcontw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (1 : ℝ)) := by
      unfold Work.Spaces.w
      refine ContinuousOn.div ?_ ?_ ?_
      · exact ((continuous_const.add continuous_id).pow 2).continuousOn
      · exact (continuous_id.pow 2).continuousOn
      · intro z hz
        exact pow_ne_zero 2 (ne_of_gt (lt_trans one_pos hz))
    have hmeas : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (volume.restrict (Set.Ioi (1 : ℝ))) := (hcontw.pow 2).aestronglyMeasurable measurableSet_Ioi
    have h := Integrable.bdd_mul h2 hmeas hbdd
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro z _
    show (Work.Spaces.w z) ^ 2 * (u z) ^ 2 = (u z) ^ 2 * (Work.Spaces.w z) ^ 2
    ring
  -- **Glue** `(0,1)` and `(1,∞)` across the null set `{1}`.
  have hA : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    hnear.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ici (1 : ℝ)) :=
    hfar.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨ha, _⟩ | h3) <;> linarith
    · intro hx
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨hx, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integral_sq_eq_of_difference =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem integral_sq_eq_of_difference (n : ℕ) {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcross : MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2) (Set.Ioi 0)) :
    ∫ t in Set.Ioi 0, (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2
      = (∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        + 2 * (∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
        + ∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
  -- Pointwise, `(c_ n t)² = (c_ n t - c t)² + 2 (c_ n t - c t) c t + (c t)²`.
  have hcongr : (fun t : ℝ => (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun t : ℝ => ((c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
          + (2 * ((c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
            + (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) :=
    Filter.Eventually.of_forall (fun t => by ring)
  rw [MeasureTheory.integral_congr_ae hcongr]
  have h23 : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * ((c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
        + (c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) := (hcross.const_mul 2).add hcw
  rw [MeasureTheory.integral_add hint h23]
  rw [MeasureTheory.integral_add (hcross.const_mul 2) hcw]
  rw [MeasureTheory.integral_const_mul]
  ring

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.intervalIntegral_weight_mul_sqrt_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- Elementary bridge between the square root and the real power: for `x ≥ 0`,
`√(x³) = x^{3/2}`. -/
private lemma sqrt_cube_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ (3 : ℕ)) = x ^ ((3 : ℝ) / 2) := by
  have h : x ^ (3 : ℕ) = (x ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) := by
    rw [show x ^ (3 : ℕ) = x ^ (3 : ℝ) from (Real.rpow_natCast x 3).symm,
      show (x ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = (x ^ ((3 : ℝ) / 2)) ^ (2 : ℝ) from
        (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hx (3 / 2) 2]
    norm_num
  exact (Real.sqrt_eq_iff_eq_sq (pow_nonneg hx 3) (Real.rpow_nonneg hx _)).mpr h

/-- Weighted Cauchy–Schwarz on an interval: for `0 < y ≤ x` and `A ≥ 0` with `√A` and `A`
interval integrable on `[y, x]`,
`∫_y^x (t/(1+t)²)·√(A t) ≤ x^{3/2}·√(∫_y^x A t)`.

The weight satisfies `0 ≤ t/(1+t)² ≤ x` and hence `∫_y^x (t/(1+t)²)² ≤ x³`, so the claim
follows from Cauchy–Schwarz. -/
theorem intervalIntegral_weight_mul_sqrt_le {A : ℝ → ℝ} {x y : ℝ}
    (hy : 0 < y) (hyx : y ≤ x) (hAnn : ∀ t, 0 ≤ A t)
    (hAint : IntervalIntegrable A MeasureTheory.volume y x)
    (hsqrtint : IntervalIntegrable (fun t : ℝ => Real.sqrt (A t)) MeasureTheory.volume y x) :
    (∫ t in y..x, (t / (1 + t) ^ 2) * Real.sqrt (A t))
      ≤ x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, A t) := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  set w : ℝ → ℝ := fun t => t / (1 + t) ^ 2 with hw
  have hwcont : ContinuousOn w (Set.uIcc y x) := by
    rw [hw, Set.uIcc_of_le hyx]
    refine ContinuousOn.div continuous_id.continuousOn ?_ ?_
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · intro t ht
      exact pow_ne_zero 2 (by linarith [ht.1, hy] : (1 : ℝ) + t ≠ 0)
  have hw2 : IntervalIntegrable (fun t : ℝ => w t ^ 2) MeasureTheory.volume y x :=
    (hwcont.pow 2).intervalIntegrable
  have hAsq : (fun t : ℝ => (Real.sqrt (A t)) ^ 2) = A := by
    funext t
    exact Real.sq_sqrt (hAnn t)
  have hg2 : IntervalIntegrable (fun t : ℝ => (Real.sqrt (A t)) ^ 2) MeasureTheory.volume y x := by
    rw [hAsq]
    exact hAint
  have hprod : IntervalIntegrable (fun t : ℝ => w t * Real.sqrt (A t)) MeasureTheory.volume y x :=
    hsqrtint.continuousOn_mul hwcont
  have hF0 : 0 ≤ ∫ t in y..x, w t * Real.sqrt (A t) := by
    apply intervalIntegral.integral_nonneg hyx
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_of_lt hy) ht.1
    have hwt : 0 ≤ w t := by
      rw [hw]
      exact div_nonneg ht0 (by positivity)
    exact mul_nonneg hwt (Real.sqrt_nonneg (A t))
  have hJ0 : 0 ≤ ∫ t in y..x, A t :=
    intervalIntegral.integral_nonneg hyx (fun t _ => hAnn t)
  have hK0 : 0 ≤ ∫ t in y..x, w t ^ 2 := by
    apply intervalIntegral.integral_nonneg hyx
    intro t _
    positivity
  have hpt : ∀ t ∈ Set.Icc y x, w t ^ 2 ≤ x ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_of_lt hy) ht.1
    have hden : (0 : ℝ) < (1 + t) ^ 2 := by
      have : (0 : ℝ) < 1 + t := by linarith
      positivity
    have h1 : (1 : ℝ) ≤ (1 + t) ^ 2 := by
      have hlt : (1 : ℝ) ≤ 1 + t := by linarith
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ (1 + t) ^ 2 := pow_le_pow_left₀ (by norm_num) hlt 2
    have hw0 : 0 ≤ w t := by rw [hw]; exact div_nonneg ht0 (le_of_lt hden)
    have hwt : w t ≤ t := by
      rw [hw, div_le_iff₀ hden]
      nlinarith [ht0, h1]
    exact pow_le_pow_left₀ hw0 (le_trans hwt ht.2) 2
  have hKi : (∫ t in y..x, w t ^ 2) ≤ x ^ (3 : ℕ) := by
    have hx2int : IntervalIntegrable (fun _ : ℝ => x ^ 2) MeasureTheory.volume y x :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hyx hw2 hx2int hpt
    have hconst : (∫ t in y..x, (fun _ : ℝ => x ^ 2) t) = x ^ 2 * (x - y) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hconst] at hmono
    have hfin : x ^ 2 * (x - y) ≤ x ^ (3 : ℕ) := by
      have h1 : x ^ 2 * (x - y) ≤ x ^ 2 * x :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg x)
      have h2 : x ^ 2 * x = x ^ (3 : ℕ) := by ring
      linarith
    linarith
  have hcs := sq_intervalIntegral_mul_le (f := w) (g := fun t : ℝ => Real.sqrt (A t))
    hyx hw2 hg2 hprod
  simp only [hAsq] at hcs
  have hmain : (∫ t in y..x, w t * Real.sqrt (A t))
      ≤ x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, A t) := by
    calc (∫ t in y..x, w t * Real.sqrt (A t))
        = Real.sqrt ((∫ t in y..x, w t * Real.sqrt (A t)) ^ 2) := (Real.sqrt_sq hF0).symm
      _ ≤ Real.sqrt ((∫ t in y..x, w t ^ 2) * (∫ t in y..x, A t)) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (∫ t in y..x, w t ^ 2) * Real.sqrt (∫ t in y..x, A t) :=
          Real.sqrt_mul hK0 _
      _ ≤ Real.sqrt (x ^ (3 : ℕ)) * Real.sqrt (∫ t in y..x, A t) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hKi) (Real.sqrt_nonneg _)
      _ = x ^ ((3 : ℝ) / 2) * Real.sqrt (∫ t in y..x, A t) := by
          rw [sqrt_cube_eq_rpow (le_of_lt hx)]
  simpa [hw] using hmain

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.lintegral_Ioo_tail_swap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

-- Intended file: Submission/Work/FTS/PhiStar/Honesty/lintegral_Ioo_tail_swap.lean
-- Intended namespace: Work.FTS.PhiStar.Honesty (like its sibling lintegral_Ioo_triangle).
-- Adapt the PROVED sibling Submission/Work/FTS/PhiStar/Honesty/lintegral_Ioo_triangle.lean
-- (`Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle`), whose inner variable runs over `(0,z)`;
-- here it runs over `(z,∞)` and the outer variable over `(0,1)`.
open MeasureTheory Set Filter

/-- `AEMeasurable` on a restricted measure upgrades to `AEMeasurable` of the indicator. -/
private lemma aemeasurable_indicator_of_restrict_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {f : α → ENNReal}
    (h : AEMeasurable f (μ.restrict s)) : AEMeasurable (s.indicator f) μ := by
  obtain ⟨g, hg, hfg⟩ := h
  exact ⟨s.indicator g, hg.indicator hs, (ae_eq_restrict_iff_indicator_ae_eq hs).mp hfg⟩

/-- Tail triangle, first key pointwise identity: for `0 < z`, the step function `1_{z<t}` times
the `(0,∞)`-indicator of `G` is the `(z,∞)`-indicator of `G` (the constraint `t > 0` is
automatic from `t > z > 0`). -/
private lemma tail_swap_step_left {z : ℝ} (hz : 0 < z) (G : ℝ → ENNReal) (t : ℝ) :
    (if z < t then (1 : ENNReal) else 0) * (Set.Ioi (0 : ℝ)).indicator G t
      = (Set.Ioi z).indicator G t := by
  by_cases h : z < t
  · have h0 : t ∈ Set.Ioi (0 : ℝ) := lt_trans hz h
    have h1 : t ∈ Set.Ioi z := h
    rw [ite_eq_left h, one_mul, Set.indicator_of_mem h0, Set.indicator_of_mem h1]
  · have h1 : t ∉ Set.Ioi z := h
    rw [ite_eq_right h, zero_mul, Set.indicator_of_notMem h1]

/-- Tail triangle, second key pointwise identity: the `(0,1)`-indicator of `F` times the step
`1_{z<t}` is the indicator of the truncated `(0,1) ∩ (0,t)`. -/
private lemma tail_swap_step_right (F : ℝ → ENNReal) (t z : ℝ) :
    (Set.Ioo (0 : ℝ) 1).indicator F z * (if z < t then (1 : ENNReal) else 0)
      = (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t).indicator F z := by
  by_cases h : z ∈ Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t
  · have hz1 : z ∈ Set.Ioo (0 : ℝ) 1 := (Set.mem_inter_iff z _ _).mp h |>.1
    have hz2 : z < t := Set.mem_Iio.mp ((Set.mem_inter_iff z _ _).mp h).2
    rw [Set.indicator_of_mem hz1, ite_eq_left hz2, mul_one, Set.indicator_of_mem h]
  · by_cases h2 : z < t
    · have hnot : z ∉ Set.Ioo (0 : ℝ) 1 :=
        fun hz1 => h ((Set.mem_inter_iff z _ _).mpr ⟨hz1, Set.mem_Iio.mpr h2⟩)
      rw [Set.indicator_of_notMem hnot, ite_eq_left h2, mul_one, Set.indicator_of_notMem h]
    · have h2' : ¬ z < t := h2
      rw [ite_eq_right h2', mul_zero, Set.indicator_of_notMem h]

/-- Tail triangle, third key pointwise identity: on `t > 0`, the `(0,∞)`-indicator of `G` times
an arbitrary factor agrees with the `(0,∞)`-indicator of the product `G t * ·`. -/
private lemma tail_swap_step_out (G : ℝ → ENNReal) (X : ℝ → ENNReal) (t : ℝ) :
    X t * (Set.Ioi (0 : ℝ)).indicator G t
      = (Set.Ioi (0 : ℝ)).indicator (fun t => G t * X t) t := by
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · have hG : (Set.Ioi (0 : ℝ)).indicator G t = G t := Set.indicator_of_mem ht G
    have hR : (Set.Ioi (0 : ℝ)).indicator (fun t => G t * X t) t = G t * X t :=
      Set.indicator_of_mem ht _
    rw [hG, hR, mul_comm]
  · have hG : (Set.Ioi (0 : ℝ)).indicator G t = 0 := Set.indicator_of_notMem ht G
    have hR : (Set.Ioi (0 : ℝ)).indicator (fun t => G t * X t) t = 0 :=
      Set.indicator_of_notMem ht _
    rw [hG, hR, mul_zero]

/-- Tonelli for the "tail triangle" `{(z,t) : 0 < z < 1, z < t}`: the iterated integral over
`z ∈ (0,1)`, `t ∈ (z,∞)` equals the iterated integral over `t > 0`, `z ∈ (0,1) ∩ (0,t)`. -/
theorem lintegral_Ioo_tail_swap {F G : ℝ → ENNReal}
    (hF : AEMeasurable F (MeasureTheory.volume.restrict (Set.Ioo 0 1)))
    (hG : AEMeasurable G (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∫⁻ z in Set.Ioo (0 : ℝ) 1, F z * ∫⁻ t in Set.Ioi z, G t)
      = ∫⁻ t in Set.Ioi (0 : ℝ), G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z) := by
  have hs : MeasurableSet (Set.Ioo (0 : ℝ) 1) := measurableSet_Ioo
  have ht0 : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  have hA : AEMeasurable (fun z : ℝ => (Set.Ioo (0 : ℝ) 1).indicator F z) volume :=
    aemeasurable_indicator_of_restrict_tail hs hF
  have hB : AEMeasurable (fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator G t) volume :=
    aemeasurable_indicator_of_restrict_tail ht0 hG
  have hstep : Measurable
      (fun p : ℝ × ℝ => (if p.1 < p.2 then (1 : ENNReal) else 0)) :=
    Measurable.ite (isOpen_lt continuous_fst continuous_snd).measurableSet measurable_const
      measurable_const
  have hstepz : ∀ z : ℝ, Measurable (fun t : ℝ => (if z < t then (1 : ENNReal) else 0)) :=
    fun z => Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hstept : ∀ t : ℝ, Measurable (fun z : ℝ => (if z < t then (1 : ENNReal) else 0)) :=
    fun t => Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hA' : AEMeasurable (fun p : ℝ × ℝ => (Set.Ioo (0 : ℝ) 1).indicator F p.1)
      (volume.prod volume) := hA.comp_fst
  have hB' : AEMeasurable (fun p : ℝ × ℝ => (Set.Ioi (0 : ℝ)).indicator G p.2)
      (volume.prod volume) := hB.comp_snd
  set Ψ : ℝ → ℝ → ENNReal := fun z t =>
    (Set.Ioo (0 : ℝ) 1).indicator F z
      * ((if z < t then (1 : ENNReal) else 0) * (Set.Ioi (0 : ℝ)).indicator G t) with hΨ
  have hAE : AEMeasurable (Function.uncurry Ψ) (volume.prod volume) := by
    rw [hΨ]
    exact AEMeasurable.mul hA' (hstep.aemeasurable.mul hB')
  have h1 : (∫⁻ z, ∫⁻ t, Ψ z t)
      = ∫⁻ z in Set.Ioo (0 : ℝ) 1, F z * ∫⁻ t in Set.Ioi z, G t := by
    have hpt : ∀ z : ℝ,
        ∫⁻ t, Ψ z t
          = (Set.Ioo (0 : ℝ) 1).indicator (fun z => F z * ∫⁻ t in Set.Ioi z, G t) z := by
      intro z
      by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
      · have hz0 : 0 < z := hz.1
        have hinner : AEMeasurable
            (fun t : ℝ => (if z < t then (1 : ENNReal) else 0)
              * (Set.Ioi (0 : ℝ)).indicator G t) volume :=
          (hstepz z).aemeasurable.mul hB
        calc ∫⁻ t, Ψ z t
            = (Set.Ioo (0 : ℝ) 1).indicator F z *
                ∫⁻ t, (if z < t then (1 : ENNReal) else 0)
                  * (Set.Ioi (0 : ℝ)).indicator G t := by
                simp only [hΨ]
                exact lintegral_const_mul'' _ hinner
          _ = (Set.Ioo (0 : ℝ) 1).indicator F z * ∫⁻ t, (Set.Ioi z).indicator G t := by
                congr 1
                exact lintegral_congr (fun t => tail_swap_step_left hz0 G t)
          _ = (Set.Ioo (0 : ℝ) 1).indicator F z * ∫⁻ t in Set.Ioi z, G t := by
                rw [lintegral_indicator measurableSet_Ioi G]
          _ = F z * ∫⁻ t in Set.Ioi z, G t := by rw [indicator_of_mem hz F]
          _ = (Set.Ioo (0 : ℝ) 1).indicator (fun z => F z * ∫⁻ t in Set.Ioi z, G t) z := by
                rw [indicator_of_mem hz]
      · have hzF : (Set.Ioo (0 : ℝ) 1).indicator F z = 0 := indicator_of_notMem hz F
        rw [indicator_of_notMem hz]
        simp only [hΨ, hzF, zero_mul, lintegral_zero]
    calc ∫⁻ z, ∫⁻ t, Ψ z t
        = ∫⁻ z, (Set.Ioo (0 : ℝ) 1).indicator (fun z => F z * ∫⁻ t in Set.Ioi z, G t) z :=
          lintegral_congr hpt
      _ = ∫⁻ z in Set.Ioo (0 : ℝ) 1, F z * ∫⁻ t in Set.Ioi z, G t := by
          rw [lintegral_indicator measurableSet_Ioo
            (fun z => F z * ∫⁻ t in Set.Ioi z, G t)]
  have h2 : (∫⁻ t, ∫⁻ z, Ψ z t)
      = ∫⁻ t in Set.Ioi (0 : ℝ), G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z) := by
    have hpt : ∀ t : ℝ,
        ∫⁻ z, Ψ z t
          = (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)
              * (Set.Ioi (0 : ℝ)).indicator G t := by
      intro t
      have hinner : AEMeasurable
          (fun z : ℝ => (Set.Ioo (0 : ℝ) 1).indicator F z
            * (if z < t then (1 : ENNReal) else 0)) volume :=
        hA.mul (hstept t).aemeasurable
      calc ∫⁻ z, Ψ z t
          = ∫⁻ z, ((Set.Ioo (0 : ℝ) 1).indicator F z * (if z < t then (1 : ENNReal) else 0))
              * (Set.Ioi (0 : ℝ)).indicator G t := by
              apply lintegral_congr
              intro z
              simp only [hΨ]
              exact (mul_assoc _ _ _).symm
        _ = (∫⁻ z, (Set.Ioo (0 : ℝ) 1).indicator F z * (if z < t then (1 : ENNReal) else 0))
              * (Set.Ioi (0 : ℝ)).indicator G t :=
              lintegral_mul_const'' _ hinner
        _ = (∫⁻ z, (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t).indicator F z)
              * (Set.Ioi (0 : ℝ)).indicator G t := by
              rw [lintegral_congr (fun z => tail_swap_step_right F t z)]
        _ = (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)
              * (Set.Ioi (0 : ℝ)).indicator G t := by
              rw [lintegral_indicator (measurableSet_Ioo.inter measurableSet_Iio) F]
    calc ∫⁻ t, ∫⁻ z, Ψ z t
        = ∫⁻ t, (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)
            * (Set.Ioi (0 : ℝ)).indicator G t :=
          lintegral_congr hpt
      _ = ∫⁻ t, (Set.Ioi (0 : ℝ)).indicator
            (fun t => G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z)) t :=
          lintegral_congr (fun t => tail_swap_step_out G
            (fun s => ∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio s), F z) t)
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), G t * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), F z) := by
          rw [lintegral_indicator measurableSet_Ioi]
  have hswap : (∫⁻ z, ∫⁻ t, Ψ z t) = ∫⁻ t, ∫⁻ z, Ψ z t :=
    lintegral_lintegral_swap (f := Ψ) hAE
  rw [← h1, hswap, h2]

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo_zero_min =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

-- Intended file: Submission/Work/FTS/PhiStar/Honesty/lintegral_ofReal_rpow_Ioo_zero_min.lean
-- Intended namespace: Work.FTS.PhiStar.Honesty.
-- Siblings to imitate: Submission/Work/FTS/PhiStar/Honesty/lintegral_ofReal_rpow_Ioo.lean
-- (`∫⁻ z in Ioo 1 t, ofReal (z^p) = ofReal ((t^(p+1)-1)/(p+1))` for `0 < p`, `1 ≤ t`) and
-- `lintegral_ofReal_rpow_Ioo_left.lean` (`∫⁻ z in Ioo t 1, ofReal (z^r)` for `r < -1`).
-- The interval here is `(0,1) ∩ (0,t)` and the exponent satisfies `-1 < r`.
open MeasureTheory Set Filter

/-- For `-1 < r` and any upper endpoint `m > 0`, the `ENNReal`-valued integral of
`z ↦ ofReal (z^r)` over `(0,m)` is exactly the `ofReal` of the Riemann integral
`∫_0^m z^r dz = m^(r+1)/(r+1)`. -/
theorem lintegral_ofReal_rpow_Ioo_zero_end (r m : ℝ) (hr : -1 < r) (hm : 0 < m) :
    (∫⁻ z in Set.Ioo (0 : ℝ) m, ENNReal.ofReal (z ^ r))
      = ENNReal.ofReal (m ^ (r + 1) / (r + 1)) := by
  have hr1 : 0 < r + 1 := by linarith
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hm.le]
    rw [integral_rpow (Or.inl hr), Real.zero_rpow hr1.ne']
    ring
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hm.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg hx.1.le r

/-- For `-1 < r` and `t > 0`, the `ENNReal`-valued integral of `z ↦ ofReal (z^r)` over the
interval `(0,1) ∩ (0,t)` is at most `ofReal (t^(r+1)/(r+1))`.  (Equality holds for `t ≤ 1`,
where the interval is `(0,t)`; for `t > 1` the interval is `(0,1)` and the value is
`ofReal (1/(r+1)) ≤ ofReal (t^(r+1)/(r+1))`.) -/
theorem lintegral_ofReal_rpow_Ioo_zero_min {r t : ℝ} (hr : -1 < r) (ht : 0 < t) :
    (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), ENNReal.ofReal (z ^ r))
      ≤ ENNReal.ofReal (t ^ (r + 1) / (r + 1)) := by
  have hr1 : 0 < r + 1 := by linarith
  have hm : 0 < min (1 : ℝ) t := lt_min zero_lt_one ht
  have hset : Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t = Set.Ioo 0 (min 1 t) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
    exact ⟨fun ⟨⟨h0, h1⟩, ht'⟩ => ⟨h0, lt_min h1 ht'⟩,
      fun ⟨h0, h⟩ => ⟨⟨h0, lt_of_lt_of_le h (min_le_left _ _)⟩,
        lt_of_lt_of_le h (min_le_right _ _)⟩⟩
  rw [hset, lintegral_ofReal_rpow_Ioo_zero_end r (min 1 t) hr hm]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hr1.le)
  exact Real.rpow_le_rpow (le_of_lt hm) (min_le_right _ _) hr1.le

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.mixed_eq_zero_off_box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Topology
open Filter

/-- `VanishOff a b c d H` says that `H` vanishes at every point lying off the closed
box `[a,b] × [c,d]` (in either coordinate). -/
private def VanishOff (a b c d : ℝ) (H : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → H z θ = 0

/-- The plain `z`-derivative of a function vanishing off the box again vanishes off the
box: off the box the `z`-slice is identically zero on a whole neighbourhood, hence its
(totalised) `deriv` is `0`. -/
private lemma pz_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.pz H) := by
  intro z θ hb
  have hev : (fun z' : ℝ => H z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    rcases hb with hz | hθ
    · filter_upwards [(isClosed_Icc (a := a) (b := b)).isOpen_compl.mem_nhds hz] with z' hz'
      exact h z' θ (Or.inl hz')
    · filter_upwards with z'
      exact h z' θ (Or.inr hθ)
  change deriv (fun z' : ℝ => H z' θ) z = 0
  rw [hev.deriv_eq, deriv_const]

/-- The plain `θ`-derivative of a function vanishing off the box again vanishes off the
box. -/
private lemma pth_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.pth H) := by
  intro z θ hb
  have hev : (fun θ' : ℝ => H z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    rcases hb with hz | hθ
    · filter_upwards with θ'
      exact h z θ' (Or.inl hz)
    · filter_upwards [(isClosed_Icc (a := c) (b := d)).isOpen_compl.mem_nhds hθ] with θ' hθ'
      exact h z θ' (Or.inr hθ')
  change deriv (fun θ' : ℝ => H z θ') θ = 0
  rw [hev.deriv_eq, deriv_const]

/-- `D_z H = z ∂_z H` of a function vanishing off the box again vanishes off the box. -/
private lemma Dz_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.Dz H) := by
  intro z θ hb
  change z * Work.Spaces.pz H z θ = 0
  rw [pz_vanishOff h z θ hb, mul_zero]

/-- `D_θ H = sin(2θ) ∂_θ H` of a function vanishing off the box again vanishes off the box. -/
private lemma Dth_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.Dth H) := by
  intro z θ hb
  change Real.sin (2 * θ) * Work.Spaces.pth H z θ = 0
  rw [pth_vanishOff h z θ hb, mul_zero]

theorem mixed_eq_zero_off_box {G : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hG : ∀ z θ, G z θ ≠ 0 → z ∈ Set.Icc a b ∧ θ ∈ Set.Icc c d) :
    ∀ j i : ℕ, ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
      Work.Spaces.mixed j i G z θ = 0 := by
  have hGQ : VanishOff a b c d G := by
    intro z θ hb
    by_contra hne
    rcases hG z θ hne with ⟨h1, h2⟩
    rcases hb with hz | hθ
    · exact hz h1
    · exact hθ h2
  -- every pure `θ`-iterate of `G` vanishes off the box
  have hDth : ∀ i : ℕ, VanishOff a b c d (Work.Spaces.DthIter i G) := by
    intro i
    induction i with
    | zero => exact hGQ
    | succ i ih => exact Dth_vanishOff ih
  intro j i z θ hb
  -- and then so does every further `z`-iterate
  have hDz : ∀ j : ℕ, VanishOff a b c d (Work.Spaces.DzIter j (Work.Spaces.DthIter i G)) := by
    intro j
    induction j with
    | zero => exact hDth i
    | succ j ih => exact Dz_vanishOff ih
  exact hDz j z θ hb

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.psi_cs_of_aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- Weighted Cauchy–Schwarz ("psi_cs", `AEStronglyMeasurable` form): for `p > 0`, `z > 0`,
`c` a.e.-strongly-measurable on `(z,∞)` with `c²` integrable there,
`(∫_z^∞ c t · t^{-p-1})² ≤ (1/p) z^{-p} ∫_z^∞ c² t^{-p-1}`.

The splitting is `c t · t^{-p-1} = (c t · t^{-(p+1)/2}) · t^{-(p+1)/2}`; Cauchy–Schwarz in
`L²((z,∞))` gives the product of the two second moments, and `∫_z^∞ t^{-p-1} = z^{-p}/p`. -/
theorem psi_cs_of_aesm {p : ℝ} (hp : 0 < p) {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi z)))
    (h2 : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi z)) :
    (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
  set e : ℝ := (-p - 1) / 2 with he
  have he_neg : e < 0 := by rw [he]; linarith
  have hee : e + e = -p - 1 := by rw [he]; ring
  have hp1 : -p - 1 < -1 := by linarith
  have hms : MeasurableSet (Set.Ioi z) := measurableSet_Ioi
  -- `t ↦ t ^ e` is continuous on `(z,∞)`
  have he_cont : ContinuousOn (fun t : ℝ => t ^ e) (Set.Ioi z) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x e (Or.inl (ne_of_gt (hz.trans hx)))).continuousWithinAt
  have hsplit : ∀ t ∈ Set.Ioi z, c t * t ^ (-p - 1) = (c t * t ^ e) * t ^ e := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    rw [mul_assoc, ← Real.rpow_add ht0, hee]
  have hsq_f : ∀ t ∈ Set.Ioi z, ‖c t * t ^ e‖ ^ 2 = (c t) ^ 2 * t ^ (-p - 1) := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    have hte : 0 ≤ t ^ e := Real.rpow_nonneg ht0.le e
    have h1 : ‖c t * t ^ e‖ = |c t| * t ^ e := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hte]
    have h2 : (t ^ e) ^ 2 = t ^ (-p - 1) := by
      rw [sq, ← Real.rpow_add ht0, hee]
    rw [h1, mul_pow, sq_abs, h2]
  have hsq_g : ∀ t ∈ Set.Ioi z, (t ^ e) ^ 2 = t ^ (-p - 1) := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    rw [sq, ← Real.rpow_add ht0, hee]
  -- integrability and `MemLp` bookkeeping
  have hcmem : MemLp c 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hc).2 h2
  have hgaesm : AEStronglyMeasurable (fun t : ℝ => t ^ e) (volume.restrict (Set.Ioi z)) :=
    he_cont.aestronglyMeasurable hms
  have hg_mem : MemLp (fun t : ℝ => t ^ e) 2 (volume.restrict (Set.Ioi z)) := by
    rw [memLp_two_iff_integrable_sq hgaesm]
    refine Integrable.congr (f := fun t : ℝ => t ^ (-p - 1)) ?_ ?_
    · exact integrableOn_Ioi_rpow_of_lt hp1 hz
    · filter_upwards [ae_restrict_mem hms] with t ht
      exact (hsq_g t ht).symm
  have hfaesm : AEStronglyMeasurable (fun t : ℝ => c t * t ^ e) (volume.restrict (Set.Ioi z)) :=
    hc.mul hgaesm
  have hf_mem : MemLp (fun t : ℝ => c t * t ^ e) 2 (volume.restrict (Set.Ioi z)) := by
    refine MemLp.of_le_mul (c := z ^ e) hcmem hfaesm ?_
    filter_upwards [ae_restrict_mem hms] with t ht
    have ht0 : 0 < t := hz.trans ht
    have hte : 0 ≤ t ^ e := Real.rpow_nonneg ht0.le e
    have hle : t ^ e ≤ z ^ e := Real.rpow_le_rpow_of_nonpos hz ht.le he_neg.le
    have h1 : ‖c t * t ^ e‖ = ‖c t‖ * t ^ e := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hte]
    rw [h1, mul_comm (z ^ e)]
    exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  -- Cauchy–Schwarz in `L²`
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Set.Ioi z))
    (f := fun t : ℝ => c t * t ^ e) (g := fun t : ℝ => t ^ e) hpq
    (by simpa using hf_mem) (by simpa using hg_mem)
  -- identify the two `L²` norms on the right
  have hB : ∫ t in Set.Ioi z, ‖c t * t ^ e‖ ^ (2 : ℝ) = ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hms] with t ht
    rw [Real.rpow_two]
    exact hsq_f t ht
  have hP : ∫ t in Set.Ioi z, ‖t ^ e‖ ^ (2 : ℝ) = z ^ (-p) / p := by
    have h1 : ∫ t in Set.Ioi z, ‖t ^ e‖ ^ (2 : ℝ) = ∫ t in Set.Ioi z, t ^ (-p - 1) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hms] with t ht
      rw [Real.rpow_two, Real.norm_of_nonneg (Real.rpow_nonneg (hz.trans ht).le e)]
      exact hsq_g t ht
    rw [h1, integral_Ioi_rpow_of_lt hp1 hz, show -p - 1 + 1 = -p by ring, neg_div_neg_eq]
  have hholder' : ∫ t in Set.Ioi z, ‖c t * t ^ e‖ * ‖t ^ e‖
      ≤ Real.sqrt (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) * Real.sqrt (z ^ (-p) / p) := by
    have hh := hholder
    rw [hB, hP] at hh
    rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  -- the `‖∫ f‖ ≤ ∫ ‖f‖` step
  have hnorm : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioi z, ‖c t * t ^ e‖ * ‖t ^ e‖ := by
    have h1 : ∫ t in Set.Ioi z, c t * t ^ (-p - 1) = ∫ t in Set.Ioi z, (c t * t ^ e) * t ^ e := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hms] with t ht
      exact hsplit t ht
    have h2 : ∫ t in Set.Ioi z, ‖(c t * t ^ e) * t ^ e‖
        = ∫ t in Set.Ioi z, ‖c t * t ^ e‖ * ‖t ^ e‖ := by
      refine integral_congr_ae ?_
      filter_upwards with t
      rw [norm_mul]
    have h3 : ‖∫ t in Set.Ioi z, (c t * t ^ e) * t ^ e‖
        ≤ ∫ t in Set.Ioi z, ‖(c t * t ^ e) * t ^ e‖ := norm_integral_le_integral_norm _
    rw [h2] at h3
    rw [← h1] at h3
    rwa [← Real.norm_eq_abs]
  -- square everything
  have hBI : 0 ≤ ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hms] with t ht
    have ht0 : 0 < t := hz.trans ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _)
  have hPI : 0 ≤ z ^ (-p) / p :=
    div_nonneg (Real.rpow_nonneg hz.le _) hp.le
  calc (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      = |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ^ 2 := by rw [sq_abs]
    _ ≤ (Real.sqrt (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) * Real.sqrt (z ^ (-p) / p)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hnorm.trans hholder') 2
    _ = (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) * (z ^ (-p) / p) := by
        rw [mul_pow, Real.sq_sqrt hBI, Real.sq_sqrt hPI]
    _ = (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by ring

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgB_tail_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-! ## The near piece `(δ,1]` -/




/-! ## The tail bound -/


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.slice_pointwise_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.PhiStar.Honesty

/-- A real number is at most its own square plus `1 / 2`:
`x ^ 2 + 1 / 2 - x = (x - 1 / 2) ^ 2 + 1 / 4 ≥ 0`. -/
private lemma self_le_sq_add_half (x : ℝ) : x ≤ x ^ 2 + 1 / 2 := by
  nlinarith [sq_nonneg (x - 1 / 2)]

/-- If `1 ≤ y` then `|x| ^ 2 ≤ (x * y) ^ 2`. -/
private lemma abs_sq_le_mul_sq {x y : ℝ} (hy : 1 ≤ y) : |x| ^ 2 ≤ (x * y) ^ 2 := by
  rw [mul_pow, sq_abs]
  exact le_mul_of_one_le_right (sq_nonneg x) (by nlinarith [hy])

/-- The `i`-th term of the radial part of `HkIntegrand α 1 F` is dominated by the integrand
itself, for `i ≤ 1`. -/
private lemma extract_le_HkIntegrand {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ} {i : ℕ} (hi : i ≤ 1) :
    (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 F z θ := by
  rw [Work.Spaces.HkIntegrand]
  have hnn : 0 ≤ ∑ i ∈ Finset.range (1 + 1), ∑ j ∈ Finset.range (1 + 1),
      (if 1 ≤ i ∧ i + j ≤ 1 then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl _
  refine le_trans ?_ (le_add_of_nonneg_right hnn)
  exact Finset.single_le_sum
    (f := fun k => (Work.Spaces.DzIter k F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun k _ => sq_nonneg _) (by rw [Finset.mem_range]; omega)

theorem slice_pointwise_le {α a t : ℝ} {F : ℝ → ℝ → ℝ} (ha : 0 < a) (hat : a ≤ t) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2 ∧
      |Work.Spaces.pz F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hsinpos : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1]
    · have := Real.pi_pos; linarith [hθ.2]
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hw : 1 ≤ Work.Spaces.w t := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < t ^ 2)]
    nlinarith [sq_nonneg t]
  -- the weight `c = w t / sin(2θ)^(η/2)` occurring in the `HkIntegrand` is at least `1`
  set c : ℝ := Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hcdef
  have hc : 1 ≤ c := by
    rw [hcdef]
    exact (one_le_div hspos).mpr (le_trans hsle hw)
  set A : ℝ := Work.Spaces.HkIntegrand α 1 F t θ with hAdef
  -- the `i = 0` and `i = 1` summands of the `HkIntegrand`
  have hterm0 : (F t θ * c) ^ 2 ≤ A := by
    rw [hcdef, hAdef]
    simpa using extract_le_HkIntegrand (α := α) (F := F) (z := t) (θ := θ) (i := 0) (by norm_num)
  have hterm1 : (t * Work.Spaces.pz F t θ * c) ^ 2 ≤ A := by
    rw [hcdef, hAdef]
    have h := extract_le_HkIntegrand (α := α) (F := F) (z := t) (θ := θ) (i := 1) (by norm_num)
    rw [show Work.Spaces.DzIter 1 F t θ = t * Work.Spaces.pz F t θ from rfl] at h
    exact h
  constructor
  · -- first conjunct: `|F t θ| ≤ F² ≤ HkIntegrand`
    have hsq : |F t θ| ^ 2 ≤ (F t θ * c) ^ 2 := abs_sq_le_mul_sq hc
    have hlin : |F t θ| ≤ |F t θ| ^ 2 + 1 / 2 := self_le_sq_add_half _
    linarith
  · -- second conjunct: `|∂_z F t θ| ≤ (t/a)²·c²·(∂_z F)² ≤ HkIntegrand / a²`
    have hta : 1 ≤ t / a := (one_le_div ha).mpr hat
    have hd : 1 ≤ t / a * c := by nlinarith [hta, hc]
    have heq : (|Work.Spaces.pz F t θ| * (t / a * c)) ^ 2
        = (t * Work.Spaces.pz F t θ * c) ^ 2 / a ^ 2 := by
      simp only [mul_pow, sq_abs]
      rw [div_pow]
      ring
    have h2 : (|Work.Spaces.pz F t θ| * (t / a * c)) ^ 2 ≤ A / a ^ 2 := by
      rw [heq]
      exact div_le_div_of_nonneg_right hterm1 (by positivity)
    have hsq : |Work.Spaces.pz F t θ| ^ 2
        ≤ (|Work.Spaces.pz F t θ| * (t / a * c)) ^ 2 := by
      simpa using abs_sq_le_mul_sq (x := |Work.Spaces.pz F t θ|) hd
    have hlin : |Work.Spaces.pz F t θ| ≤ |Work.Spaces.pz F t θ| ^ 2 + 1 / 2 :=
      self_le_sq_add_half _
    linarith

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.sq_rpow_tail_mul_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

/-- **Weighted Hardy/Cauchy–Schwarz tail bound.**

For `p > 0`, `z ≥ 1`, an a.e.-measurable `c` with `c²` integrable on `(1,∞)`, the square of
`z^p ∫_z^∞ c t · t^{-p-1} dt` is at most `(2p)^{-1} ∫_z^∞ c t² · t^{-1} dt`.

This is the classical Hardy inequality for the half-line, proved by writing
`c t · t^{-p-1} = (c t · t^{-1/2}) · t^{-p-1/2}` and applying Cauchy–Schwarz on `L²((z,∞))`
(`Work.Spaces.cs_integral`); the second factor contributes `∫_z^∞ t^{-2p-1} = z^{-2p}/(2p)`. -/
theorem sq_rpow_tail_mul_integral_le {c : ℝ → ℝ} {p z : ℝ} (hp : 0 < p) (hz : 1 ≤ z)
    (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi (1 : ℝ))) :
    (z ^ p * ∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (1 / (2 * p)) * (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  -- `z ≥ 1 > 0`
  have hc2 : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi z) :=
    hfar.mono_set (Set.Ioi_subset_Ioi hz)
  have hc_meas : AEStronglyMeasurable c (volume.restrict (Set.Ioi z)) :=
    hc.aestronglyMeasurable.restrict
  -- the power functions are continuous (hence a.e. strongly measurable) on `(z,∞)`
  have hcont_pow : ∀ r : ℝ, ContinuousOn (fun t : ℝ => t ^ r) (Set.Ioi z) := fun r =>
    continuous_id.continuousOn.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz0 ht)))
  have hmeas_pow : ∀ r : ℝ,
      AEStronglyMeasurable (fun t : ℝ => t ^ r) (volume.restrict (Set.Ioi z)) := fun r =>
    (hcont_pow r).aestronglyMeasurable measurableSet_Ioi
  -- `c² · t^{-1}` is integrable on `(z,∞)`, dominated by `c²` because `t ≥ 1` there
  have hJint : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (-1 : ℝ)) (Set.Ioi z) := by
    refine Integrable.mono' hc2 ((hc_meas.pow 2).mul (hmeas_pow (-1))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := le_trans hz (le_of_lt ht)
    have ht0 : 0 < t := lt_trans hz0 ht
    have hle : t ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (c t)),
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_of_le_one_right (sq_nonneg _) hle
  -- the two `L²` factors
  have hu_meas : AEStronglyMeasurable (fun t : ℝ => c t * t ^ (-1 / 2 : ℝ))
      (volume.restrict (Set.Ioi z)) := hc_meas.mul (hmeas_pow (-1 / 2))
  have hv_meas : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1 / 2 : ℝ))
      (volume.restrict (Set.Ioi z)) := hmeas_pow (-p - 1 / 2)
  have hu_sq : Integrable (fun t : ℝ => (c t * t ^ (-1 / 2 : ℝ)) ^ 2)
      (volume.restrict (Set.Ioi z)) := by
    refine hJint.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz0 ht
    have h : (t ^ (-1 / 2 : ℝ)) ^ 2 = t ^ (-1 : ℝ) := by
      rw [pow_two, ← Real.rpow_add ht0]; norm_num
    rw [mul_pow, h]
  have hv_sq : Integrable (fun t : ℝ => (t ^ (-p - 1 / 2 : ℝ)) ^ 2)
      (volume.restrict (Set.Ioi z)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 1) (by linarith) hz0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz0 ht
    rw [pow_two, ← Real.rpow_add ht0]
    ring_nf
  -- Cauchy–Schwarz on `(z,∞)`
  have hcs := Work.Spaces.cs_integral
    (u := fun t : ℝ => c t * t ^ (-1 / 2 : ℝ))
    (v := fun t : ℝ => t ^ (-p - 1 / 2 : ℝ))
    ((memLp_two_iff_integrable_sq hu_meas).mpr hu_sq)
    ((memLp_two_iff_integrable_sq hv_meas).mpr hv_sq)
  -- identify the three integrals appearing in Cauchy–Schwarz
  have e1 : (∫ x in Set.Ioi z, c x * x ^ (-1 / 2 : ℝ) * x ^ (-p - 1 / 2 : ℝ))
      = ∫ t in Set.Ioi z, c t * t ^ (-p - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hz0 ht
    rw [mul_assoc, ← Real.rpow_add ht0]
    ring_nf
  have e2 : (∫ x in Set.Ioi z, (c x * x ^ (-1 / 2 : ℝ)) ^ 2)
      = ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hz0 ht
    have h : (t ^ (-1 / 2 : ℝ)) ^ 2 = t ^ (-1 : ℝ) := by
      rw [pow_two, ← Real.rpow_add ht0]; norm_num
    rw [mul_pow, h]
  have e3 : (∫ x in Set.Ioi z, (x ^ (-p - 1 / 2 : ℝ)) ^ 2) = z ^ (-2 * p) / (2 * p) := by
    have hcong : (∫ x in Set.Ioi z, (x ^ (-p - 1 / 2 : ℝ)) ^ 2)
        = ∫ t in Set.Ioi z, t ^ (-2 * p - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hz0 ht
      rw [pow_two, ← Real.rpow_add ht0]
      ring_nf
    rw [hcong, integral_Ioi_rpow_of_lt (a := -2 * p - 1) (by linarith) hz0]
    rw [show (-2 * p - 1) + 1 = -2 * p by ring]
    ring
  have hmain : (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) * (z ^ (-2 * p) / (2 * p)) := by
    rw [← e1, ← e2, ← e3]
    exact hcs
  have hzp : (z ^ p) ^ 2 = z ^ (2 * p) := by
    rw [pow_two, ← Real.rpow_add hz0]; ring_nf
  have hzz : z ^ (2 * p) * z ^ (-2 * p) = 1 := by
    rw [← Real.rpow_add hz0, show 2 * p + (-2 * p) = 0 by ring, Real.rpow_zero]
  calc (z ^ p * ∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      = z ^ (2 * p) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2 := by
        rw [mul_pow, hzp]
    _ ≤ z ^ (2 * p) * ((∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) *
          (z ^ (-2 * p) / (2 * p))) :=
        mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hz0.le _)
    _ = (1 / (2 * p)) * (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) := by
        rw [show z ^ (2 * p) * ((∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) *
              (z ^ (-2 * p) / (2 * p)))
            = (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) *
              (z ^ (2 * p) * z ^ (-2 * p)) / (2 * p) by ring]
        rw [hzz]
        ring

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.tendsto_sq_mul_w_sq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

/-- The square of the radial weight `w(z) = (1+z)²/z²` in closed form.
Because Lean's division is total, this holds for every `t` (both sides vanish at `t = 0`). -/
private lemma w_sq_eq (t : ℝ) : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  ring_nf

/-- `(w t)² = ((1+t)/t)⁴`; the form in which the factor is genuinely continuous on `(0,∞)`. -/
private lemma div_w_sq_eq (t : ℝ) : ((1 + t) / t) ^ 4 = (Work.Spaces.w t) ^ 2 := by
  rw [w_sq_eq, div_pow]

/-- Pointwise domination on the near field `(0,1]`: `w(t)² ≤ 16/t⁴` there. -/
private lemma sq_mul_w_sq_le_near {x t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    x ^ 2 * (Work.Spaces.w t) ^ 2 ≤ 16 * (x ^ 2 / t ^ 4) := by
  have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht0 4
  have h1t : (1 + t) ^ 4 ≤ 16 := by
    have hle : 1 + t ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + t := by linarith
    calc (1 + t) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 hle 4
      _ = 16 := by norm_num
  have hw : x ^ 2 * (Work.Spaces.w t) ^ 2 = (x ^ 2 * (1 + t) ^ 4) / t ^ 4 := by
    rw [w_sq_eq, mul_div_assoc]
  rw [hw, ← mul_div_assoc, div_le_div_iff_of_pos_right ht4]
  calc x ^ 2 * (1 + t) ^ 4 ≤ x ^ 2 * 16 := mul_le_mul_of_nonneg_left h1t (sq_nonneg x)
    _ = 16 * x ^ 2 := by ring

/-- Pointwise domination on the far field `[1,∞)`: `w(t)² ≤ 16` there. -/
private lemma sq_mul_w_sq_le_far {x t : ℝ} (ht : 1 ≤ t) :
    x ^ 2 * (Work.Spaces.w t) ^ 2 ≤ 16 * x ^ 2 := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht0 4
  have hle : (1 + t) ^ 4 ≤ 16 * t ^ 4 := by
    have h1 : 1 + t ≤ 2 * t := by linarith
    have h0 : (0 : ℝ) ≤ 1 + t := by linarith
    calc (1 + t) ^ 4 ≤ (2 * t) ^ 4 := pow_le_pow_left₀ h0 h1 4
      _ = 16 * t ^ 4 := by ring
  have hw16 : (Work.Spaces.w t) ^ 2 ≤ 16 := by
    rw [w_sq_eq, div_le_iff₀ ht4]
    exact hle
  calc x ^ 2 * (Work.Spaces.w t) ^ 2 ≤ x ^ 2 * 16 :=
        mul_le_mul_of_nonneg_left hw16 (sq_nonneg x)
    _ = 16 * x ^ 2 := by ring

/-- The half-line `(0,∞)` is the (a.e. equal) disjoint union `(0,1) ∪ (1,∞)`. -/
private lemma Ioi_zero_ae_eq_Ioo_union_Ioi :
    Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  rw [MeasureTheory.ae_eq_set]
  have h₁ : Set.Ioi (0 : ℝ) \ (Set.Ioo 0 1 ∪ Set.Ioi 1) = {1} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, hnot⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hnot (Or.inl ⟨h0, h⟩)
      · exact hnot (Or.inr h)
    · rintro rfl
      norm_num
  have h₂ : (Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi 1) \ Set.Ioi 0 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx | hx, hx0⟩
    · exact hx0 hx.1
    · exact hx0 (Set.mem_Ioi.mpr (lt_trans one_pos (Set.mem_Ioi.mp hx)))
  exact ⟨by rw [h₁, measure_singleton], by rw [h₂, measure_empty]⟩

theorem tendsto_sq_mul_w_sq_zero {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (h1 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (h2 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1))
    (h1c : Filter.Tendsto (fun n => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4) Filter.atTop (nhds 0))
    (h2c : Filter.Tendsto (fun n => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop (nhds 0) := by
  -- ### Integrability of the weighted square on the two halves
  have hF1 : ∀ n, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioo (0:ℝ) 1) := by
    intro n
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
      have hg : AEStronglyMeasurable (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4)
          (volume.restrict (Set.Ioo (0:ℝ) 1)) := (h1 n).aestronglyMeasurable
      have hc : AEStronglyMeasurable (fun t : ℝ => (1 + t) ^ 4)
          (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
        ((continuous_const.add continuous_id).pow 4).aestronglyMeasurable
      refine (hg.mul hc).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t _
      show ((c_ n t - c t) ^ 2 / t ^ 4) * (1 + t) ^ 4
        = (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2
      rw [w_sq_eq]
      ring_nf
    refine Integrable.mono' (g := fun t : ℝ => 16 * ((c_ n t - c t) ^ 2 / t ^ 4)) ?_ hmeas ?_
    · exact (h1 n).const_mul 16
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact sq_mul_w_sq_le_near ht.1 ht.2.le
  have hF2 : ∀ n, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi (1:ℝ)) := by
    intro n
    have hcont : ContinuousOn (fun t : ℝ => ((1 + t) / t) ^ 4) (Set.Ioi (1:ℝ)) := by
      apply ContinuousOn.pow
      apply ContinuousOn.div
      · exact (continuous_const.add continuous_id).continuousOn
      · exact continuous_id.continuousOn
      · intro t ht
        exact ne_of_gt (lt_trans one_pos ht)
    have hc : AEStronglyMeasurable (fun t : ℝ => ((1 + t) / t) ^ 4)
        (volume.restrict (Set.Ioi (1:ℝ))) := hcont.aestronglyMeasurable measurableSet_Ioi
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (volume.restrict (Set.Ioi (1:ℝ))) := by
      refine ((h2 n).aestronglyMeasurable.mul hc).congr ?_
      filter_upwards with t
      show (c_ n t - c t) ^ 2 * ((1 + t) / t) ^ 4
        = (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2
      rw [div_w_sq_eq]
    refine Integrable.mono' (g := fun t : ℝ => 16 * (c_ n t - c t) ^ 2) ?_ hmeas ?_
    · exact (h2 n).const_mul 16
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact sq_mul_w_sq_le_far ht.le
  -- ### Splitting the half-line
  have hdisj : Disjoint (Set.Ioo (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
    rw [disjoint_left]
    intro x hx1 hx2
    exact absurd hx2 (not_lt.mpr hx1.2.le)
  have hsplit : ∀ n, (∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      = (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        + (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
    intro n
    rw [MeasureTheory.setIntegral_congr_set Ioi_zero_ae_eq_Ioo_union_Ioi]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi (hF1 n) (hF2 n)
  -- ### The two half-line bounds
  have hb1 : ∀ n, (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      ≤ 16 * ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4 := by
    intro n
    have h := MeasureTheory.setIntegral_mono_of_nonneg
      (s := Set.Ioo (0:ℝ) 1)
      (f := fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (g := fun t : ℝ => 16 * ((c_ n t - c t) ^ 2 / t ^ 4))
      (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun t ht => sq_mul_w_sq_le_near ht.1 ht.2.le)
      ((h1 n).const_mul 16)
    calc (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        ≤ ∫ t in Set.Ioo (0:ℝ) 1, 16 * ((c_ n t - c t) ^ 2 / t ^ 4) := h
      _ = 16 * ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4 := by
          rw [MeasureTheory.integral_const_mul]
  have hb2 : ∀ n, (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      ≤ 16 * ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 := by
    intro n
    have h := MeasureTheory.setIntegral_mono_of_nonneg
      (s := Set.Ioi (1:ℝ))
      (f := fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (g := fun t : ℝ => 16 * (c_ n t - c t) ^ 2)
      (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun t ht => sq_mul_w_sq_le_far ht.le)
      ((h2 n).const_mul 16)
    calc (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        ≤ ∫ t in Set.Ioi (1:ℝ), 16 * (c_ n t - c t) ^ 2 := h
      _ = 16 * ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
  -- ### The majorant sequence tends to `0`
  have hupper : Filter.Tendsto
      (fun n => 16 * (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
        + 16 * (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)) Filter.atTop (nhds 0) := by
    have h := (h1c.const_mul (16:ℝ)).add (h2c.const_mul (16:ℝ))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0:ℝ)) (f := Filter.atTop)) hupper ?_ ?_
  · intro n
    show (0:ℝ) ≤ ∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2
    rw [hsplit n]
    exact add_nonneg
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioi
        (fun t _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  · intro n
    show (∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        ≤ 16 * (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
          + 16 * (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)
    rw [hsplit n]
    linarith [hb1 n, hb2 n]

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Aux.cos_sq_Gam_div_sin_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The integrand `cos²t · Γ(α,t) / sin t` of the angular tail integral. -/
def Igr (α t : ℝ) : ℝ := Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t

/-! ## Elementary identities and pointwise bounds -/

/-- The basic rewrite `c² (s c²)^p / s = c^{2+2p} s^{p-1}` for `c, s > 0`. -/
lemma rpow_id (p c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    c ^ 2 * (s * c ^ 2) ^ p / s = c ^ (2 + 2 * p) * s ^ (p - 1) := by
  rw [show (c ^ 2 : ℝ) = c ^ (2 : ℝ) by norm_num [Real.rpow_ofNat]]
  have hc2 : (0 : ℝ) < c ^ (2 : ℝ) := Real.rpow_pos_of_pos hc 2
  have h1 : (s * c ^ (2 : ℝ)) ^ p = s ^ p * (c ^ (2 : ℝ)) ^ p :=
    Real.mul_rpow (le_of_lt hs) (le_of_lt hc2)
  rw [h1, ← Real.rpow_mul (le_of_lt hc) (2 : ℝ) p]
  have h3 : c ^ (2 + 2 * p) = c ^ (2 : ℝ) * c ^ (2 * p) := Real.rpow_add hc 2 (2 * p)
  rw [h3, show s ^ (p - 1) = s ^ p / s ^ (1 : ℝ) by rw [Real.rpow_sub hs p 1], Real.rpow_one]
  ring

/-- For `t ∈ (0,π/2)` the integrand equals `cos(t)^{2+2α/3} sin(t)^{α/3-1}`. -/
lemma Igr_eq (α t : ℝ) (ht0 : 0 < t) (ht1 : t < π / 2) :
    Igr α t = Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t ^ (α / 3 - 1) := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht1⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  rw [Igr, Work.Spaces.Gam]
  exact rpow_id (α / 3) (Real.cos t) (Real.sin t) hc hs

/-- The integrand is nonnegative on `(0,π/2]`. -/
lemma Igr_nonneg (α t : ℝ) (_hα : 0 < α) (ht : t ∈ Set.Ioc 0 (π / 2)) : 0 ≤ Igr α t := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · obtain ⟨ht0, _⟩ := ht
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
    have hG : 0 ≤ Work.Spaces.Gam α t :=
      Real.rpow_nonneg (mul_nonneg (le_of_lt hs) (sq_nonneg _)) _
    rw [Igr]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hG) (le_of_lt hs)
  · subst heq
    rw [Igr, Real.cos_pi_div_two]
    simp

/-- On `(0,π/2]` the integrand is dominated by `sin(t)^{α/3-1}`. -/
lemma Igr_le_sin (α t : ℝ) (hα : 0 < α) (ht : t ∈ Set.Ioc 0 (π / 2)) :
    Igr α t ≤ Real.sin t ^ (α / 3 - 1) := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · obtain ⟨ht0, _⟩ := ht
    have hc : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
    rw [Igr_eq α t ht0 hlt]
    have h1 : Real.cos t ^ (2 + 2 * (α / 3)) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hc) (Real.cos_le_one t) (by positivity)
    calc Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t ^ (α / 3 - 1)
        ≤ 1 * Real.sin t ^ (α / 3 - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt hs) _)
      _ = Real.sin t ^ (α / 3 - 1) := one_mul _
  · subst heq
    rw [Igr, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp

/-- Jordan-type linear majorant: `sin(t)^{p-1} ≤ (π/2)^{1-p} t^{p-1}` on `(0,π/2]`
for `p ≤ 1`. -/
lemma sin_rpow_le_lin (p t : ℝ) (hp1 : p ≤ 1) (ht : t ∈ Set.Ioc 0 (π / 2)) :
    Real.sin t ^ (p - 1) ≤ (π / 2) ^ (1 - p) * t ^ (p - 1) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hsin : 2 / π * t ≤ Real.sin t := Real.mul_le_sin (le_of_lt ht0) ht1
  have hpos : 0 < 2 / π * t := by positivity
  have hp2 : p - 1 ≤ 0 := by linarith
  have key := Real.rpow_le_rpow_of_nonpos hpos hsin hp2
  have hmr : (2 / π * t) ^ (p - 1) = (2 / π) ^ (p - 1) * t ^ (p - 1) :=
    Real.mul_rpow (by positivity) (le_of_lt ht0)
  have hcoef : (2 / π : ℝ) ^ (p - 1) = (π / 2) ^ (1 - p) := by
    rw [show (2 / π : ℝ) = (π / 2)⁻¹ by ring, Real.inv_rpow (by positivity : (0 : ℝ) ≤ π / 2),
      show (1 : ℝ) - p = -(p - 1) by ring, Real.rpow_neg (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [hmr, hcoef] at key
  exact key

/-- On `[2/3, π/2]` the integrand is dominated by `4 cos(t)^{2+2α/3} sin t`. -/
lemma Igr_le_hard (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (ht : t ∈ Set.Icc (2 / 3) (π / 2)) :
    Igr α t ≤ 4 * (Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t) := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · obtain ⟨ht2, _⟩ := ht
    have ht0 : 0 < t := by linarith
    have hsl : (1 : ℝ) / 2 ≤ Real.sin t := by
      have h1 : Real.pi / 6 ≤ t := by have := Real.pi_lt_four; linarith
      have h2 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6) (y := t)
        (by linarith [Real.pi_pos]) hlt.le h1
      rwa [Real.sin_pi_div_six] at h2
    rw [Igr_eq α t ht0 hlt]
    have hpow : Real.sin t ^ (α / 3 - 1) ≤ 4 * Real.sin t := by
      have h1 : Real.sin t ^ (α / 3 - 1) ≤ (1 / 2 : ℝ) ^ (α / 3 - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hsl (by linarith)
      have h2 : (1 / 2 : ℝ) ^ (α / 3 - 1) = 2 ^ (1 - α / 3) := by
        rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (α / 3 - 1),
          show -(α / 3 - 1) = 1 - α / 3 by ring]
      have h3 : (2 : ℝ) ^ (1 - α / 3) ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
          (by linarith : 1 - α / 3 ≤ 1)
        rwa [Real.rpow_one] at this
      linarith [hsl]
    have hc0 : 0 ≤ Real.cos t ^ (2 + 2 * (α / 3)) :=
      Real.rpow_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩)) _
    calc Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t ^ (α / 3 - 1)
        ≤ Real.cos t ^ (2 + 2 * (α / 3)) * (4 * Real.sin t) :=
          mul_le_mul_of_nonneg_left hpow hc0
      _ = 4 * (Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t) := by ring
  · subst heq
    rw [Igr, Real.cos_pi_div_two]
    simp [Real.zero_rpow (by linarith : 2 + 2 * (α / 3) ≠ 0)]

/-- The right-hand-side comparison for the second estimate:
`4 cos(θ)^{3+2p}/(3+2p) ≤ 100 cos³θ (sinθ cos²θ)^p` on `[2/3, π/2]`. -/
lemma hard_compare (p θ : ℝ) (hp0 : 0 < p) (hple : p ≤ 1) (hθ : θ ∈ Set.Icc (2 / 3) (π / 2)) :
    4 * (Real.cos θ) ^ (3 + 2 * p) / (3 + 2 * p)
      ≤ 100 * (Real.cos θ) ^ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ p := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [hθ2, Real.pi_pos]⟩
  have hs12 : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h1 : Real.pi / 6 ≤ θ := by have := Real.pi_lt_four; linarith
    have h2 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6) (y := θ)
      (by linarith [Real.pi_pos]) hθ2 h1
    rwa [Real.sin_pi_div_six] at h2
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hθ2, Real.pi_pos]⟩
  have hsp : (1 : ℝ) / 2 ≤ Real.sin θ ^ p := by
    have h1 : (1 / 2 : ℝ) ^ p ≤ Real.sin θ ^ p :=
      Real.rpow_le_rpow (by norm_num) hs12 (le_of_lt hp0)
    have h2 : (1 : ℝ) / 2 ≤ (1 / 2 : ℝ) ^ p := by
      have := Real.rpow_le_rpow_of_exponent_ge (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hple
      rwa [Real.rpow_one] at this
    linarith
  have hcoeff : 4 / (3 + 2 * p) ≤ 100 * Real.sin θ ^ p := by
    have h1 : 4 / (3 + 2 * p) ≤ 4 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    linarith
  rcases eq_or_lt_of_le hcos0 with hzero | hpos
  · rw [← hzero, Real.zero_rpow (by linarith : 3 + 2 * p ≠ 0)]
    simp
  · have h1 : (Real.cos θ) ^ (3 + 2 * p) = (Real.cos θ) ^ 3 * (Real.cos θ) ^ (2 * p) := by
      rw [Real.rpow_add hpos 3 (2 * p)]
      norm_num [Real.rpow_ofNat]
    have h2 : (Real.sin θ * Real.cos θ ^ 2) ^ p = Real.sin θ ^ p * (Real.cos θ) ^ (2 * p) := by
      rw [show (Real.cos θ ^ 2 : ℝ) = (Real.cos θ) ^ (2 : ℝ) by norm_num [Real.rpow_ofNat],
        Real.mul_rpow hsin0 (Real.rpow_nonneg hcos0 2), ← Real.rpow_mul hcos0 2 p]
    calc 4 * (Real.cos θ) ^ (3 + 2 * p) / (3 + 2 * p)
        = (4 / (3 + 2 * p)) * ((Real.cos θ) ^ 3 * (Real.cos θ) ^ (2 * p)) := by rw [h1]; ring
      _ ≤ (100 * Real.sin θ ^ p) * ((Real.cos θ) ^ 3 * (Real.cos θ) ^ (2 * p)) :=
          mul_le_mul_of_nonneg_right hcoeff
            (mul_nonneg (pow_nonneg hcos0 3) (Real.rpow_nonneg hcos0 _))
      _ = 100 * (Real.cos θ) ^ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ p := by rw [h2]; ring

/-! ## The two integrals -/

/-- `∫_a^b t^{p-1} dt = (b^p - a^p)/p` for `p > 0`. -/
lemma integral_rpow_sub (p a b : ℝ) (hp : 0 < p) :
    ∫ t in a..b, t ^ (p - 1) = (b ^ p - a ^ p) / p := by
  have h := integral_rpow (a := a) (b := b) (r := p - 1) (Or.inl (by linarith : -1 < p - 1))
  rw [show p - 1 + 1 = p by ring] at h
  exact h

/-- `∫_a^b cos(t)^{2+2p} sin t dt = (cos a^{3+2p} - cos b^{3+2p})/(3+2p)`. -/
lemma integral_cos_sin (p a b : ℝ) (hp : 0 < p) (hab : a ≤ b) :
    ∫ t in a..b, Real.cos t ^ (2 + 2 * p) * Real.sin t
      = (Real.cos a ^ (3 + 2 * p) - Real.cos b ^ (3 + 2 * p)) / (3 + 2 * p) := by
  have hden : 3 + 2 * p ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun t : ℝ => -(Real.cos t ^ (3 + 2 * p)) / (3 + 2 * p))
        (Real.cos x ^ (2 + 2 * p) * Real.sin x) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ (3 + 2 * p))
        ((-Real.sin x) * (3 + 2 * p) * Real.cos x ^ (2 + 2 * p)) x := by
      have h := (Real.hasDerivAt_cos x).rpow_const (Or.inr (by linarith : (1 : ℝ) ≤ 3 + 2 * p))
      rwa [show 3 + 2 * p - 1 = 2 + 2 * p by ring] at h
    have h2 : HasDerivAt (fun t : ℝ => -(Real.cos t ^ (3 + 2 * p)) / (3 + 2 * p))
        (-((-Real.sin x) * (3 + 2 * p) * Real.cos x ^ (2 + 2 * p)) / (3 + 2 * p)) x :=
      h1.neg.div_const (3 + 2 * p)
    convert h2 using 1
    field_simp
  have hcast : Continuous (fun t : ℝ => Real.cos t ^ (3 + 2 * p)) :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 3 + 2 * p)).comp Real.continuous_cos
  have hcont : ContinuousOn (fun t : ℝ => -(Real.cos t ^ (3 + 2 * p)) / (3 + 2 * p))
      (Set.Icc a b) := ((hcast.neg).div_const _).continuousOn
  have hint : IntervalIntegrable (fun t : ℝ => Real.cos t ^ (2 + 2 * p) * Real.sin t)
      volume a b :=
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
      Real.continuous_cos).mul Real.continuous_sin).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  rw [h]
  ring

/-- Comparison of an interval integral with an integrable majorant, without
integrability of the integrand itself. -/
lemma integral_le_of_majorant {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Ioc a b, 0 ≤ f t) (hg : IntegrableOn g (Set.Ioc a b))
    (hle : ∀ t ∈ Set.Ioc a b, f t ≤ g t) :
    ∫ t in a..b, f t ≤ ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hf t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hle t ht

/-! ## The two estimates -/

/-- The first estimate: on `[0, 2/3]` the tail is `≤ 100/α`. -/
theorem conjunct1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (2 / 3)) :
    ∫ t in θ..(π / 2), Igr α t ≤ 100 / α := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  have hθle : θ ≤ π / 2 := by linarith [hθ2, Real.pi_gt_three]
  set p : ℝ := α / 3 with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hple : p ≤ 1 := by rw [hpdef]; linarith
  have hhalf : (0 : ℝ) < π / 2 := by positivity
  have hpip : (π / 2) ^ (1 - p) * (π / 2) ^ p = π / 2 := by
    rw [← Real.rpow_add hhalf (1 - p) p, show 1 - p + p = 1 by ring, Real.rpow_one]
  set M : ℝ → ℝ :=
    fun t => (π / 2) ^ (1 - p) * t ^ (p - 1) + 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t)
    with hMdef
  have hint1 : IntegrableOn (fun t : ℝ => (π / 2) ^ (1 - p) * t ^ (p - 1)) (Set.Ioc θ (π / 2)) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := θ) (b := π / 2)
        (by linarith : -1 < p - 1) :
        IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume θ (π / 2)).1).const_mul _
  have hint2 : IntegrableOn (fun t : ℝ => 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t))
      (Set.Ioc θ (π / 2)) :=
    ((continuous_const.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
      Real.continuous_cos).mul Real.continuous_sin)).intervalIntegrable θ (π / 2)).1
  have hMint : IntegrableOn M (Set.Ioc θ (π / 2)) := hint1.add hint2
  have key : ∫ t in θ..(π / 2), Igr α t ≤ ∫ t in θ..(π / 2), M t := by
    apply integral_le_of_majorant hθle
    · intro t ht
      exact Igr_nonneg α t hα ⟨by linarith [ht.1, hθ0], ht.2⟩
    · exact hMint
    · intro t ht
      obtain ⟨ht0, ht1⟩ := ht
      have htpos : 0 < t := by linarith [ht0, hθ0]
      have hsin0 : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_mem_Icc ⟨le_of_lt htpos, by linarith [ht1, Real.pi_pos]⟩
      have hcos0 : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [ht1, Real.pi_pos]⟩
      have hM : M t = (π / 2) ^ (1 - p) * t ^ (p - 1)
          + 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) := rfl
      rcases le_total t (2 / 3) with hcase | hcase
      · have h1 : Igr α t ≤ (π / 2) ^ (1 - p) * t ^ (p - 1) :=
          le_trans (Igr_le_sin α t hα ⟨htpos, ht1⟩)
            (sin_rpow_le_lin p t hple ⟨htpos, ht1⟩)
        have h2 : 0 ≤ 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) :=
          mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hcos0 _) hsin0)
        rw [hM]; linarith
      · have h4 : Igr α t ≤ 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) :=
          Igr_le_hard α t hα hα1 ⟨hcase, ht1⟩
        have h5 : 0 ≤ (π / 2) ^ (1 - p) * t ^ (p - 1) :=
          mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (le_of_lt htpos) _)
        rw [hM]; linarith
  have hMval : ∫ t in θ..(π / 2), M t
      = (π / 2) ^ (1 - p) * (((π / 2) ^ p - θ ^ p) / p)
        + 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p) := by
    have h1 : IntervalIntegrable (fun t : ℝ => (π / 2) ^ (1 - p) * t ^ (p - 1)) volume θ (π / 2) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := θ) (b := π / 2)
        (by linarith : -1 < p - 1)).const_mul _
    have h2 : IntervalIntegrable (fun t : ℝ => 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t))
        volume θ (π / 2) :=
      (continuous_const.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
        Real.continuous_cos).mul Real.continuous_sin)).intervalIntegrable θ (π / 2)
    rw [hMdef]
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_rpow_sub p θ (π / 2) hp0,
      integral_cos_sin p θ (π / 2) hp0 hθle]
    ring
  have hMle : ∫ t in θ..(π / 2), M t ≤ (π / 2) / p + 4 / (3 + 2 * p) := by
    rw [hMval]
    have h1 : (π / 2) ^ (1 - p) * (((π / 2) ^ p - θ ^ p) / p)
        ≤ (π / 2) ^ (1 - p) * ((π / 2) ^ p / p) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
      apply div_le_div_of_nonneg_right _ (le_of_lt hp0)
      linarith [Real.rpow_nonneg hθ0 p]
    have h2 : 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p)
        ≤ 4 / (3 + 2 * p) := by
      rw [Real.cos_pi_div_two, Real.zero_rpow (by linarith : 3 + 2 * p ≠ 0), sub_zero]
      apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 3 + 2 * p)
      have hc0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hθle, Real.pi_pos]⟩
      have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
      have := Real.rpow_le_one hc0 hc1 (by linarith : (0 : ℝ) ≤ 3 + 2 * p)
      linarith
    have h3 : (π / 2) ^ (1 - p) * ((π / 2) ^ p / p) = (π / 2) / p := by
      rw [← mul_div_assoc, hpip]
    linarith
  have hfin : (π / 2) / p + 4 / (3 + 2 * p) ≤ 100 / α := by
    have hA : (π / 2) / p ≤ 6 / α := by
      rw [hpdef]
      rw [show (π / 2) / (α / 3) = (3 * π / 2) / α by ring]
      apply div_le_div_of_nonneg_right _ (le_of_lt hα)
      linarith [Real.pi_lt_four]
    have hB : 4 / (3 + 2 * p) ≤ 94 / α := by
      rw [hpdef]
      have hb1 : 4 / (3 + 2 * (α / 3)) ≤ 4 / 3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        linarith
      have hb2 : (4 : ℝ) / 3 ≤ 94 / α := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα]
        linarith
      linarith
    have hsum : 6 / α + 94 / α = 100 / α := by ring
    linarith
  linarith

/-- The second estimate: on `[2/3, π/2]` the tail is `≤ 100 cos³θ Γ(α,θ)`. -/
theorem conjunct2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (2 / 3) (π / 2)) :
    ∫ t in θ..(π / 2), Igr α t ≤ 100 * Real.cos θ ^ 3 * Work.Spaces.Gam α θ := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  set p : ℝ := α / 3 with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hple : p ≤ 1 := by rw [hpdef]; linarith
  have key : ∫ t in θ..(π / 2), Igr α t
      ≤ ∫ t in θ..(π / 2), 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) := by
    apply integral_le_of_majorant hθ2
    · intro t ht
      exact Igr_nonneg α t hα ⟨by linarith [ht.1, hθ0], ht.2⟩
    · exact ((continuous_const.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
        Real.continuous_cos).mul Real.continuous_sin)).intervalIntegrable θ (π / 2)).1
    · intro t ht
      obtain ⟨ht0, ht1⟩ := ht
      exact Igr_le_hard α t hα hα1 ⟨by linarith [ht0, hθ0], ht1⟩
  have hval : ∫ t in θ..(π / 2), 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t)
      = 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p) := by
    rw [intervalIntegral.integral_const_mul, integral_cos_sin p θ (π / 2) hp0 hθ2]
    ring
  have hzero : (Real.cos (π / 2)) ^ (3 + 2 * p) = 0 := by
    rw [Real.cos_pi_div_two, Real.zero_rpow (by linarith : 3 + 2 * p ≠ 0)]
  calc ∫ t in θ..(π / 2), Igr α t
      ≤ 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p) := by
        rw [← hval]; exact key
    _ = 4 * (Real.cos θ) ^ (3 + 2 * p) / (3 + 2 * p) := by rw [hzero, sub_zero]
    _ ≤ 100 * (Real.cos θ) ^ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ p :=
          hard_compare p θ hp0 hple ⟨hθ0, hθ2⟩
    _ = 100 * Real.cos θ ^ 3 * Work.Spaces.Gam α θ := by rw [Work.Spaces.Gam, ← hpdef]

/-- **The angular tail bounds.**  There is a universal constant `K` such that for every
`0 < α ≤ 1/4` the tail `∫_θ^{π/2} cos²t Γ(α,t)/sin t dt` is `≤ K/α` for `θ ∈ [0,2/3]`
and `≤ K cos³θ Γ(α,θ)` for `θ ∈ [2/3, π/2]`. -/
theorem cos_sq_Gam_div_sin_bounds : ∃ K : ℝ, 0 < K ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (0 : ℝ) (2 / 3),
      (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t) ≤ K / α) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (2 / 3 : ℝ) (Real.pi / 2),
      (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t)
        ≤ K * Real.cos θ ^ 3 * Work.Spaces.Gam α θ) := by
  refine ⟨100, by norm_num, ?_, ?_⟩
  · intro α hα hα1 θ hθ
    simpa only [Igr] using conjunct1 α hα hα1 θ hθ
  · intro α hα hα1 θ hθ
    simpa only [Igr] using conjunct2 α hα hα1 θ hθ

end Work.FTS.PhiStar.Psi0Aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.PhiStar.RadGreenSupport

open MeasureTheory Set Filter

theorem ibp_lower {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1)))
    {z : ℝ} (hz : 0 < z) :
    ∫ t in (0 : ℝ)..z,
        (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t)
          * t ^ ((2 * (m : ℝ) + 5) / α - 1)
      = α * z ^ ((2 * (m : ℝ) + 5) / α + 1) * deriv c z
        - 2 * (m : ℝ) * z ^ ((2 * (m : ℝ) + 5) / α) * c z
        + 2 * (m : ℝ) * ((2 * (m : ℝ) + 5) / α)
            * ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
  set s : ℝ := (2 * (m : ℝ) + 5) / α with hs
  have hαne : α ≠ 0 := ne_of_gt hα
  have hsdef : α * s = 2 * (m : ℝ) + 5 := by
    rw [hs]
    field_simp
    try ring
  have hnum : 0 < 2 * (m : ℝ) + 5 := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hspos : 0 < s := by
    rw [hs]
    exact div_pos hnum hα
  -- ## Elementary bounds from `hb`
  have hc_le : ∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t) := by
    intro t ht
    simpa only [iteratedDeriv_zero, Nat.zero_add, pow_one] using hb 0 (by norm_num) t ht
  have hc1_le : ∀ t : ℝ, 0 < t → |deriv c t| ≤ A / (1 + t ^ 2) := by
    intro t ht
    simpa only [iteratedDeriv_one] using hb 1 (by norm_num) t ht
  have hc2_le : ∀ t : ℝ, 0 < t → |iteratedDeriv 2 c t| ≤ A / (1 + t ^ 3) := by
    intro t ht
    exact hb 2 le_rfl t ht
  have hdiv_le : ∀ B d : ℝ, 0 ≤ B → 1 ≤ d → B / d ≤ B := by
    intro B d hB hd
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < d)]
    nlinarith [hB, hd]
  have hc_bd : ∀ t : ℝ, 0 < t → |c t| ≤ A := fun t ht =>
    le_trans (hc_le t ht) (hdiv_le A (1 + t) hA (by linarith))
  have hc1_bd : ∀ t : ℝ, 0 < t → |deriv c t| ≤ A := fun t ht =>
    le_trans (hc1_le t ht) (hdiv_le A (1 + t ^ 2) hA (by have := sq_nonneg t; linarith))
  have hc2_bd : ∀ t : ℝ, 0 < t → |iteratedDeriv 2 c t| ≤ A := fun t ht =>
    le_trans (hc2_le t ht) (hdiv_le A (1 + t ^ 3) hA (by have := pow_nonneg ht.le 3; linarith))
  -- ## Regularity of `c`, `c'`, `c''` on `(0,∞)`
  obtain ⟨hcont_c, hcont_d1, hcont_d2, hd_c, hd_dc⟩ := contDiffOn_two_regularity hc
  -- ## The primitive and its derivative
  let F : ℝ → ℝ := fun t => α * (t ^ (s + 1) * deriv c t) + (-(2 * (m : ℝ))) * (t ^ s * c t)
  let G : ℝ → ℝ := fun t =>
    (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1)
      - (2 * (m : ℝ) * s) * (c t * t ^ (s - 1))
  have hder : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt F (G t) t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hp1 : HasDerivAt (fun v : ℝ => v ^ (s + 1)) ((s + 1) * t ^ (s + 1 - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))
    have hp2 : HasDerivAt (fun v : ℝ => v ^ s) (s * t ^ (s - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))
    have hm1 : HasDerivAt (fun v : ℝ => v ^ (s + 1) * deriv c v)
        (((s + 1) * t ^ (s + 1 - 1)) * deriv c t + t ^ (s + 1) * iteratedDeriv 2 c t) t :=
      hp1.mul (hd_dc t ht0)
    have hm2 : HasDerivAt (fun v : ℝ => v ^ s * c v)
        ((s * t ^ (s - 1)) * c t + t ^ s * deriv c t) t :=
      hp2.mul (hd_c t ht0)
    have h3 := (hm1.const_mul α).add (hm2.const_mul (-(2 * (m : ℝ))))
    have hF : HasDerivAt F
        (α * (((s + 1) * t ^ (s + 1 - 1)) * deriv c t + t ^ (s + 1) * iteratedDeriv 2 c t)
          + (-(2 * (m : ℝ))) * ((s * t ^ (s - 1)) * c t + t ^ s * deriv c t)) t := by
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards with y
      simp only [F, Pi.add_apply]
    refine hF.congr_deriv ?_
    have ht1 : t ^ (s + 1 - 1) = t ^ s :=
      congr_arg (fun e : ℝ => t ^ e) (show s + 1 - 1 = s by ring)
    have ht2 : t ^ (s + 1) = t ^ (2 : ℝ) * t ^ (s - 1) := by
      rw [show s + 1 = (2 : ℝ) + (s - 1) by ring, Real.rpow_add ht0]
    have ht3 : t ^ s = t * t ^ (s - 1) := by
      calc t ^ s = t ^ ((1 : ℝ) + (s - 1)) :=
            congr_arg (fun e : ℝ => t ^ e) (show s = (1 : ℝ) + (s - 1) by ring)
        _ = t ^ 1 * t ^ (s - 1) := Real.rpow_add ht0 1 (s - 1)
        _ = t * t ^ (s - 1) := by simp only [Real.rpow_one]
    simp only [G]
    rw [ht1, ht2, ht3]
    rw [show t ^ 2 = t ^ (2 : ℝ) from (Real.rpow_natCast t 2).symm]
    linear_combination (t * t ^ (s - 1) * deriv c t) * hsdef
  -- ## Interval integrability of the two summands
  have hcont_sum : ContinuousOn
      (fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun t : ℝ => α * t ^ 2) (Set.Ioi 0) :=
      (continuousOn_const (c := α)).mul (continuousOn_id.pow 2)
    have h2 : ContinuousOn (fun t : ℝ => (5 + α) * t) (Set.Ioi 0) :=
      (continuousOn_const (c := 5 + α)).mul continuousOn_id
    have h3 : ContinuousOn (fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t) (Set.Ioi 0) :=
      h1.mul hcont_d2
    have h4 : ContinuousOn (fun t : ℝ => (5 + α) * t * deriv c t) (Set.Ioi 0) :=
      h2.mul hcont_d1
    exact h3.add h4
  have hbnd_sum : ∀ t : ℝ, 0 < t →
      |α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t| ≤ (|α| + |5 + α|) * A := by
    intro t ht
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have h12 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have h13 : (0 : ℝ) < 1 + t ^ 3 := by positivity
    have ht_sq_le : t ^ 2 ≤ 1 + t ^ 3 := by
      by_cases h : t ≤ 1
      · have h1 : 0 ≤ t * (1 - t) := mul_nonneg ht.le (by linarith)
        have h2 : 0 ≤ t ^ 3 := pow_nonneg ht.le 3
        nlinarith [h1, h2, h]
      · have h1 : 0 ≤ t ^ 2 * (t - 1) := mul_nonneg (sq_nonneg t) (by linarith [not_le.mp h])
        nlinarith [h1]
    have e1 : t ^ 2 * |iteratedDeriv 2 c t| ≤ A := by
      calc t ^ 2 * |iteratedDeriv 2 c t| ≤ t ^ 2 * (A / (1 + t ^ 3)) :=
            mul_le_mul_of_nonneg_left (hc2_le t ht) ht2
        _ = A * t ^ 2 / (1 + t ^ 3) := by ring
        _ ≤ A := by
            rw [div_le_iff₀ h13]
            exact mul_le_mul_of_nonneg_left ht_sq_le hA
    have e2 : t * |deriv c t| ≤ A := by
      have hle : t ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (2 * t - 1)]
      calc t * |deriv c t| ≤ t * (A / (1 + t ^ 2)) :=
            mul_le_mul_of_nonneg_left (hc1_le t ht) ht.le
        _ = A * t / (1 + t ^ 2) := by ring
        _ ≤ A := by
            rw [div_le_iff₀ h12]
            exact mul_le_mul_of_nonneg_left hle hA
    have eabs1 : |α * t ^ 2 * iteratedDeriv 2 c t| = |α| * (t ^ 2 * |iteratedDeriv 2 c t|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht2]
      ring
    have eabs2 : |(5 + α) * t * deriv c t| = |5 + α| * (t * |deriv c t|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.le]
      ring
    calc |α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t|
        ≤ |α * t ^ 2 * iteratedDeriv 2 c t| + |(5 + α) * t * deriv c t| := abs_add_le _ _
      _ = |α| * (t ^ 2 * |iteratedDeriv 2 c t|) + |5 + α| * (t * |deriv c t|) := by
            rw [eabs1, eabs2]
      _ ≤ |α| * A + |5 + α| * A :=
            add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg α))
              (mul_le_mul_of_nonneg_left e2 (abs_nonneg (5 + α)))
      _ = (|α| + |5 + α|) * A := by ring
  have hIA : IntervalIntegrable
      (fun t : ℝ => (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1))
      volume (0 : ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).2
      (ioc_bounded_integrable
        (f := fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t)
        (r := s) (z := z) (B := (|α| + |5 + α|) * A) hspos hz
        (mul_nonneg (add_nonneg (abs_nonneg α) (abs_nonneg (5 + α))) hA) hcont_sum hbnd_sum)
  have hIB : IntervalIntegrable (fun t : ℝ => (2 * (m : ℝ) * s) * (c t * t ^ (s - 1)))
      volume (0 : ℝ) z :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).2
      (ioc_bounded_integrable (f := c) (r := s) (z := z) (B := A) hspos hz hA hcont_c
        hc_bd)).const_mul (2 * (m : ℝ) * s)
  have hInt : IntervalIntegrable G volume (0 : ℝ) z := by
    simpa only [G] using hIA.sub hIB
  -- ## The limit of the primitive at `0⁺` and at `z`
  have hF0 : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 := tendsto_rpow_mul_bounded (f := deriv c) (r := s + 1) (B := A)
      (by linarith) hA hc1_bd
    have h2 := tendsto_rpow_mul_bounded (f := c) (r := s) (B := A) hspos hA hc_bd
    have h3 : Tendsto
        (fun t : ℝ => α * (t ^ (s + 1) * deriv c t) + (-(2 * (m : ℝ))) * (t ^ s * c t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := (Filter.Tendsto.const_mul α h1).add
        (Filter.Tendsto.const_mul (-(2 * (m : ℝ))) h2)
      simpa only [mul_zero, add_zero] using h
    simpa only [F] using h3
  have hFz : Tendsto F (nhdsWithin z (Set.Iio z)) (nhds (F z)) :=
    (hder z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- ## The fundamental theorem of calculus
  have hFTC : ∫ t in (0 : ℝ)..z, G t = F z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz
      (fun t ht => hder t ht.1) hInt hF0 hFz
    simpa only [sub_zero] using h
  have hsplit : ∫ t in (0 : ℝ)..z, G t
      = (∫ t in (0 : ℝ)..z,
            (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1))
        - (2 * (m : ℝ) * s) * (∫ t in (0 : ℝ)..z, c t * t ^ (s - 1)) := by
    simp only [G]
    rw [intervalIntegral.integral_sub hIA hIB, intervalIntegral.integral_const_mul]
  have hfin : (∫ t in (0 : ℝ)..z,
          (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (s - 1))
      = F z + (2 * (m : ℝ) * s) * (∫ t in (0 : ℝ)..z, c t * t ^ (s - 1)) := by
    rw [hFTC] at hsplit
    linarith [hsplit]
  rw [hfin]
  simp only [F]
  ring

end Work.FTS.PhiStar.RadGreenSupport
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadGreenSupport

/-- `t ^ a * t ^ b = t ^ (a + b)` for `t > 0`. -/
private lemma rpowMul {t : ℝ} (ht : 0 < t) (a b : ℝ) : t ^ a * t ^ b = t ^ (a + b) :=
  (Real.rpow_add ht a b).symm

/-- `t ^ a / t ^ n = t ^ (a - n)` for `t > 0` and a natural exponent `n`. -/
private lemma rpowDivNat {t : ℝ} (ht : 0 < t) (a : ℝ) (n : ℕ) : t ^ a / t ^ n = t ^ (a - n) := by
  rw [show t ^ n = t ^ ((n : ℕ) : ℝ) from (Real.rpow_natCast t n).symm, div_eq_mul_inv,
    ← Real.rpow_neg ht.le ((n : ℕ) : ℝ), rpowMul ht a (-((n : ℕ) : ℝ)), ← sub_eq_add_neg]

/-- `1 / t = t ^ (-1)`. -/
private lemma one_div_eq_rpow (t : ℝ) : 1 / t = t ^ (-1 : ℝ) := by
  rw [one_div, ← Real.rpow_neg_one]

/-- `t ^ (-1) * t ^ (-r - 1) = t ^ (-r - 2)`. -/
private lemma rpow_neg_one_mul {t : ℝ} (ht : 0 < t) (r : ℝ) :
    t ^ (-1 : ℝ) * t ^ (-r - 1) = t ^ (-r - 2) := by
  rw [rpowMul ht (-1) (-r - 1), show (-1 : ℝ) + (-r - 1) = -r - 2 by ring]

/-- `t ^ n / (1 + t ^ (n + 1)) ≤ 1 / t` for `t > 0`. -/
private lemma pow_div_one_add_pow_le {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ n / (1 + t ^ (n + 1)) ≤ 1 / t := by
  have hpos : (0 : ℝ) < 1 + t ^ (n + 1) := by
    have := pow_nonneg ht.le (n + 1); linarith
  rw [div_le_div_iff₀ hpos ht, one_mul, (pow_succ t n).symm]
  linarith

theorem ibp_upper {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1)))
    {z : ℝ} (hz : 0 < z) :
    ∫ t in Set.Ioi z,
        (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t)
          * t ^ (-(2 * (m : ℝ) / α) - 1)
      = -α * z ^ (1 - 2 * (m : ℝ) / α) * deriv c z
        - (2 * (m : ℝ) + 5) * z ^ (-(2 * (m : ℝ) / α)) * c z
        + (2 * (m : ℝ) + 5) * (2 * (m : ℝ) / α)
            * ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := by
  set r : ℝ := 2 * (m : ℝ) / α with hr
  have hrr : 2 * (m : ℝ) = α * r := by
    calc 2 * (m : ℝ) = (2 * (m : ℝ) / α) * α := (div_mul_cancel₀ _ (ne_of_gt hα)).symm
      _ = r * α := by rw [hr]
      _ = α * r := by ring
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) hα.le
  have hm5 : (0 : ℝ) ≤ 2 * (m : ℝ) + 5 := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- ### bounds for `c` and its derivatives
  have hc0 : ∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t) := by
    intro t ht
    simpa only [iteratedDeriv_zero, Nat.zero_add, pow_one] using
      hb 0 (by norm_num : (0 : ℕ) ≤ 2) t ht
  have hc1 : ∀ t : ℝ, 0 < t → |deriv c t| ≤ A / (1 + t ^ 2) := by
    intro t ht
    simpa only [iteratedDeriv_one, Nat.reduceAdd] using hb 1 (by norm_num : (1 : ℕ) ≤ 2) t ht
  have hc2 : ∀ t : ℝ, 0 < t → |iteratedDeriv 2 c t| ≤ A / (1 + t ^ 3) := by
    intro t ht
    simpa only [Nat.reduceAdd] using hb 2 (by norm_num : (2 : ℕ) ≤ 2) t ht
  -- ### the second derivative, continuity and differentiability statements
  have hfun2 : (fun t : ℝ => iteratedDeriv 2 c t) = deriv (deriv c) := by
    funext t
    have h2 : (2 : ℕ) = 1 + 1 := by norm_num
    rw [h2, iteratedDeriv_succ, iteratedDeriv_one]
  have hcd : ContinuousOn (deriv c) (Set.Ioi (0 : ℝ)) :=
    hc.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcdd : ContinuousOn (deriv (deriv c)) (Set.Ioi (0 : ℝ)) :=
    ((hc.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioi
      (m := 0) (by norm_num)).continuousOn
  have hcont2 : ContinuousOn (fun t : ℝ => iteratedDeriv 2 c t) (Set.Ioi (0 : ℝ)) := by
    rw [hfun2]; exact hcdd
  have hderiv_c : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t := by
    intro t ht
    have hc1' : ContDiffOn ℝ 1 c (Set.Ioi (0 : ℝ)) := hc.of_le (by norm_num)
    have hdiff : DifferentiableAt ℝ c t :=
      ((contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).1 hc1').1.differentiableAt
        (Ioi_mem_nhds ht)
    exact hdiff.hasDerivAt
  have hderiv_d : ∀ t : ℝ, 0 < t → HasDerivAt (deriv c) (iteratedDeriv 2 c t) t := by
    intro t ht
    have hd1 : ContDiffOn ℝ 1 (deriv c) (Set.Ioi (0 : ℝ)) :=
      hc.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
    have hdiff : DifferentiableAt ℝ (deriv c) t :=
      ((contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).1 hd1).1.differentiableAt
        (Ioi_mem_nhds ht)
    have hpt : iteratedDeriv 2 c t = deriv (deriv c) t := by
      have h := congrFun hfun2 t
      simpa using h
    rw [hpt]
    exact hdiff.hasDerivAt
  -- ### the antiderivative and the two integrands
  let G : ℝ → ℝ := fun s => α * (s ^ (1 - r) * deriv c s) + (2 * (m : ℝ) + 5) * (s ^ (-r) * c s)
  let I : ℝ → ℝ :=
    fun s => (α * s ^ 2 * iteratedDeriv 2 c s + (5 + α) * s * deriv c s) * s ^ (-r - 1)
  let J : ℝ → ℝ := fun s => c s * s ^ (-r - 1)
  let Kc : ℝ := (2 * (m : ℝ) + 5) * r
  -- ### continuity of `I`, `J` on the tail
  have hsub : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hz.le
  have hcontJ : ContinuousOn J (Set.Ioi z) := by
    have h4 : ContinuousOn (fun t : ℝ => t ^ (-r - 1)) (Set.Ioi z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
    have h5 : ContinuousOn c (Set.Ioi z) := hc.continuousOn.mono hsub
    exact h5.mul h4
  have hcontI : ContinuousOn I (Set.Ioi z) := by
    have h1 : ContinuousOn (fun t : ℝ => iteratedDeriv 2 c t) (Set.Ioi z) := hcont2.mono hsub
    have h2 : ContinuousOn (deriv c) (Set.Ioi z) := hcd.mono hsub
    have h3 : ContinuousOn (fun t : ℝ => t ^ (-r - 1)) (Set.Ioi z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
    have h4a : ContinuousOn (fun t : ℝ => α * t ^ 2) (Set.Ioi z) :=
      continuousOn_const.mul (continuousOn_id.pow 2)
    have h4b : ContinuousOn (fun t : ℝ => (5 + α) * t) (Set.Ioi z) :=
      continuousOn_const.mul continuousOn_id
    have h4 : ContinuousOn
        (fun t : ℝ => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) (Set.Ioi z) :=
      (h4a.mul h1).add (h4b.mul h2)
    exact h4.mul h3
  -- ### integrability of `J`
  have hIntJ : IntegrableOn J (Set.Ioi z) := by
    rw [MeasureTheory.IntegrableOn]
    refine Integrable.mono' (g := fun t : ℝ => A * t ^ (-r - 2)) ?_ ?_ ?_
    · exact ((integrableOn_Ioi_rpow_iff hz).2 (by linarith)).const_mul A
    · exact hcontJ.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans hz ht
      have hAdiv : A / (1 + t) ≤ A / t := div_le_div_of_nonneg_left hA ht0 (by linarith)
      have hAeq : A / t * t ^ (-r - 1) = A * t ^ (-r - 2) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one t, mul_assoc, rpow_neg_one_mul ht0 r]
      rw [Real.norm_eq_abs]
      dsimp only [J]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc |c t| * t ^ (-r - 1)
          ≤ (A / t) * t ^ (-r - 1) :=
            mul_le_mul_of_nonneg_right (le_trans (hc0 t ht0) hAdiv)
              (Real.rpow_nonneg ht0.le _)
        _ = A * t ^ (-r - 2) := hAeq
  -- ### integrability of `I`
  have hIntI : IntegrableOn I (Set.Ioi z) := by
    rw [MeasureTheory.IntegrableOn]
    refine Integrable.mono' (g := fun t : ℝ => (2 * α + 5) * A * t ^ (-r - 2)) ?_ ?_ ?_
    · exact ((integrableOn_Ioi_rpow_iff hz).2 (by linarith)).const_mul ((2 * α + 5) * A)
    · exact hcontI.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans hz ht
      have hp : t ^ (-1 : ℝ) * t ^ (-r - 1) = t ^ (-r - 2) := rpow_neg_one_mul ht0 r
      have hI1 : |α * t ^ 2 * iteratedDeriv 2 c t| * t ^ (-r - 1) ≤ α * A * t ^ (-r - 2) := by
        have habs : |α * t ^ 2 * iteratedDeriv 2 c t| = α * t ^ 2 * |iteratedDeriv 2 c t| := by
          simp only [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg (pow_nonneg ht0.le 2)]
        rw [habs]
        have hdiv : t ^ 2 / (1 + t ^ 3) ≤ 1 / t := pow_div_one_add_pow_le ht0 2
        have hstep : α * t ^ 2 * (A / (1 + t ^ 3)) ≤ α * A * t ^ (-1 : ℝ) := by
          have he : α * t ^ 2 * (A / (1 + t ^ 3)) = α * A * (t ^ 2 / (1 + t ^ 3)) := by ring
          have he2 : α * A * (1 / t) = α * A * t ^ (-1 : ℝ) := by rw [one_div_eq_rpow]
          rw [he, ← he2]
          exact mul_le_mul_of_nonneg_left hdiv (mul_nonneg hα.le hA)
        have hle : α * t ^ 2 * |iteratedDeriv 2 c t| ≤ α * t ^ 2 * (A / (1 + t ^ 3)) :=
          mul_le_mul_of_nonneg_left (hc2 t ht0) (mul_nonneg hα.le (pow_nonneg ht0.le 2))
        calc α * t ^ 2 * |iteratedDeriv 2 c t| * t ^ (-r - 1)
            ≤ (α * t ^ 2 * (A / (1 + t ^ 3))) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg ht0.le _)
          _ ≤ (α * A * t ^ (-1 : ℝ)) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg ht0.le _)
          _ = α * A * t ^ (-r - 2) := by rw [mul_assoc, hp]
      have hI2 : |(5 + α) * t * deriv c t| * t ^ (-r - 1) ≤ (5 + α) * A * t ^ (-r - 2) := by
        have h5α : (0 : ℝ) ≤ 5 + α := by linarith
        have habs : |(5 + α) * t * deriv c t| = (5 + α) * t * |deriv c t| := by
          simp only [abs_mul, abs_of_nonneg h5α, abs_of_nonneg ht0.le]
        rw [habs]
        have hdiv : t / (1 + t ^ 2) ≤ 1 / t := by
          simpa only [pow_one] using pow_div_one_add_pow_le ht0 1
        have hstep : (5 + α) * t * (A / (1 + t ^ 2)) ≤ (5 + α) * A * t ^ (-1 : ℝ) := by
          have he : (5 + α) * t * (A / (1 + t ^ 2)) = (5 + α) * A * (t / (1 + t ^ 2)) := by ring
          have he2 : (5 + α) * A * (1 / t) = (5 + α) * A * t ^ (-1 : ℝ) := by rw [one_div_eq_rpow]
          rw [he, ← he2]
          exact mul_le_mul_of_nonneg_left hdiv (mul_nonneg h5α hA)
        have hle : (5 + α) * t * |deriv c t| ≤ (5 + α) * t * (A / (1 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left (hc1 t ht0) (mul_nonneg h5α ht0.le)
        calc (5 + α) * t * |deriv c t| * t ^ (-r - 1)
            ≤ ((5 + α) * t * (A / (1 + t ^ 2))) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg ht0.le _)
          _ ≤ ((5 + α) * A * t ^ (-1 : ℝ)) * t ^ (-r - 1) :=
              mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg ht0.le _)
          _ = (5 + α) * A * t ^ (-r - 2) := by rw [mul_assoc, hp]
      rw [Real.norm_eq_abs]
      dsimp only [I]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc |α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t| * t ^ (-r - 1)
          ≤ (|α * t ^ 2 * iteratedDeriv 2 c t| + |(5 + α) * t * deriv c t|) * t ^ (-r - 1) :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.rpow_nonneg ht0.le _)
        _ = |α * t ^ 2 * iteratedDeriv 2 c t| * t ^ (-r - 1)
              + |(5 + α) * t * deriv c t| * t ^ (-r - 1) := by ring
        _ ≤ α * A * t ^ (-r - 2) + (5 + α) * A * t ^ (-r - 2) := add_le_add hI1 hI2
        _ = (2 * α + 5) * A * t ^ (-r - 2) := by ring
  have hIntKJ : IntegrableOn (fun t : ℝ => I t - Kc * J t) (Set.Ioi z) :=
    hIntI.sub (hIntJ.const_mul Kc)
  -- ### the derivative of `G`
  have hderivG : ∀ t : ℝ, 0 < t → HasDerivAt G (I t - Kc * J t) t := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht
    have hpow1 : HasDerivAt (fun s : ℝ => s ^ (1 - r)) ((1 - r) * t ^ (1 - r - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl htne)
    have hpow2 : HasDerivAt (fun s : ℝ => s ^ (-r)) ((-r) * t ^ (-r - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl htne)
    have h1 : HasDerivAt (fun s : ℝ => α * (s ^ (1 - r) * deriv c s))
        (α * ((1 - r) * t ^ (1 - r - 1) * deriv c t + t ^ (1 - r) * iteratedDeriv 2 c t))
        t :=
      (hpow1.mul (hderiv_d t ht)).const_mul α
    have h2 : HasDerivAt (fun s : ℝ => (2 * (m : ℝ) + 5) * (s ^ (-r) * c s))
        ((2 * (m : ℝ) + 5) * ((-r) * t ^ (-r - 1) * c t + t ^ (-r) * deriv c t)) t :=
      (hpow2.mul (hderiv_c t ht)).const_mul (2 * (m : ℝ) + 5)
    have hkey : α * ((1 - r) * t ^ (1 - r - 1) * deriv c t + t ^ (1 - r) * iteratedDeriv 2 c t)
        + (2 * (m : ℝ) + 5) * ((-r) * t ^ (-r - 1) * c t + t ^ (-r) * deriv c t)
        = I t - Kc * J t := by
      have hw1 : t ^ (1 - r - 1) = t * t ^ (-r - 1) := by
        rw [show 1 - r - 1 = 1 + (-r - 1) by ring, Real.rpow_add ht 1 (-r - 1),
          Real.rpow_one]
      have hw2 : t ^ (1 - r) = t ^ 2 * t ^ (-r - 1) := by
        rw [show 1 - r = 2 + (-r - 1) by ring, Real.rpow_add ht 2 (-r - 1)]
        rw [Real.rpow_ofNat]
      have hw3 : t ^ (-r) = t * t ^ (-r - 1) := by
        calc t ^ (-r) = t ^ (1 + (-r - 1)) := congrArg (fun p : ℝ => t ^ p) (by ring)
          _ = t ^ 1 * t ^ (-r - 1) := Real.rpow_add ht 1 (-r - 1)
          _ = t * t ^ (-r - 1) := by simp only [Real.rpow_one]
      dsimp only [I, J, Kc]
      rw [hw1, hw2, hw3]
      rw [hrr]
      ring
    exact (h1.add h2).congr_deriv hkey
  -- ### the limit of `G` at infinity
  have hlim : Tendsto G atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (g := fun t : ℝ => (α * A + (2 * (m : ℝ) + 5) * A) * t ^ (-1 : ℝ))
      (Eventually.of_forall fun t => norm_nonneg (G t)) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht1
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
      have h1 : t ^ (1 - r) * (A / (1 + t ^ 2)) ≤ A * t ^ (-r - 1) := by
        have hdiv : t ^ (1 - r) / (1 + t ^ 2) ≤ t ^ (1 - r) / t ^ 2 :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) (pow_pos ht0 2) (by linarith)
        have he : t ^ (1 - r) / t ^ 2 = t ^ (-r - 1) := by
          rw [rpowDivNat ht0 (1 - r) 2,
            show (1 - r) - ((2 : ℕ) : ℝ) = -r - 1 by push_cast; ring]
        have hmul : t ^ (1 - r) * (A / (1 + t ^ 2)) = A * (t ^ (1 - r) / (1 + t ^ 2)) := by ring
        rw [hmul]
        calc A * (t ^ (1 - r) / (1 + t ^ 2)) ≤ A * (t ^ (1 - r) / t ^ 2) :=
              mul_le_mul_of_nonneg_left hdiv hA
          _ = A * t ^ (-r - 1) := by rw [he]
      have h2 : t ^ (-r) * (A / (1 + t)) ≤ A * t ^ (-r - 1) := by
        have hdiv : t ^ (-r) / (1 + t) ≤ t ^ (-r) / t ^ 1 := by
          simpa only [pow_one] using
            div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) ht0 (by linarith)
        have he : t ^ (-r) / t ^ 1 = t ^ (-r - 1) := by
          rw [rpowDivNat ht0 (-r) 1,
            show (-r) - ((1 : ℕ) : ℝ) = -r - 1 by push_cast; ring]
        have hmul : t ^ (-r) * (A / (1 + t)) = A * (t ^ (-r) / (1 + t)) := by ring
        rw [hmul]
        calc A * (t ^ (-r) / (1 + t)) ≤ A * (t ^ (-r) / t ^ 1) :=
              mul_le_mul_of_nonneg_left hdiv hA
          _ = A * t ^ (-r - 1) := by rw [he]
      have hA1 : |α * (t ^ (1 - r) * deriv c t)| = α * (t ^ (1 - r) * |deriv c t|) := by
        simp only [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hA2 : |(2 * (m : ℝ) + 5) * (t ^ (-r) * c t)|
          = (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := by
        simp only [abs_mul, abs_of_nonneg hm5, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hG : ‖G t‖ ≤ α * (t ^ (1 - r) * |deriv c t|)
          + (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := by
        rw [Real.norm_eq_abs]
        dsimp only [G]
        calc |α * (t ^ (1 - r) * deriv c t) + (2 * (m : ℝ) + 5) * (t ^ (-r) * c t)|
            ≤ |α * (t ^ (1 - r) * deriv c t)|
              + |(2 * (m : ℝ) + 5) * (t ^ (-r) * c t)| := abs_add_le _ _
          _ = α * (t ^ (1 - r) * |deriv c t|) + (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := by
              rw [hA1, hA2]
      calc ‖G t‖
          ≤ α * (t ^ (1 - r) * |deriv c t|) + (2 * (m : ℝ) + 5) * (t ^ (-r) * |c t|) := hG
        _ ≤ α * (t ^ (1 - r) * (A / (1 + t ^ 2)))
              + (2 * (m : ℝ) + 5) * (t ^ (-r) * (A / (1 + t))) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hc1 t ht0) (Real.rpow_nonneg ht0.le _)) hα.le
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hc0 t ht0) (Real.rpow_nonneg ht0.le _)) hm5
        _ ≤ α * (A * t ^ (-r - 1)) + (2 * (m : ℝ) + 5) * (A * t ^ (-r - 1)) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left h1 hα.le
            · exact mul_le_mul_of_nonneg_left h2 hm5
        _ = (α + (2 * (m : ℝ) + 5)) * A * t ^ (-r - 1) := by ring
        _ ≤ (α + (2 * (m : ℝ) + 5)) * A * t ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith))
              (mul_nonneg (by linarith) hA)
        _ = (α * A + (2 * (m : ℝ) + 5) * A) * t ^ (-1 : ℝ) := by ring
    · have hfun : (fun t : ℝ => (α * A + (2 * (m : ℝ) + 5) * A) * t ^ (-1 : ℝ))
          = fun t : ℝ => (α * A + (2 * (m : ℝ) + 5) * A) * t⁻¹ := by
        funext t
        rw [Real.rpow_neg_one]
      rw [hfun]
      simpa using tendsto_inv_atTop_zero.const_mul (α * A + (2 * (m : ℝ) + 5) * A)
  -- ### the fundamental theorem of calculus on `(z, ∞)`
  have hftc : ∫ t in Set.Ioi z, (I t - Kc * J t) = 0 - G z :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (a := z) (f := G) (f' := fun t => I t - Kc * J t)
      (fun t ht => hderivG t (lt_of_lt_of_le hz ht)) hIntKJ hlim
  have hsplit : (∫ t in Set.Ioi z, (I t - Kc * J t))
      = (∫ t in Set.Ioi z, I t) - Kc * (∫ t in Set.Ioi z, J t) := by
    have h1 : (∫ t in Set.Ioi z, (I t - Kc * J t))
        = (∫ t in Set.Ioi z, I t) - (∫ t in Set.Ioi z, Kc * J t) := by
      simpa only [smul_eq_mul] using integral_sub hIntI (hIntJ.const_mul Kc)
    have h2 : (∫ t in Set.Ioi z, Kc * J t) = Kc * (∫ t in Set.Ioi z, J t) :=
      integral_const_mul Kc J
    rw [h1, h2]
  have hmain : (∫ t in Set.Ioi z, I t) = -G z + Kc * (∫ t in Set.Ioi z, J t) := by
    linarith [hftc, hsplit]
  have hfinal : (∫ t in Set.Ioi z, I t)
      = -α * z ^ (1 - r) * deriv c z - (2 * (m : ℝ) + 5) * z ^ (-r) * c z
        + (2 * (m : ℝ) + 5) * r * ∫ t in Set.Ioi z, c t * t ^ (-r - 1) := by
    rw [hmain]
    dsimp only [G, Kc, J]
    ring
  have hgoal_eq : (∫ t in Set.Ioi z, I t)
      = ∫ t in Set.Ioi z,
          (α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) * t ^ (-r - 1) := rfl
  rw [← hgoal_eq]
  exact hfinal

end Work.FTS.PhiStar.RadGreenSupport
end
end
