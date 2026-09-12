import ChallengeDeps
import Mathlib.Analysis.Calculus.MeanValue
open OptimalMoebius
open Topology ContDiff
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 0
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Elementary consequences of `IsMoebiusEmbedding`

Any start toward Schwartz's Main Theorem (`a > √3` for every smooth embedded
paper Möbius band of aspect ratio `a`) has to extract metric facts from the
definition of `IsMoebiusEmbedding`:  the map `f` is `C∞` on the closed unit
strip, its within-derivative is a linear isometry at every point of the strip,
and `f` is periodic and injective on a fundamental domain.

This module records the basic analytic consequences that do not require the
deep geometry of the paper:
  * the unit strip is convex;
  * the within-derivative has operator norm `≤ 1` at every point of the strip;
  * `f` is distance non-increasing on the strip (Lipschitz with constant 1),
    by the mean value inequality on the convex strip.
-/

noncomputable section
namespace Submission.PaperBand

/-- The unit strip `{x | x 0 ∈ Icc 0 1}` is convex. -/
lemma unitStrip_convex : Convex ℝ unitStrip := by
  unfold unitStrip Convex
  intro x hx y hy a b ha hb hab
  constructor
  · have h1 : 0 ≤ a * (x 0) + b * (y 0) := by
      nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
    simpa using h1
  · have h2 : a * (x 0) + b * (y 0) ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]
    simpa using h2

/-- A Moebius embedding is differentiable (within the strip) at every point of
the unit strip. -/
lemma embedding_differentiableOn {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    DifferentiableOn ℝ f unitStrip :=
  hf.smooth.differentiableOn (by simp)

/-- The within-derivative of a Moebius embedding preserves norms at every point
of the unit strip:  it is a linear isometry. -/
lemma fderiv_norm_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, ∀ v : ℝ², ‖fderivWithin ℝ f unitStrip x v‖ = ‖v‖ := by
  intro x hx v
  exact (hf.isometry x hx).norm_map_of_map_zero (map_zero _) v

/-- The operator norm of the within-derivative is at most `1` on the strip. -/
lemma fderiv_opnorm_le_one {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, ‖fderivWithin ℝ f unitStrip x‖ ≤ 1 := by
  intro x hx
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : 0 ≤ (1:ℝ))]
  intro v
  have hn := fderiv_norm_eq hf x hx v
  rw [hn]
  simp

/-- `f` is distance non-increasing on the unit strip:
`‖f y - f x‖ ≤ ‖y - x‖` for all `x, y` in the strip. -/
lemma embedding_lipschitz {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ ⦃x⦄, x ∈ unitStrip → ∀ ⦃y⦄, y ∈ unitStrip → ‖f y - f x‖ ≤ ‖y - x‖ := by
  intro x hx y hy
  have hle := Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (f := f) (s := unitStrip) (x := x) (y := y)
    (embedding_differentiableOn hf) (fderiv_opnorm_le_one hf) unitStrip_convex hx hy
  simpa using hle

end Submission.PaperBand
end
