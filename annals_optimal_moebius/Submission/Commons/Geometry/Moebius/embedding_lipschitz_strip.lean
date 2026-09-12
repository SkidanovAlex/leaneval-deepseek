import Mathlib.Analysis.Calculus.MeanValue
import Submission.Commons.Geometry.Moebius.escape_of_shared_endpoint

open Topology ContDiff
set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Commons.Geometry.Moebius

open Commons.PaperMoebius

/-- The unit strip `{x | x 0 ∈ Icc 0 1}` is convex. -/
lemma unitStrip_convex : Convex ℝ unitStrip := by
  unfold unitStrip Convex
  intro x hx y hy u v hu hv huv
  constructor
  · have h1 : 0 ≤ u * (x 0) + v * (y 0) :=
      add_nonneg (mul_nonneg hu hx.1) (mul_nonneg hv hy.1)
    simpa using h1
  · have h2 : u * (x 0) + v * (y 0) ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hx.2 hu, mul_le_mul_of_nonneg_left hy.2 hv]
    simpa using h2

/-- A Möbius embedding is differentiable (within the strip) at every point of
the unit strip. -/
lemma embedding_differentiableOn {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    DifferentiableOn ℝ f unitStrip :=
  hf.smooth.differentiableOn (by simp)

/-- The within-derivative of a Möbius embedding preserves norms at every point
of the unit strip: it is a linear isometry. -/
lemma fderiv_norm_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, ∀ v : ℝ², ‖fderivWithin ℝ f unitStrip x v‖ = ‖v‖ := by
  intro x hx v
  exact (hf.isometry x hx).norm_map_of_map_zero (map_zero _) v

/-- The operator norm of the within-derivative is at most `1` on the strip. -/
lemma fderiv_opnorm_le_one {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ unitStrip, ‖fderivWithin ℝ f unitStrip x‖ ≤ 1 := by
  intro x hx
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : 0 ≤ (1 : ℝ))]
  intro v
  rw [fderiv_norm_eq hf x hx v]
  simp

/-- `f` is distance non-increasing on the unit strip:
`‖f y - f x‖ ≤ ‖y - x‖` for all `x, y` in the strip. -/
theorem embedding_lipschitz_strip {a : ℝ} {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hf : Commons.PaperMoebius.IsMoebiusEmbedding a f) :
    ∀ ⦃x⦄, x ∈ Commons.PaperMoebius.unitStrip → ∀ ⦃y⦄, y ∈ Commons.PaperMoebius.unitStrip →
      ‖f y - f x‖ ≤ ‖y - x‖ := by
  intro x hx y hy
  have hle := Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (f := f) (s := unitStrip) (x := x) (y := y)
    (embedding_differentiableOn hf) (fderiv_opnorm_le_one hf) unitStrip_convex hx hy
  simpa using hle

end Commons.Geometry.Moebius
