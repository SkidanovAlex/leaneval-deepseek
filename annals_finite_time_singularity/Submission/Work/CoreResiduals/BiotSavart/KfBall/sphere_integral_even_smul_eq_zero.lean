import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.LWP.Defs

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
