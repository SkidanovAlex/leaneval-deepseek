import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.Basic
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.KH.SymAMoments` — the bump moments and the explicit threshold `ε₀`

This module carries the two scalar constants on which the FS-parameter instance of the two-cut
symbol comparison (`Work.BoseFixB1.KH.symA_fsParams`) depends, plus the explicit threshold

    `ε₀ = δ^{323}`,   `δ = min (1/2) (min (M₁+1)⁻¹ (32M₂+1)⁻¹)`,

where `M₁`, `M₂` are the first two moments of the squared bump profile

    `M₁ = (2π)⁻³ ∫ profHat(t)² ‖t‖ dt`,   `M₂ = (2π)⁻³ ∫ profHat(t)² ‖t‖² dt`.

The diluteness enters the whole comparison only through `t = μ(a v)³`, and FS's parameters are
`fsParams t`, so `s = fsParams t . s = t^{1/323}`; `t ≤ ε₀ = δ^{323}` is exactly `s ≤ δ`, and `δ`
was chosen so that `s ≤ δ` gives, with no further arithmetic input,

* `d = s⁶ ≤ 1/2` (from `s ≤ 1/2`),
* `eT = s^{23/4} ≤ 1/2` (from `s ≤ 1/2`),
* `M₁ ≤ 1/s` (from `s ≤ (M₁+1)⁻¹`),
* `8M₂ ≤ (1−d)²/s²` (from `s ≤ (32M₂+1)⁻¹`, which gives `32M₂ s² ≤ s ≤ 1/2 ≤ 1/4·4`).

These are the four hypotheses of `Work.BoseFixB1.symA_fsKinCoeff_mix_scaled` (besides positivity)
at FS's parameters; see `Work.BoseFixB1.KH.fsParams_small_criteria` in
`Submission/Work/BoseFixB1/KH/SymACriteria.lean` for their proof.

The `min` with `(M₁+1)⁻¹`/`(32M₂+1)⁻¹` (rather than `1/M₁`, `1/(32M₂)`) makes `δ` positive
*unconditionally*, using only `0 ≤ M₁`, `0 ≤ M₂`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Work.BoseFixB1.KH

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The first moment `M₁ = (2π)⁻³ ∫ profHat(t)² ‖t‖ dt` of the squared bump profile. -/
def symAMom1 : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : R3, (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖

/-- The second moment `M₂ = (2π)⁻³ ∫ profHat(t)² ‖t‖² dt` of the squared bump profile. -/
def symAMom2 : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : R3, (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2

lemma symAMom1_nonneg : 0 ≤ symAMom1 := by
  rw [symAMom1]
  exact mul_nonneg (by positivity)
    (integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (norm_nonneg _)))

lemma symAMom2_nonneg : 0 ≤ symAMom2 := by
  rw [symAMom2]
  exact mul_nonneg (by positivity)
    (integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- The small scale `δ`: the threshold for FS's `s = (μa³)^{1/323}`. -/
def symASmallScale : ℝ :=
  min (1 / 2) (min ((symAMom1 + 1)⁻¹) ((32 * symAMom2 + 1)⁻¹))

lemma symASmallScale_pos : 0 < symASmallScale := by
  rw [symASmallScale]
  refine lt_min (by norm_num) (lt_min ?_ ?_)
  · exact inv_pos.mpr (by linarith [symAMom1_nonneg])
  · exact inv_pos.mpr (by linarith [symAMom2_nonneg])

lemma symASmallScale_le_half : symASmallScale ≤ 1 / 2 := min_le_left _ _

lemma symASmallScale_le_mom1 : symASmallScale ≤ (symAMom1 + 1)⁻¹ :=
  le_trans (min_le_right _ _) (min_le_left _ _)

lemma symASmallScale_le_mom2 : symASmallScale ≤ (32 * symAMom2 + 1)⁻¹ :=
  le_trans (min_le_right _ _) (min_le_right _ _)

lemma symASmallScale_le_one : symASmallScale ≤ 1 := by
  linarith [symASmallScale_le_half]

/-- The explicit threshold `ε₀ = δ^{323}` for the diluteness `μ(a v)³`. -/
def symAEps0 : ℝ := symASmallScale ^ (323 : ℝ)

lemma symAEps0_pos : 0 < symAEps0 := Real.rpow_pos_of_pos symASmallScale_pos _

end Work.BoseFixB1.KH
