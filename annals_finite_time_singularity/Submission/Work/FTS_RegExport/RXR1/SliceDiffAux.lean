import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.SliceDiffAux`

Auxiliary vocabulary for `Work.FTS_RegExport.RXR1.slice_diff_weighted`.

The target lemma bounds the mixed slots of order `≤ 1` of the *difference of two slices*
`slice g τ - slice g τ'` of a `LimApprox` family by

  `C · (z^{3/2}/(1+z)²) · |τ - τ'|`

uniformly on the open quadrant.  The single analytic input is the weighted pointwise bound
`hw` on the mixed slots of order `≤ 2` of any profile which is `C^∞` on the open quadrant and
honest in `ℋ⁴` and in the boundary traces.  This file fixes

* `SliceW` — the radial weight `z^{3/2}/(1+z)²` (an `abbrev`, so that it is syntactically the
  same expression as the one appearing in the hypothesis `hw`);
* `HwBnd β C` — the inner part of that hypothesis, as a predicate;
* the two definitional identities `mixed 1 0 f = z·∂_z f` and `mixed 0 1 f = sin 2θ·∂_θ f`;
* the elementary consequences of `SliceW` used to make the bounds uniform on a compact
  subinterval of `(0,∞)`.
-/

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_RegExport.RXR1

/-- The radial weight `z^{3/2}/(1+z)²` of the weighted slot bound. -/
abbrev SliceW (z : ℝ) : ℝ := z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2

/-- **The weighted slot bound**: the inner part of the hypothesis `hw` of the target lemma.
`C` bounds the mixed slots of order `≤ 2` of a class-`C⁴` profile by the weight `SliceW` times
its `ℋ⁴`-norm. -/
def HwBnd (β C : ℝ) : Prop :=
  ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem β 4 f →
    Work.FTS.Nonlin.BdryTraces β 4 f →
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f

lemma SliceW_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ SliceW z :=
  div_nonneg (Real.rpow_nonneg hz _) (by positivity)

lemma SliceW_pos {z : ℝ} (hz : 0 < z) : 0 < SliceW z :=
  div_pos (Real.rpow_pos_of_pos hz _) (by positivity)

/-- `mixed 1 0 f = z · ∂_z f` (definitional). -/
lemma mixed_one_zero_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 f z θ = z * Work.Spaces.pzIter 1 f z θ := rfl

/-- `mixed 0 1 f = sin(2θ) · ∂_θ f` (definitional). -/
lemma mixed_zero_one_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 f z θ = Real.sin (2 * θ) * Work.Spaces.pthIter 1 f z θ := rfl

/-- `SliceW z / z = z^{1/2}/(1+z)²`. -/
lemma SliceW_div_eq {z : ℝ} (hz : 0 < z) :
    SliceW z / z = z ^ ((1 : ℝ) / 2) / (1 + z) ^ 2 := by
  have h : z ^ ((3 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * z := by
    rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hz,
      Real.rpow_one]
  simp only [SliceW]
  rw [h]
  field_simp

/-- `SliceW z / (z·z) = z^{-1/2}/(1+z)²`. -/
lemma SliceW_div_sq_eq {z : ℝ} (hz : 0 < z) :
    SliceW z / (z * z) = z ^ (-(1 : ℝ) / 2) / (1 + z) ^ 2 := by
  have h : z ^ ((3 : ℝ) / 2) = z ^ (-(1 : ℝ) / 2) * (z * z) := by
    rw [show ((3 : ℝ) / 2) = -(1 : ℝ) / 2 + 1 + 1 by norm_num, Real.rpow_add hz,
      Real.rpow_add hz, Real.rpow_one]
    ring
  simp only [SliceW]
  rw [h]
  field_simp

/-- On `(0, 2z+1)` the weight `SliceW (·)/·` is bounded by `√(2z+1)`. -/
lemma SliceW_div_le_sqrt {z z' : ℝ} (hz : 0 < z) (hz' : z / 2 ≤ z') (hz'' : z' ≤ 2 * z + 1) :
    SliceW z' / z' ≤ Real.sqrt (2 * z + 1) := by
  have hz'0 : 0 < z' := lt_of_lt_of_le (by linarith) hz'
  rw [SliceW_div_eq hz'0, Real.sqrt_eq_rpow]
  have h1 : z' ^ ((1 : ℝ) / 2) / (1 + z') ^ 2 ≤ z' ^ ((1 : ℝ) / 2) / 1 := by
    refine div_le_div_of_nonneg_left (Real.rpow_nonneg hz'0.le _) one_pos ?_
    nlinarith
  rw [div_one] at h1
  exact h1.trans (Real.rpow_le_rpow hz'0.le hz'' (by norm_num))

/-- On `(z/2, ∞)` the weight `SliceW (·)/(·)²` is bounded by `(z/2)^{-1/2}`. -/
lemma SliceW_div_sq_le {z z' : ℝ} (hz : 0 < z) (hz' : z / 2 ≤ z') :
    SliceW z' / (z' * z') ≤ (z / 2) ^ (-(1 : ℝ) / 2) := by
  have hz'0 : 0 < z' := lt_of_lt_of_le (by linarith) hz'
  rw [SliceW_div_sq_eq hz'0]
  have h1 : z' ^ (-(1 : ℝ) / 2) / (1 + z') ^ 2 ≤ z' ^ (-(1 : ℝ) / 2) / 1 := by
    refine div_le_div_of_nonneg_left (Real.rpow_nonneg hz'0.le _) one_pos ?_
    nlinarith
  rw [div_one] at h1
  exact h1.trans (Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < z / 2) hz'
    (by norm_num))

end Work.FTS_RegExport.RXR1
