import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.HardyRightNoCont
import Submission.Work.Elliptic.IntegrableSqMulW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary bounds for the weight `w z = (1+z)² / z²` on `(1,∞)`

On `(1,∞)` one has `1 ≤ w z ≤ 4`: indeed `w z = (1 + 1/z)²` and `1 < 1 + 1/z < 2`
for `z > 1`.  Consequently `w z ² ≤ 16` there. -/

/-- On `(1,∞)` the weight `w z = (1+z)²/z²` is at least `1`. -/
theorem one_le_w_of_one_lt {z : ℝ} (hz : 1 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  nlinarith

/-- On `(1,∞)` the weight `w z = (1+z)²/z²` is at most `4`. -/
theorem w_le_four_of_one_lt {z : ℝ} (hz : 1 < z) : Work.Spaces.w z ≤ 4 := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, div_le_iff₀ hz2]
  have h1 : 1 + z ≤ 2 * z := by linarith
  have h2 : (0 : ℝ) ≤ 1 + z := by linarith
  nlinarith [mul_self_le_mul_self h2 h1]

/-- On `(1,∞)` the square of the weight is at most `16`. -/
theorem w_sq_le_sixteen_of_one_lt {z : ℝ} (hz : 1 < z) : (Work.Spaces.w z) ^ 2 ≤ 16 := by
  have h := w_le_four_of_one_lt hz
  nlinarith [one_le_w_of_one_lt hz]

/-- Weighted Hardy inequality on the right half-line: for `U` differentiable on `(1,∞)` with derivative `-(f z / z)`, tending to `0` at `+∞`, and with `f²w²` integrable on `(1,∞)`, one has `U²w²` integrable on `(1,∞)` with `∫_{(1,∞)} U²w² ≤ 107 ∫_{(1,∞)} f²w²`. Here `w z = (1+z)²/z²` is `Work.Spaces.w`. Intended route: `(z U' z)² = (f z)²`, the dual Hardy inequality `∫_{(1,∞)} U² ≤ 6 ∫_{(1,∞)} (zU')²`, the pointwise bounds `1 ≤ w ≤ 4` on `(1,∞)` (so `w² ≤ 16`), giving the constant `96 ≤ 107`. -/
theorem HardyRightW (f U : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1 : ℝ), HasDerivAt U (-(f z / z)) z)
    (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) ∧
      ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 107 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  -- `f²` is integrable on `(1,∞)` and `∫ f² ≤ ∫ f² w²`.
  obtain ⟨hf2int, hf2le⟩ := IntegrableSqMulW hint
  -- The pointwise bounds for the weight.
  have hw1 : ∀ z ∈ Set.Ioi (1 : ℝ), 1 ≤ Work.Spaces.w z := fun z hz => one_le_w_of_one_lt hz
  have hw4sq : ∀ z ∈ Set.Ioi (1 : ℝ), (Work.Spaces.w z) ^ 2 ≤ 16 :=
    fun z hz => w_sq_le_sixteen_of_one_lt hz
  -- The derivative prescribed by the hypotheses.
  set U' : ℝ → ℝ := fun z => -(f z / z) with hU'def
  -- On `(1,∞)` one has `(z U' z)² = (f z)²`.
  have hzeq : EqOn (fun z : ℝ => (z * U' z) ^ 2) (fun z : ℝ => (f z) ^ 2) (Set.Ioi 1) := by
    intro z hz
    simp only [hU'def]
    have hz0 : z ≠ 0 := ne_of_gt (lt_trans one_pos hz)
    have h : z * (-(f z / z)) = -(f z) := by field_simp
    rw [h]; ring
  have hzeq_int : ∫ z in Set.Ioi (1 : ℝ), (z * U' z) ^ 2 = ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioi hzeq
  -- Hence `(z U' z)²` is integrable on `(1,∞)`.
  have hU'int : MeasureTheory.IntegrableOn (fun z : ℝ => (z * U' z) ^ 2) (Set.Ioi 1) :=
    hf2int.congr_fun hzeq.symm measurableSet_Ioi
  -- The dual Hardy inequality on `(1,∞)`.
  obtain ⟨hU2int, hU2le⟩ := HardyRightNoCont U U' hderiv htend hU'int
  have hU2le' : ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 ≤ 6 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 := by
    rw [hzeq_int] at hU2le
    exact hU2le
  -- Nonnegativity of the right-hand side.
  have hF2nn : 0 ≤ ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- `U² w²` is integrable, being `U²` times the bounded function `w²`.
  have hU2w2int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
    have hg : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (volume.restrict (Set.Ioi 1)) := by
      have hcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
        apply ContinuousOn.pow
        apply ContinuousOn.div
        · exact (continuousOn_const.add continuousOn_id).pow 2
        · exact continuousOn_id.pow 2
        · intro z hz
          have hz0 : (0 : ℝ) < z := lt_trans one_pos hz
          positivity
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    rw [MeasureTheory.IntegrableOn] at hU2int ⊢
    exact hU2int.mul_bdd hg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hw4sq z hz)
  -- `∫ U² w² ≤ 16 ∫ U²`.
  have hS : ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ 16 * ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 := by
    rw [MeasureTheory.IntegrableOn] at hU2int
    have h16 : IntegrableOn (fun z : ℝ => 16 * (U z) ^ 2) (Set.Ioi (1 : ℝ)) := hU2int.const_mul 16
    have hmono := setIntegral_mono_on hU2w2int h16 measurableSet_Ioi
      (fun z hz => by have h := hw4sq z hz; nlinarith [sq_nonneg (U z)])
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  refine ⟨hU2w2int, ?_⟩
  calc ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ 16 * ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 := hS
    _ ≤ 16 * (6 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2) := by linarith [hU2le']
    _ = 96 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 := by ring
    _ ≤ 96 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by linarith [hf2le]
    _ ≤ 107 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by nlinarith [hF2nn]

end Work.Elliptic
