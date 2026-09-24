import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant

/-!
# The Fejér-kernel majorant and the exponential sum `Σ_{t∈W} e^{itu}`

Auxiliary definitions and elementary facts for
`Work.GM.Energy.RMoments.Rfun_integral_pow4`.

The point of the Fejér kernel `ψ(u) = (2π)⁻¹ sinc(u/2)²` is that it is nonnegative, bounded below
by a positive constant on `[0, log 2]`, and band limited: its Fourier transform is the triangle
function `tri` (supported in `[-1,1]`).  This is what converts an integral of `‖R‖⁴` over
`v ∈ [1,2]` (`u = log v ∈ [0, log 2]`) into the additive energy count.
-/

namespace Work.GM.Energy.RMoments

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

/-- The exponential sum `Σ_{t ∈ W} e^{i t u}`; it equals `Rfun W (e^u)`. -/
noncomputable def expSum (W : Finset ℝ) (u : ℝ) : ℂ :=
  ∑ t ∈ W, cexp (Complex.I * ((t * u : ℝ) : ℂ))

/-- The Fejér kernel `ψ(u) = (2π)⁻¹ sinc(u/2)²`. -/
noncomputable def fejerK (u : ℝ) : ℝ := (2 * Real.pi)⁻¹ * Real.sinc (u / 2) ^ 2

/-- The quadruple sum-difference `q₁ + q₂ - q₃ - q₄` (the expression appearing in `energy`). -/
def sumdiff (q : ℝ × ℝ × ℝ × ℝ) : ℝ := q.1 + q.2.1 - q.2.2.1 - q.2.2.2

lemma expSum_apply (W : Finset ℝ) (u : ℝ) :
    expSum W u = ∑ t ∈ W, cexp (Complex.I * ((t * u : ℝ) : ℂ)) := rfl

@[simp] lemma expSum_empty (u : ℝ) : expSum ∅ u = 0 := by simp [expSum]

lemma continuous_expSum (W : Finset ℝ) : Continuous (expSum W) := by
  unfold expSum
  exact continuous_finsetSum _ (fun t _ => by fun_prop)

lemma norm_expSum_le_card (W : Finset ℝ) (u : ℝ) : ‖expSum W u‖ ≤ (W.card : ℝ) := by
  calc ‖expSum W u‖ ≤ ∑ t ∈ W, ‖cexp (Complex.I * ((t * u : ℝ) : ℂ))‖ := by
        unfold expSum; exact norm_sum_le _ _
    _ = ∑ t ∈ W, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
    _ = (W.card : ℝ) := by simp

lemma fejerK_nonneg (u : ℝ) : 0 ≤ fejerK u := by
  unfold fejerK
  positivity

lemma fejerK_le_const (u : ℝ) : fejerK u ≤ (2 * Real.pi)⁻¹ := by
  unfold fejerK
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have h1 : Real.sinc (u / 2) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (Real.abs_sinc_le_one (u / 2))
  calc (2 * Real.pi)⁻¹ * Real.sinc (u / 2) ^ 2 ≤ (2 * Real.pi)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr h2π.le)
    _ = (2 * Real.pi)⁻¹ := mul_one _

lemma fejerK_continuous : Continuous fejerK := by
  unfold fejerK; fun_prop

/-- `fejerK` is bounded below by `1/(4π)` on `[0, log 2]`. -/
lemma fejerK_lower {u : ℝ} (hu : u ∈ Set.Icc 0 (Real.log 2)) :
    (4 * Real.pi)⁻¹ ≤ fejerK u := by
  have hlog2 : Real.log 2 ≤ Real.pi / 2 := by
    have h1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans_le (by norm_num)
    nlinarith [Real.pi_gt_three]
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have hu2 : |u / (2 * Real.pi)| ≤ 1 / 4 := by
    have huabs : |u| ≤ Real.log 2 := by rw [abs_of_nonneg hu.1]; exact hu.2
    rw [abs_div, abs_of_pos h2π, div_le_iff₀ h2π]
    nlinarith [huabs, hlog2]
  have hsinc := Commons.Analysis.Fourier.sinc_pi_sq_lower_bound hu2
  have hsinc' : (1:ℝ) / 2 ≤ Real.sinc (u / 2) ^ 2 := by
    convert hsinc using 2
    field_simp
  have h4 : (4 * Real.pi)⁻¹ = (2 * Real.pi)⁻¹ * (1 / 2) := by
    field_simp; ring
  rw [h4, show fejerK u = (2 * Real.pi)⁻¹ * Real.sinc (u / 2) ^ 2 from rfl]
  exact mul_le_mul_of_nonneg_left hsinc' (inv_nonneg.mpr h2π.le)

/-- `fejerK` is integrable. -/
lemma fejerK_integrable : Integrable fejerK := by
  have hpi : Integrable (fun y : ℝ => Real.sinc (Real.pi * y) ^ 2) :=
    Commons.Analysis.Fourier.integrable_sinc_pi_sq
  have h1 : Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
    have h := hpi.comp_mul_left' (R := (Real.pi)⁻¹) (inv_ne_zero Real.pi_ne_zero)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    show Real.sinc (Real.pi * (Real.pi⁻¹ * x)) ^ 2 = Real.sinc x ^ 2
    rw [mul_inv_cancel_left₀ Real.pi_ne_zero]
  have hhalf : Integrable (fun u : ℝ => Real.sinc (u / 2) ^ 2) := by
    have h := h1.comp_mul_left' (R := (2:ℝ)⁻¹) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    show Real.sinc ((2:ℝ)⁻¹ * u) ^ 2 = Real.sinc (u / 2) ^ 2
    rw [inv_mul_eq_div]
  have h2 := hhalf.const_mul ((2 * Real.pi)⁻¹)
  refine h2.congr (Filter.Eventually.of_forall fun u => ?_)
  show (2 * Real.pi)⁻¹ * Real.sinc (u / 2) ^ 2 = fejerK u
  rw [fejerK]

end Work.GM.Energy.RMoments
