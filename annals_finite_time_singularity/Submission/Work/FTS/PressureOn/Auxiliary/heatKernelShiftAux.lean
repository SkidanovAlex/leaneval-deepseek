/-
# Derivatives and integrability of the shifted heat kernel

The translating chain rules for `fderiv`, `gradient` and `laplaceTrace`, the explicit first and
second derivatives of the Gaussian profile `s ↦ A exp (-(c s))`, the resulting formulas for the
gradient and the Laplace trace of the shifted heat kernel `y ↦ heatKernel t (x - y)`, and the
integrability of those three functions.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.gradient_comp_normSq
import Submission.Work.FTS.PressureOn.Green.laplaceTrace_exp_neg_mul_normSq
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_cutKernel
import Submission.Work.FTS.PressureOn.Auxiliary.gaussShift.integrable_poly_exp_neg_normSq_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section


/-- **The translating chain rule for the Fréchet derivative.** -/
lemma fderiv_comp_sub_const (G : R3 → ℝ) (x y : R3) :
    fderiv ℝ (fun w : R3 => G (w - x)) y = fderiv ℝ G (y - x) :=
  fderiv_comp_sub x

/-- **The translating chain rule for gradients.**  `gradient` is unchanged by precomposing with
the translation `y' ↦ y' - x`. -/
lemma gradient_comp_sub_const (Φ : R3 → ℝ) (x y : R3) :
    gradient (fun y' : R3 => Φ (y' - x)) y = gradient Φ (y - x) := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, inner_gradient_left, fderiv_comp_sub_const Φ x y]

/-- **The translating chain rule for the Laplace trace.**  `laplaceTrace` is unchanged by
precomposing with the translation `y' ↦ y' - x`. -/
lemma laplaceTrace_comp_sub_const (Φ : R3 → ℝ) (x y : R3) :
    laplaceTrace (fun y' : R3 => Φ (y' - x)) y = laplaceTrace Φ (y - x) := by
  rw [Work.FTS.PressureOn.laplaceTrace, Work.FTS.PressureOn.laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun w : R3 => fderiv ℝ (fun y' : R3 => Φ (y' - x)) w (FiniteTimeSingularity.e i))
      = (fun w : R3 => fderiv ℝ Φ (w - x) (FiniteTimeSingularity.e i)) := by
    funext w
    rw [fderiv_comp_sub_const Φ x w]
  rw [h1]
  rw [show (fun w : R3 => fderiv ℝ Φ (w - x) (FiniteTimeSingularity.e i))
      = (fun w : R3 => (fun z : R3 => fderiv ℝ Φ z (FiniteTimeSingularity.e i))
          (w - x)) from rfl]
  rw [fderiv_comp_sub_const (fun z : R3 => fderiv ℝ Φ z (FiniteTimeSingularity.e i)) x y]

/-- The gradient of a function of `‖·‖²`: `∇ (F ∘ ‖·‖²) z = 2F'(‖z‖²) • z`. -/
lemma gradient_comp_normSq_eq (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (z : R3) :
    gradient (fun x : R3 => F (‖x‖ ^ 2)) z = (2 * deriv F (‖z‖ ^ 2)) • z := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, gradient_comp_normSq F hF z]
  simp only [smul_apply, innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]

/-- The norm of the gradient is the operator norm of the derivative. -/
lemma norm_gradient_eq_norm_fderiv (f : R3 → ℝ) (y : R3) :
    ‖gradient f y‖ = ‖fderiv ℝ f y‖ := by
  rw [gradient]
  exact LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ f y)


/-! ## Derivatives and integrability of the shifted heat kernel -/

/-- The derivative of `s ↦ exp (-(c s))`. -/
lemma deriv_exp_neg_mul (c s : ℝ) :
    deriv (fun s : ℝ => Real.exp (-(c * s))) s = -c * Real.exp (-(c * s)) := by
  have hfun : (fun s : ℝ => -(c * s)) = fun s : ℝ => (-c) * s := by
    funext t
    ring
  have hd2 : DifferentiableAt ℝ (fun s : ℝ => -(c * s)) s := by
    rw [hfun]
    fun_prop
  have hcomp : deriv (fun s : ℝ => Real.exp (-(c * s))) s
      = deriv Real.exp (-(c * s)) * deriv (fun s : ℝ => -(c * s)) s := by
    have h := deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) s (h := fun s : ℝ => -(c * s)) (h₂ := Real.exp)
      Real.differentiable_exp.differentiableAt hd2
    simpa only [Function.comp_def] using h
  rw [hcomp, Real.deriv_exp, hfun, deriv_const_mul_id]
  ring

lemma deriv_expProfile (A c s : ℝ) :
    deriv (fun s : ℝ => A * Real.exp (-(c * s))) s = -(A * c) * Real.exp (-(c * s)) := by
  have hd : DifferentiableAt ℝ (fun s : ℝ => Real.exp (-(c * s))) s := by fun_prop
  rw [deriv_const_mul A hd, deriv_exp_neg_mul]
  ring

lemma deriv_deriv_expProfile (A c s : ℝ) :
    deriv (deriv (fun s : ℝ => A * Real.exp (-(c * s)))) s
      = (A * c ^ 2) * Real.exp (-(c * s)) := by
  rw [show deriv (fun s : ℝ => A * Real.exp (-(c * s)))
        = fun s : ℝ => -(A * c) * Real.exp (-(c * s)) from funext (deriv_expProfile A c)]
  have hd : DifferentiableAt ℝ (fun s : ℝ => Real.exp (-(c * s))) s := by fun_prop
  rw [deriv_const_mul (-(A * c)) hd, deriv_exp_neg_mul]
  ring

lemma contDiff_expProfile (A c : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (fun s : ℝ => A * Real.exp (-(c * s))) := by
  have h1 : ContDiff ℝ n (fun s : ℝ => -(c * s)) :=
    ((contDiff_const (𝕜 := ℝ) (c := c)).mul contDiff_id).neg
  exact ((contDiff_const (𝕜 := ℝ) (c := A)).mul (Real.contDiff_exp.comp h1))

lemma contDiff_heatKernel (t : ℝ) (ht : 0 < t) (n : ℕ∞) :
    ContDiff ℝ n (heatKernel t) := by
  have h : heatKernel t = fun z : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (‖z‖ ^ 2) := by
    funext z
    rw [heatKernel_eq_const_mul_exp ht]
  rw [h]
  exact (contDiff_expProfile _ _ n).comp (contDiff_norm_sq ℝ)

lemma contDiff_heatKernel_comp_sub (t : ℝ) (ht : 0 < t) (x : R3) (n : ℕ∞) :
    ContDiff ℝ n (fun y' : R3 => heatKernel t (x - y')) :=
  (contDiff_heatKernel t ht n).comp (contDiff_const.sub contDiff_id)

/-- The heat kernel, shifted: `γ_t (x - y) = A exp (-(c ‖y - x‖²))`. -/
lemma heatKernel_shift_eq (t : ℝ) (ht : 0 < t) (x y : R3) :
    heatKernel t (x - y) = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := by
  rw [heatKernel_eq_const_mul_exp ht, norm_sub_rev]

/-- **The Laplace trace of the shifted heat kernel.** -/
lemma laplaceTrace_heatKernel_shift (t : ℝ) (ht : 0 < t) (x y : R3) :
    laplaceTrace (fun y' : R3 => heatKernel t (x - y')) y
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          ((4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) := by
  have hpoint : (fun y' : R3 => heatKernel t (x - y'))
      = fun y' : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-((4 * t)⁻¹ * s))) (‖y' - x‖ ^ 2) := by
    funext y'
    rw [heatKernel_shift_eq t ht x y']
  rw [hpoint, laplaceTrace_comp_sub_const
    (fun z : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (‖z‖ ^ 2)) x y]
  rw [Work.FTS.PressureOn.PoissonAux.laplaceTrace_normSq
    (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-((4 * t)⁻¹ * s)))
    (contDiff_expProfile _ _ 2) (y - x)]
  rw [deriv_expProfile _ _ (‖y - x‖ ^ 2), deriv_deriv_expProfile _ _ (‖y - x‖ ^ 2)]
  ring

/-- **The gradient of the shifted heat kernel.** -/
lemma gradient_heatKernel_shift (t : ℝ) (ht : 0 < t) (x y : R3) :
    gradient (fun y' : R3 => heatKernel t (x - y')) y
      = -(((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
          Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) • (y - x)) := by
  have hpoint : (fun y' : R3 => heatKernel t (x - y'))
      = fun y' : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-((4 * t)⁻¹ * s))) (‖y' - x‖ ^ 2) := by
    funext y'
    rw [heatKernel_shift_eq t ht x y']
  rw [hpoint, gradient_comp_sub_const
    (fun z : R3 => (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (‖z‖ ^ 2)) x y,
    gradient_comp_normSq_eq (fun s : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((4 * t)⁻¹ * s))) (contDiff_expProfile _ _ 1) (y - x),
    deriv_expProfile _ _ (‖y - x‖ ^ 2)]
  rw [← neg_smul]
  congr 1
  ring

lemma integrable_heatKernel_shift (t : ℝ) (ht : 0 < t) (x : R3) :
    Integrable (fun y : R3 => heatKernel t (x - y)) := by
  have hc : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  have hbase : Integrable (fun y : R3 =>
      ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) + 0 * ‖y - x‖ ^ 2) *
        Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) :=
    gaussShift.integrable_poly_exp_neg_normSq_sub _ 0 _ (by positivity) le_rfl hc x
  refine hbase.congr (Eventually.of_forall fun y => ?_)
  show ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) + 0 * ‖y - x‖ ^ 2) *
      Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) = heatKernel t (x - y)
  rw [heatKernel_shift_eq t ht x y]
  ring

lemma integrable_laplaceTrace_heatKernel_shift (t : ℝ) (ht : 0 < t) (x : R3) :
    Integrable (fun y : R3 => laplaceTrace (fun y' : R3 => heatKernel t (x - y')) y) := by
  have hcpos : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  have hApos : (0 : ℝ) < (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by positivity
  have hbound := gaussShift.integrable_poly_exp_neg_normSq_sub
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (6 * (4 * t)⁻¹))
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (4 * ((4 * t)⁻¹) ^ 2)) (4 * t)⁻¹
    (by positivity) (by positivity) hcpos x
  refine Integrable.mono' hbound ?_ ?_
  · exact (Green.continuous_laplaceTrace _
      (contDiff_heatKernel_comp_sub t ht x 2)).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, laplaceTrace_heatKernel_shift t ht x y]
    have hexp : 0 < Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := Real.exp_pos _
    have h1 : |4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹|
        ≤ 4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 + 6 * (4 * t)⁻¹ := by
      rw [abs_le]
      constructor <;> nlinarith [hcpos, sq_nonneg (‖y - x‖), sq_nonneg (4 * t)⁻¹]
    rw [abs_mul, abs_mul, abs_of_pos hApos, abs_of_pos hexp]
    have hAe : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := le_of_lt hApos
    have hkey : |4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹|
          * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))
        ≤ (4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 + 6 * (4 * t)⁻¹)
          * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hexp)
    have h4 : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (|4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 - 6 * (4 * t)⁻¹|
            * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)))
        ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          ((4 * ((4 * t)⁻¹) ^ 2 * ‖y - x‖ ^ 2 + 6 * (4 * t)⁻¹)
            * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hkey hAe
    refine le_trans h4 (le_of_eq ?_)
    ring

lemma integrable_gradient_heatKernel_shift (t : ℝ) (ht : 0 < t) (x : R3) :
    Integrable (fun y : R3 => ‖gradient (fun y' : R3 => heatKernel t (x - y')) y‖) := by
  have hcpos : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  have hApos : (0 : ℝ) < (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by positivity
  have hbound := gaussShift.integrable_poly_exp_neg_normSq_sub
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹))
    ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹)) (4 * t)⁻¹
    (by positivity) (by positivity) hcpos x
  refine Integrable.mono' hbound ?_ ?_
  · exact (Green.contDiff_gradient _
      (contDiff_heatKernel_comp_sub t ht x 2)).continuous.norm.aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [gradient_heatKernel_shift t ht x y, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        (2 * (4 * t)⁻¹) * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)))]
    have h1 : ‖y - x‖ ≤ 1 + ‖y - x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖y - x‖ - 1), norm_nonneg (y - x)]
    have h2 : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
        Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := by positivity
    calc (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) * ‖y - x‖
        ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) *
            Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) * (1 + ‖y - x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹)
            + (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (2 * (4 * t)⁻¹) * ‖y - x‖ ^ 2)
            * Real.exp (-((4 * t)⁻¹ * ‖y - x‖ ^ 2)) := by
          ring

end

end Work.FTS.PressureOn.Auxiliary
