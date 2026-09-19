import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular

/-! # Vertical exponential decay of the Gamma function (Stirling-type bound)

This module proves the uniform bound

`‖Γ(σ + i t)‖ ≤ C(σ)·(1+|t|)^σ·e^{-π|t|/2}`   for all `σ > 0`, `t ∈ ℝ`

by contour rotation of Euler's Gamma integral followed by an elementary optimization
of the rotation angle.  Everything here imports only `Mathlib`.
-/

open Complex Filter MeasureTheory Set
open scoped Real Topology Interval

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

noncomputable section

namespace AfeRect

open Complex Filter MeasureTheory Set
open scoped Real Interval
open Complex

noncomputable section

/-- The boundary integral of `f` over the rectangle with opposite corners `z w`
(positively oriented; matches the left-hand side of Mathlib's Cauchy-Goursat rectangle
theorems). -/
noncomputable def rectBoundary (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I))
    - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
    + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))
    - I • (∫ y : ℝ in z.im..w.im, f (re z + y * I))

/-- **Cauchy-Goursat for a rectangle**: if `f` is holomorphic on the closed rectangle then
the boundary integral vanishes. -/
lemma rectBoundary_eq_zero_of_differentiableOn (f : ℂ → ℂ) (z w : ℂ)
    (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectBoundary z w f = 0 := by
  unfold rectBoundary
  exact integral_boundary_rect_eq_zero_of_differentiableOn f z w H

end

end AfeRect

open Complex Filter MeasureTheory Set
open scoped Real
namespace GRBase

noncomputable section

/-- `cexp (x : ℂ) = (Real.exp x : ℂ)`. -/
lemma cexp_ofReal_exp (x : ℝ) : cexp (x : ℂ) = (Real.exp x : ℂ) := (Complex.ofReal_exp x).symm

/-- The unrotated Γ integrand `e^{-r}·r^{s-1}` (`r > 0`). -/
noncomputable def J0 (s : ℂ) (r : ℝ) : ℂ := cexp (-(r : ℂ)) * (r : ℂ) ^ (s - 1)

/-- The rotated Γ integrand `e^{-r·e^{-iθ}}·r^{s-1}` (`r > 0`). -/
noncomputable def Jr (s : ℂ) (θ : ℝ) (r : ℝ) : ℂ :=
  cexp (-((r : ℂ) * cexp (-(I * (θ : ℂ))))) * (r : ℂ) ^ (s - 1)

/-- Pullback to the real line of the unrotated integrand: `Hs s x = e^{-e^x}·e^{s·x}`. -/
noncomputable def Hs (s : ℂ) (x : ℝ) : ℂ := cexp (-cexp (x : ℂ)) * cexp (s * (x : ℂ))

/-- Pullback to the real line of the rotated integrand: `Hr s θ x = e^{-e^{x-iθ}}·e^{s·(x-iθ)}`. -/
noncomputable def Hr (s : ℂ) (θ : ℝ) (x : ℝ) : ℂ :=
  cexp (-(cexp ((x : ℂ) - (θ : ℂ) * I))) * cexp (s * ((x : ℂ) - (θ : ℂ) * I))

/-- `(e^x : ℂ)^z = cexp (z·x)` for real `x`. -/
lemma cpow_ofReal_exp (x : ℝ) (z : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ z = cexp (z * (x : ℂ)) := by
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [Complex.cpow_def_of_ne_zero hx]
  have hlog : Complex.log ((Real.exp x : ℝ) : ℂ) = (x : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos x).le]
    norm_num [Real.log_exp]
  rw [hlog]
  ring_nf

/-- `(e^x : ℂ)^{s-1}·(e^x : ℂ) = (e^x : ℂ)^s`. -/
lemma cpow_exp_sub_one_mul (x : ℝ) (s : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ (s - 1) * ((Real.exp x : ℝ) : ℂ) = ((Real.exp x : ℝ) : ℂ) ^ s := by
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  calc
    ((Real.exp x : ℝ) : ℂ) ^ (s - 1) * ((Real.exp x : ℝ) : ℂ)
        = ((Real.exp x : ℝ) : ℂ) ^ (s - 1) * ((Real.exp x : ℝ) : ℂ) ^ 1 := by
          rw [Complex.cpow_one]
    _ = ((Real.exp x : ℝ) : ℂ) ^ ((s - 1) + 1) := (Complex.cpow_add (s - 1) 1 hx).symm
    _ = ((Real.exp x : ℝ) : ℂ) ^ s := by congr 1; ring

/-- `(e^x : ℂ)·(e^x : ℂ)^{s-1} = (e^x : ℂ)^s`. -/
lemma cpow_exp_mul_sub_one (x : ℝ) (s : ℂ) :
    ((Real.exp x : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ) ^ (s - 1) = ((Real.exp x : ℝ) : ℂ) ^ s := by
  rw [mul_comm, cpow_exp_sub_one_mul]

/-- `Hs s x = exp x • J0 s (exp x)` pointwise. -/
lemma Hs_smul (s : ℂ) (x : ℝ) : Hs s x = Real.exp x • J0 s (Real.exp x) := by
  calc
    Hs s x = cexp (-((Real.exp x : ℝ) : ℂ)) * (((Real.exp x : ℝ) : ℂ) ^ s) := by
      unfold Hs
      rw [cexp_ofReal_exp x]
      rw [← cpow_ofReal_exp x s]
    _ = Real.exp x • J0 s (Real.exp x) := by
      unfold J0
      rw [← cpow_exp_sub_one_mul x s]
      change cexp (-((Real.exp x : ℝ) : ℂ))
          * ((((Real.exp x : ℝ) : ℂ) ^ (s - 1)) * ((Real.exp x : ℝ) : ℂ))
        = (Real.exp x : ℂ) * (cexp (-((Real.exp x : ℝ) : ℂ)) * (((Real.exp x : ℝ) : ℂ) ^ (s - 1)))
      ring

/-- `e^{-iθ} = cos θ - i·sin θ`. -/
lemma cexp_neg_I_mul (θ : ℝ) :
    cexp (-(I * (θ : ℂ))) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
  rw [show -(I * (θ : ℂ)) = (-(θ : ℂ)) * I by ring]
  rw [Complex.exp_mul_I]
  have hc : cos (-(θ : ℂ)) = (Real.cos θ : ℂ) := by
    rw [Complex.cos_neg, ← Complex.ofReal_cos]
  have hs : sin (-(θ : ℂ)) = -((Real.sin θ : ℂ)) := by
    rw [Complex.sin_neg, ← Complex.ofReal_sin]
  rw [hc, hs]
  ring

/-- `exp (x - iθ) = e^x · e^{-iθ}`. -/
lemma cexp_sub_I_mul_exp (x : ℝ) (θ : ℝ) :
    cexp ((x : ℂ) - (θ : ℂ) * I) = ((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ))) := by
  calc
    cexp ((x : ℂ) - (θ : ℂ) * I) = cexp ((x : ℂ) + -((θ : ℂ) * I)) := rfl
    _ = cexp (x : ℂ) * cexp (-((θ : ℂ) * I)) := Complex.exp_add _ _
    _ = ((Real.exp x : ℝ) : ℂ) * cexp (-((θ : ℂ) * I)) := by rw [cexp_ofReal_exp x]
    _ = ((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ))) := by
          have harg : -((θ : ℂ) * I) = -(I * (θ : ℂ)) := by ring
          rw [harg]

/-- `exp (s·(x - iθ)) = exp(s·x) · exp(-(iθ)·s)`. -/
lemma cexp_mul_sub (s : ℂ) (x : ℝ) (θ : ℝ) :
    cexp (s * ((x : ℂ) - (θ : ℂ) * I)) = cexp (s * (x : ℂ)) * cexp (-((I * (θ : ℂ)) * s)) := by
  calc
    cexp (s * ((x : ℂ) - (θ : ℂ) * I))
        = cexp (s * (x : ℂ) + -(s * ((θ : ℂ) * I))) := by congr 1; ring
    _ = cexp (s * (x : ℂ)) * cexp (-(s * ((θ : ℂ) * I))) := Complex.exp_add _ _
    _ = cexp (s * (x : ℂ)) * cexp (-((I * (θ : ℂ)) * s)) := by
          have harg : -(s * ((θ : ℂ) * I)) = -((I * (θ : ℂ)) * s) := by ring
          rw [harg]

/-- `Hr s θ x = cexp(-(I·θ)·s) * (exp x • Jr s θ (exp x))` pointwise. -/
lemma Hr_smul (s : ℂ) (θ : ℝ) (x : ℝ) :
    Hr s θ x = cexp (-((I * (θ : ℂ)) * s)) * (Real.exp x • Jr s θ (Real.exp x)) := by
  calc
    Hr s θ x = cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * cexp (s * ((x : ℂ) - (θ : ℂ) * I)) := by
          unfold Hr
          rw [cexp_sub_I_mul_exp x θ]
    _ = cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * (cexp (s * (x : ℂ)) * cexp (-((I * (θ : ℂ)) * s))) := by
          rw [cexp_mul_sub s x θ]
    _ = cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * ((((Real.exp x : ℝ) : ℂ) ^ s) * cexp (-((I * (θ : ℂ)) * s))) := by
          rw [← cpow_ofReal_exp x s]
    _ = cexp (-((I * (θ : ℂ)) * s)) * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * (((Real.exp x : ℝ) : ℂ) ^ s)) := by ring
    _ = cexp (-((I * (θ : ℂ)) * s)) * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * (((Real.exp x : ℝ) : ℂ) * (((Real.exp x : ℝ) : ℂ) ^ (s - 1)))) := by
          rw [← cpow_exp_mul_sub_one x s]
    _ = cexp (-((I * (θ : ℂ)) * s)) * (Real.exp x • Jr s θ (Real.exp x)) := by
          unfold Jr
          change cexp (-((I * (θ : ℂ)) * s))
              * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
                * (((Real.exp x : ℝ) : ℂ) * (((Real.exp x : ℝ) : ℂ) ^ (s - 1))))
            = cexp (-((I * (θ : ℂ)) * s))
              * ((Real.exp x : ℂ) * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
                * (((Real.exp x : ℝ) : ℂ) ^ (s - 1))))
          ring

/-- Real part of `e^{-iθ}` is `cos θ`. -/
lemma re_cexp_neg_I_mul (θ : ℝ) : (cexp (-(I * (θ : ℂ)))).re = Real.cos θ := by
  rw [cexp_neg_I_mul]
  rw [Complex.sub_re, Complex.mul_re]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Real part of `-r·e^{-iθ}` is `-r·cos θ`. -/
lemma re_neg_mul_cexp_neg_I_mul (r : ℝ) (θ : ℝ) :
    (-((r : ℂ) * cexp (-(I * (θ : ℂ))))).re = -(r * Real.cos θ) := by
  rw [cexp_neg_I_mul]
  simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Norm of the rotated integrand: `‖Jr s θ r‖ = exp(-r·cos θ)·r^{Re s - 1}` for `r > 0`. -/
lemma norm_Jr (s : ℂ) (θ : ℝ) (r : ℝ) (hr : 0 < r) :
    ‖Jr s θ r‖ = Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1) := by
  unfold Jr
  rw [norm_mul]
  have h₁ : ‖cexp (-((r : ℂ) * cexp (-(I * (θ : ℂ)))))‖ =
      Real.exp (-(r * Real.cos θ)) := by
    rw [Complex.norm_exp, re_neg_mul_cexp_neg_I_mul]
  have h₅ : ‖(r : ℂ) ^ (s - 1)‖ = r ^ (s.re - 1) := by
    have h₆ : ((s - 1 : ℂ).re) = s.re - 1 := by simp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, h₆]
  rw [h₁, h₅]

/-- Norm of the unrotated integrand: `‖J0 s r‖ = exp(-r)·r^{Re s - 1}` for `r > 0`. -/
lemma norm_J0 (s : ℂ) (r : ℝ) (hr : 0 < r) :
    ‖J0 s r‖ = Real.exp (-r) * r ^ (s.re - 1) := by
  unfold J0
  rw [norm_mul]
  have h₁ : ‖cexp (-(r : ℂ))‖ = Real.exp (-r) := by
    rw [Complex.norm_exp]
    simp
  have h₅ : ‖(r : ℂ) ^ (s - 1)‖ = r ^ (s.re - 1) := by
    have h₆ : ((s - 1 : ℂ).re) = s.re - 1 := by simp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, h₆]
  rw [h₁, h₅]

end
end GRBase

open Complex Filter MeasureTheory Set
open scoped Real Interval Topology
namespace GRVert

noncomputable section

/-- The Γ-contour integrand restricted to a vertical line: `V s x₀ y = F s (x₀ + iy)`. -/
noncomputable def V (s : ℂ) (x₀ y : ℝ) : ℂ :=
  cexp (-cexp ((x₀ : ℂ) + (y : ℂ) * I)) * cexp (s * ((x₀ : ℂ) + (y : ℂ) * I))

/-- Real part of `(x : ℂ) + (y : ℂ) * I`. -/
lemma re_ofReal_add_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
  ring_nf

/-- Imaginary part of `(x : ℂ) + (y : ℂ) * I`. -/
lemma im_ofReal_add_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by
  rw [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
  ring_nf

/-- Real part of `s · (x₀ + iy)` for real `x₀`, `y`. -/
lemma re_smul_ofReal_add_mul_I (s : ℂ) (x₀ y : ℝ) :
    (s * ((x₀ : ℂ) + (y : ℂ) * I)).re = s.re * x₀ - s.im * y := by
  rw [Complex.mul_re, re_ofReal_add_mul_I, im_ofReal_add_mul_I]

/-- Exact norm of the vertical-line integrand: `‖V s x₀ y‖ = e^{-e^{x₀}cos y} e^{s.re·x₀ - s.im·y}`. -/
lemma norm_V_eq (s : ℂ) (x₀ y : ℝ) :
    ‖V s x₀ y‖ = Real.exp (-(Real.exp x₀ * Real.cos y)) * Real.exp (s.re * x₀ - s.im * y) := by
  unfold V
  rw [norm_mul]
  have h1 : ‖cexp (-cexp ((x₀ : ℂ) + (y : ℂ) * I))‖ =
      Real.exp (-(Real.exp x₀ * Real.cos y)) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.neg_re, Complex.exp_re, re_ofReal_add_mul_I, im_ofReal_add_mul_I]
  have h2 : ‖cexp (s * ((x₀ : ℂ) + (y : ℂ) * I))‖ = Real.exp (s.re * x₀ - s.im * y) := by
    rw [Complex.norm_exp]
    congr 1
    rw [re_smul_ofReal_add_mul_I]
  rw [h1, h2]

/-- For `|y| ≤ |θ| < π/2`: `cos θ ≤ cos y`. -/
lemma cos_le_cos_of_abs_le {θ y : ℝ} (hθ : |θ| < Real.pi / 2) (hy : |y| ≤ |θ|) :
    Real.cos θ ≤ Real.cos y := by
  have hθπ : |θ| ≤ Real.pi := by linarith [Real.pi_pos]
  calc
    Real.cos θ = Real.cos |θ| := by rw [Real.cos_abs]
    _ ≤ Real.cos |y| := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) hθπ hy
    _ = Real.cos y := by rw [Real.cos_abs]

/-- `|θ| < π/2` ⟹ `0 < cos θ`. -/
lemma cos_pos_of_abs_lt_pi_div_two {θ : ℝ} (hθ : |θ| < Real.pi / 2) : 0 < Real.cos θ := by
  exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)

/-- Pointwise norm bound on the vertical lines, valid for `|y| ≤ |θ| < π/2`:

    ‖V s x₀ y‖ ≤ exp (-(exp x₀ * cos θ)) * exp (s.re * x₀ + |s.im| * |θ|)  -/
lemma norm_V_le (s : ℂ) (x₀ : ℝ) {θ y : ℝ} (hθ : |θ| < Real.pi / 2) (hy : |y| ≤ |θ|) :
    ‖V s x₀ y‖ ≤ Real.exp (-(Real.exp x₀ * Real.cos θ)) * Real.exp (s.re * x₀ + |s.im| * |θ|) := by
  rw [norm_V_eq]
  have hcos : Real.cos θ ≤ Real.cos y := cos_le_cos_of_abs_le hθ hy
  have hc1 : Real.exp x₀ * Real.cos θ ≤ Real.exp x₀ * Real.cos y :=
    mul_le_mul_of_nonneg_left hcos (Real.exp_pos x₀).le
  have hExp1 : Real.exp (-(Real.exp x₀ * Real.cos y)) ≤ Real.exp (-(Real.exp x₀ * Real.cos θ)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hsm : -(s.im * y) ≤ |s.im| * |θ| := by
    calc
      -(s.im * y) ≤ |s.im * y| := neg_le_abs (s.im * y)
      _ = |s.im| * |y| := by rw [abs_mul]
      _ ≤ |s.im| * |θ| := mul_le_mul_of_nonneg_left hy (abs_nonneg s.im)
  have hExp2 : Real.exp (s.re * x₀ - s.im * y) ≤ Real.exp (s.re * x₀ + |s.im| * |θ|) := by
    exact Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul hExp1 hExp2 (Real.exp_pos _).le (Real.exp_pos _).le

/-- Any point of the open-closed interval `Ι 0 (-θ)` lies in `[-|θ|, |θ|]`. -/
lemma abs_le_of_mem_uIoc {θ : ℝ} {y : ℝ} (hy : y ∈ Set.uIoc 0 (-θ)) : |y| ≤ |θ| := by
  rw [Set.mem_uIoc] at hy
  rcases hy with h | h
  · have hy0 : 0 ≤ y := le_of_lt h.1
    have hθ0 : θ ≤ 0 := by linarith
    rw [abs_of_nonneg hy0, abs_of_nonpos hθ0]
    exact h.2
  · have hθp : 0 ≤ θ := by linarith
    rw [abs_of_nonpos h.2, abs_of_nonneg hθp]
    linarith

/-- Norm bound for the right-edge vertical integral. -/
lemma right_edge_norm_le (s : ℂ) {θ : ℝ} (hθ : |θ| < Real.pi / 2) (T : ℝ) :
    ‖∫ y in 0..(-θ), V s T y‖ ≤
      (Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T + |s.im| * |θ|)) * |θ| := by
  have hpt : ∀ y ∈ Set.uIoc 0 (-θ), ‖V s T y‖ ≤
      Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T + |s.im| * |θ|) := by
    intro y hy
    exact norm_V_le s T hθ (abs_le_of_mem_uIoc hy)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := -θ)
    (f := fun y => V s T y) hpt
  simpa [sub_zero] using hb

/-- Pointwise bound on the left edge: `‖V s (-T) y‖ ≤ e^{-s.re·T}·e^{|s.im||θ|}`. -/
lemma left_edge_pointwise_le (s : ℂ) {θ y : ℝ} (hθ : |θ| < Real.pi / 2) (hy : |y| ≤ |θ|) (T : ℝ) :
    ‖V s (-T) y‖ ≤ Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by
  have hb := norm_V_le s (-T) hθ hy
  have hnonneg : 0 ≤ Real.exp (-T) * Real.cos θ :=
    mul_nonneg (Real.exp_pos (-T)).le (cos_pos_of_abs_lt_pi_div_two hθ).le
  have hle1 : Real.exp (-(Real.exp (-T) * Real.cos θ)) ≤ 1 := by
    have hle0 : -(Real.exp (-T) * Real.cos θ) ≤ 0 := neg_nonpos.mpr hnonneg
    simpa using (Real.exp_le_exp.mpr hle0)
  calc
    ‖V s (-T) y‖ ≤ Real.exp (-(Real.exp (-T) * Real.cos θ)) * Real.exp (s.re * (-T) + |s.im| * |θ|) := hb
    _ = Real.exp (-(Real.exp (-T) * Real.cos θ)) * Real.exp (-(s.re * T) + |s.im| * |θ|) := by
      congr 1
      ring_nf
    _ = Real.exp (-(Real.exp (-T) * Real.cos θ)) * (Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|)) := by
      rw [Real.exp_add]
    _ ≤ 1 * (Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|)) := by
      exact mul_le_mul_of_nonneg_right hle1 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by simp

/-- Norm bound for the left-edge vertical integral. -/
lemma left_edge_norm_le (s : ℂ) {θ : ℝ} (hθ : |θ| < Real.pi / 2) (T : ℝ) :
    ‖∫ y in 0..(-θ), V s (-T) y‖ ≤
      Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) * |θ| := by
  have hpt : ∀ y ∈ Set.uIoc 0 (-θ), ‖V s (-T) y‖ ≤
      Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by
    intro y hy
    exact left_edge_pointwise_le s hθ (abs_le_of_mem_uIoc hy) T
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := -θ)
    (f := fun y => V s (-T) y) hpt
  simpa [sub_zero] using hb

/-- `exp (-(exp T · c)) · exp (k·T) → 0` as `T → ∞`, for `0 < c`. -/
lemma tendsto_exp_neg_exp_mul (c k : ℝ) (hc : 0 < c) :
    Tendsto (fun T : ℝ => Real.exp (-(Real.exp T * c)) * Real.exp (k * T)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun T : ℝ => c * (Real.exp T / T)) atTop atTop := by
    have h := Real.tendsto_exp_div_pow_atTop 1
    simpa [pow_one] using h.const_mul_atTop hc
  have hge : ∀ᶠ T in atTop, (k + 1) ≤ c * (Real.exp T / T) :=
    hdiv.eventually (eventually_ge_atTop (k + 1))
  have hmain : Tendsto (fun T : ℝ => k * T - c * Real.exp T) atTop atBot := by
    refine Filter.tendsto_atBot_mono' atTop ?hle Filter.tendsto_neg_atTop_atBot
    filter_upwards [hge, eventually_ge_atTop 1] with T hT hT1
    have hTpos : 0 < T := by linarith
    have hm : (k + 1) * T ≤ (c * (Real.exp T / T)) * T :=
      mul_le_mul_of_nonneg_right hT (le_of_lt hTpos)
    have hcancel : (c * (Real.exp T / T)) * T = c * Real.exp T := by
      field_simp [hTpos.ne']
    rw [hcancel] at hm
    linarith
  have hExp : Tendsto (fun T : ℝ => Real.exp (k * T - c * Real.exp T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hmain
  refine hExp.congr' (Filter.Eventually.of_forall (fun T => ?_))
  change Real.exp (k * T - c * Real.exp T) = Real.exp (-(Real.exp T * c)) * Real.exp (k * T)
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- The right vertical edge of the Γ-contour rectangle tends to zero as `T → ∞`. -/
theorem right_edge_tendsto (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s T y) atTop (𝓝 0) := by
  have _hσ : 0 < s.re := hs
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hcos : 0 < Real.cos θ := cos_pos_of_abs_lt_pi_div_two hθ
  let Bd : ℝ → ℝ := fun T => Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T)
  have hBd : Tendsto Bd atTop (𝓝 0) := tendsto_exp_neg_exp_mul (Real.cos θ) s.re hcos
  refine squeeze_zero (fun T => norm_nonneg _) (fun T => right_edge_norm_le s hθ T) ?_
  have hg : (fun T : ℝ =>
        (Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T + |s.im| * |θ|)) * |θ|)
      = (fun T : ℝ => (|θ| * Real.exp (|s.im| * |θ|)) * Bd T) := by
    funext T
    dsimp [Bd]
    rw [Real.exp_add]
    ring_nf
  rw [hg]
  simpa using (tendsto_const_nhds.mul hBd)

/-- The left vertical edge of the Γ-contour rectangle tends to zero as `T → ∞`. -/
theorem left_edge_tendsto (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s (-T) y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun T => norm_nonneg _) (fun T => left_edge_norm_le s hθ T) ?_
  have hneg : Tendsto (fun T : ℝ => Real.exp (-(s.re * T))) atTop (𝓝 0) := by
    have hst : Tendsto (fun T : ℝ => s.re * T) atTop atTop :=
      (Filter.tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop).const_mul_atTop hs
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hst
  have hg : (fun T : ℝ => Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) * |θ|)
      = (fun T : ℝ => (|θ| * Real.exp (|s.im| * |θ|)) * Real.exp (-(s.re * T))) := by
    funext T
    ring_nf
  rw [hg]
  simpa using (tendsto_const_nhds.mul hneg)

end
end GRVert

open Filter MeasureTheory Set Real intervalIntegral
open scoped Real
namespace GRRealInt

/-- The Euler-type real integral `∫₀^∞ e^{-c·r}·r^{σ-1} dr` converges for `c > 0`, `σ > 0`. -/
lemma real_integrable_exp_neg_mul_rpow {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    IntegrableOn (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      ((intervalIntegrable_rpow' (by linarith : -1 < σ - 1)).continuousOn_mul
        (by fun_prop : ContinuousOn (fun r : ℝ => Real.exp (-(c * r))) (Set.uIcc 0 1)))
  · have hcont : ContinuousOn (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1)) (Ici 1) := by
      have h1 : ContinuousOn (fun r : ℝ => Real.exp (-(c * r))) (Ici 1) := by fun_prop
      have h2 : ContinuousOn (fun r : ℝ => r ^ (σ - 1)) (Ici 1) :=
        continuousOn_id.rpow_const (by
          intro x hx
          exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
      exact h1.mul h2
    have ho : (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1)) =O[atTop]
        (fun r : ℝ => Real.exp (-(c / 2) * r)) := by
      have hlt : -c < -(c / 2) := by linarith
      simpa [neg_mul] using
        (isLittleO_exp_mul_rpow_of_lt (σ - 1) (a := -c) (b := -(c / 2)) hlt).isBigO
    exact integrable_of_isBigO_exp_neg (div_pos hc two_pos) hcont ho

end GRRealInt

open Complex Filter MeasureTheory Set
open GRBase
open scoped Real
namespace GRSubst

noncomputable section

/-- ae: `(-∞,0) ∪ (0,∞) = ℝ`. -/
lemma Iio_union_Ioi_ae_univ : (Iio (0 : ℝ) ∪ Ioi 0 : Set ℝ) =ᵐ[volume] (Set.univ : Set ℝ) := by
  rw [ae_eq_univ]
  have hcomp : ((Iio (0 : ℝ) ∪ Ioi 0)ᶜ : Set ℝ) = {0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hx0
      exact hx (lt_or_gt_of_ne hx0)
    · intro hx
      simp [hx]
  rw [hcomp]
  simp

/-- `(0,∞) = (0,1) ∪ {1} ∪ (1,∞)`. -/
lemma Ioi_eq_union : Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ) ∪ Ioi 1 := by
  ext x
  constructor
  · intro hx
    rcases lt_trichotomy x 1 with h | h | h
    · exact Or.inl (Or.inl ⟨hx, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · intro hx
    rcases hx with h | h
    · rcases h with h | h
      · exact h.1
      · have hx1 : x = 1 := Set.mem_singleton_iff.mp h
        simp [hx1]
    · exact lt_trans zero_lt_one (by simpa using h)

/-- The unrotated integrand equals the `GammaIntegral` integrand pointwise on `r > 0`. -/
lemma J0_eq_GammaIntegrand (s : ℂ) (r : ℝ) (_hr : 0 < r) :
    J0 s r = ↑(Real.exp (-r)) * (r : ℂ) ^ (s - 1) := by
  unfold J0
  have h1 : cexp (-(r : ℂ)) = (Real.exp (-r) : ℂ) := by
    rw [← Complex.ofReal_neg, (Complex.ofReal_exp (-r)).symm]
  rw [h1]

/-- `J0 s` is integrable over `(0,∞)` (Euler's integral, `0 < Re s`). -/
lemma integrable_J0 (s : ℂ) (hs : 0 < s.re) : IntegrableOn (J0 s) (Ioi 0) := by
  have hg : IntegrableOn (fun r : ℝ => ↑(Real.exp (-r)) * (r : ℂ) ^ (s - 1)) (Ioi 0) := by
    simpa [Complex.GammaIntegral] using Complex.GammaIntegral_convergent hs
  refine hg.congr_fun ?_ measurableSet_Ioi
  intro r hr
  exact (J0_eq_GammaIntegrand s r hr).symm

/-- **T2**: the rotated integrand is integrable over `(0,∞)` for `0 < Re s`, `|θ| < π/2`. -/
lemma integrable_Jr (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    IntegrableOn (Jr s θ) (Ioi 0) := by
  have hcos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  constructor
  · have hc1 : ContinuousOn (fun r : ℝ => cexp (-((r : ℂ) * cexp (-(I * (θ : ℂ)))))) (Ioi 0) := by
      fun_prop
    have hc2 : ContinuousOn (fun r : ℝ => (r : ℂ) ^ (s - 1)) (Ioi 0) := by
      apply continuousOn_of_forall_continuousAt
      intro r hr
      refine ContinuousAt.comp (continuousAt_cpow_const ?_) Complex.continuous_ofReal.continuousAt
      exact ofReal_mem_slitPlane.2 hr
    exact (hc1.mul hc2).aestronglyMeasurable measurableSet_Ioi
  · rw [← hasFiniteIntegral_norm_iff]
    have hreal : IntegrableOn (fun r : ℝ => Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1)) (Ioi 0) := by
      refine (GRRealInt.real_integrable_exp_neg_mul_rpow hcos hs).congr_fun ?_ measurableSet_Ioi
      intro r hr
      have harg : -(Real.cos θ * r) = -(r * Real.cos θ) := by ring
      simp [harg]
    refine HasFiniteIntegral.congr hreal.2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with r hr
    exact (norm_Jr s θ r hr).symm

/-- Substitution `r = e^x` on the negative half-line: image `(0, exp a)`. -/
lemma integral_comp_exp_Iio (g : ℝ → ℂ) (a : ℝ) :
    ∫ x in Iio a, Real.exp x • g (Real.exp x) = ∫ y in Ioo 0 (Real.exp a), g y := by
  rw [← Real.image_exp_Iio a]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Iio a) (f := Real.exp)
    (f' := fun x : ℝ => Real.exp x) measurableSet_Iio
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Iio ?_
  intro x hx
  simp [abs_of_pos (Real.exp_pos x)]

/-- Substitution `r = e^x` on the negative half-line: integrability transfer. -/
lemma integrableOn_comp_exp_Iio (g : ℝ → ℂ) (a : ℝ) :
    IntegrableOn (fun x => Real.exp x • g (Real.exp x)) (Iio a) ↔
      IntegrableOn g (Ioo 0 (Real.exp a)) := by
  rw [← Real.image_exp_Iio a]
  rw [MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Iio a) (f := Real.exp)
    (f' := fun x : ℝ => Real.exp x) measurableSet_Iio
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g]
  refine Iff.intro ?_ ?_
  · intro h
    exact h.congr_fun (fun x hx => by simp [abs_of_pos (Real.exp_pos x)]) measurableSet_Iio
  · intro h
    exact h.congr_fun (fun x hx => by simp [abs_of_pos (Real.exp_pos x)]) measurableSet_Iio

/-- abbreviation: the substitution integrand `x ↦ e^x • g(e^x)`. -/
noncomputable def phi (g : ℝ → ℂ) (x : ℝ) : ℂ := Real.exp x • g (Real.exp x)

/-- integrability of `x ↦ e^x • g(e^x)` on the two half-lines. -/
lemma integrable_comp_exp_union (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (phi g) (Iio 0 ∪ Ioi 0) := by
  have hIio : IntegrableOn (phi g) (Iio 0) := by
    exact (integrableOn_comp_exp_Iio g 0).2 (hg.mono_set (by intro x hx; exact hx.1))
  have hIoi : IntegrableOn (phi g) (Ioi 0) := by
    exact (integrableOn_comp_exp_Ioi g 0).2 (hg.mono_set (by intro x hx; exact lt_trans (Real.exp_pos 0) (by simpa using hx)))
  exact hIio.union hIoi

/-- disjointness of the split pieces of `(0,∞)`. -/
lemma disjoint_Iio_Ioi : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  change x < 0 at hx1
  change 0 < x at hx2
  linarith

/-- disjointness of the split pieces of `(0,∞)`. -/
lemma disjoint_Ioo_singleton : Disjoint (Ioo (0 : ℝ) 1) ({1} : Set ℝ) := by
  rw [Set.disjoint_left]
  intro x hx1 hxs
  change 0 < x ∧ x < 1 at hx1
  have hxs' : x = 1 := Set.mem_singleton_iff.mp hxs
  linarith

/-- disjointness of the split pieces of `(0,∞)`. -/
lemma disjoint_IooIoi_singleton : Disjoint (Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) (Ioi 1) := by
  rw [Set.disjoint_left]
  intro x hxAC hxB
  change 1 < x at hxB
  rcases hxAC with hxA | hxs
  · change 0 < x ∧ x < 1 at hxA
    linarith
  · have hxs' : x = 1 := Set.mem_singleton_iff.mp hxs
    linarith

/-- `∫_{(0,1)} g + ∫_{(1,∞)} g = ∫_{(0,∞)} g`. -/
lemma integral_Ioi_eq_add (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    (∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in Ioi 1, g y) = ∫ y in Ioi 0, g y := by
  have hA : IntegrableOn g (Ioo (0 : ℝ) 1) := hg.mono_set (by intro x hx; exact hx.1)
  have hB : IntegrableOn g (Ioi 1) := hg.mono_set (by intro x hx; exact lt_trans zero_lt_one (by simpa using hx))
  have hC : IntegrableOn g ({1} : Set ℝ) := hg.mono_set (by intro x hx; simp at hx; simp [hx])
  have hsing : (∫ y in ({1} : Set ℝ), g y) = 0 := by
    rw [MeasureTheory.integral_singleton]
    have hvol : volume.real ({1} : Set ℝ) = 0 := by
      change (volume ({1} : Set ℝ)).toReal = 0
      rw [MeasureTheory.measure_singleton (x := (1 : ℝ))]
      simp
    rw [hvol]
    simp
  have hAC : (∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in ({1} : Set ℝ), g y)
      = ∫ y in Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ), g y := by
    exact (MeasureTheory.setIntegral_union (s := Ioo (0 : ℝ) 1) (t := ({1} : Set ℝ))
      disjoint_Ioo_singleton (measurableSet_singleton 1) hA hC).symm
  have hACB : (∫ y in Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ), g y) + (∫ y in Ioi 1, g y)
      = ∫ y in (Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) ∪ Ioi 1, g y := by
    exact (MeasureTheory.setIntegral_union (s := Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) (t := Ioi 1)
      disjoint_IooIoi_singleton measurableSet_Ioi (hA.union hC) hB).symm
  calc
    (∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in Ioi 1, g y)
        = ((∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in ({1} : Set ℝ), g y)) + (∫ y in Ioi 1, g y) := by
          rw [hsing]
          ring
    _ = (∫ y in Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ), g y) + (∫ y in Ioi 1, g y) := by rw [hAC]
    _ = ∫ y in (Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) ∪ Ioi 1, g y := hACB
    _ = ∫ y in Ioi 0, g y := by rw [Ioi_eq_union]

/-- integral of `x ↦ e^x • g(e^x)` over the two half-lines equals `∫_{(0,∞)} g`. -/
lemma integral_comp_exp_union (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    (∫ x in Iio 0 ∪ Ioi 0, phi g x) = ∫ y in Ioi 0, g y := by
  calc
    (∫ x in Iio 0 ∪ Ioi 0, phi g x)
        = (∫ x in Iio 0, phi g x) + (∫ x in Ioi 0, phi g x) := by
          have hpieces := MeasureTheory.integrableOn_union.mp (integrable_comp_exp_union g hg)
          exact MeasureTheory.setIntegral_union (s := Iio (0 : ℝ)) (t := Ioi 0)
            disjoint_Iio_Ioi measurableSet_Ioi hpieces.1 hpieces.2
    _ = (∫ y in Ioo 0 1, g y) + (∫ y in Ioi 1, g y) := by
          change (∫ x in Iio 0, Real.exp x • g (Real.exp x)) + (∫ x in Ioi 0, Real.exp x • g (Real.exp x))
            = (∫ y in Ioo 0 1, g y) + (∫ y in Ioi 1, g y)
          rw [integral_comp_exp_Iio g 0, integral_comp_exp_Ioi g 0]
          norm_num
    _ = ∫ y in Ioi 0, g y := integral_Ioi_eq_add g hg

/-- whole-line substitution: `∫_ℝ e^x • g(e^x) = ∫_{(0,∞)} g`. -/
lemma integral_comp_exp (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    (∫ x : ℝ, phi g x) = ∫ y in Ioi 0, g y := by
  calc
    (∫ x : ℝ, phi g x) = ∫ x in (Set.univ : Set ℝ), phi g x := by simp
    _ = ∫ x in (Iio 0 ∪ Ioi 0), phi g x :=
      (MeasureTheory.setIntegral_congr_set Iio_union_Ioi_ae_univ).symm
    _ = ∫ y in Ioi 0, g y := integral_comp_exp_union g hg

/-- whole-line integrability of `x ↦ e^x • g(e^x)`. -/
lemma integrable_comp_exp (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) : Integrable (phi g) := by
  have hunion : IntegrableOn (phi g) (Iio 0 ∪ Ioi 0) := integrable_comp_exp_union g hg
  have huniv : IntegrableOn (phi g) (Set.univ : Set ℝ) := hunion.congr_set_ae Iio_union_Ioi_ae_univ.symm
  exact (MeasureTheory.integrableOn_univ).mp huniv

/-- `∫_ℝ Hs s = Γ(s)` for `0 < Re s`. -/
lemma integral_Hs (s : ℂ) (hs : 0 < s.re) : (∫ x : ℝ, Hs s x) = Complex.Gamma s := by
  have hφ : (fun x : ℝ => Hs s x) = phi (J0 s) := by
    funext x
    exact GRBase.Hs_smul s x
  rw [hφ]
  rw [integral_comp_exp (J0 s) (integrable_J0 s hs)]
  have hg : (∫ y in Ioi 0, J0 s y) = Complex.GammaIntegral s := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => J0_eq_GammaIntegrand s y hy)]
    rfl
  rw [hg, ← Complex.Gamma_eq_integral hs]

/-- `∫_ℝ Hr s θ = e^{-iθs}·∫_{(0,∞)} Jr s θ`. -/
lemma integral_Hr (s : ℂ) (θ : ℝ) (hs : 0 < s.re) (hθ : |θ| < Real.pi / 2) :
    (∫ x : ℝ, Hr s θ x) = cexp (-((I * (θ : ℂ)) * s)) * (∫ y in Ioi 0, Jr s θ y) := by
  have hφ : (fun x : ℝ => Hr s θ x) = fun x => cexp (-((I * (θ : ℂ)) * s)) * phi (Jr s θ) x := by
    funext x
    exact GRBase.Hr_smul s θ x
  rw [hφ]
  rw [MeasureTheory.integral_const_mul (cexp (-((I * (θ : ℂ)) * s))) (phi (Jr s θ))]
  rw [integral_comp_exp (Jr s θ) (integrable_Jr s hs hθ)]

/-- `Hs s` is integrable over `ℝ`. -/
lemma integrable_Hs (s : ℂ) (hs : 0 < s.re) : Integrable (Hs s) := by
  have hφ : (fun x : ℝ => Hs s x) = phi (J0 s) := by
    funext x
    exact GRBase.Hs_smul s x
  change Integrable (fun x : ℝ => Hs s x)
  rw [hφ]
  exact integrable_comp_exp (J0 s) (integrable_J0 s hs)

/-- `Hr s θ` is integrable over `ℝ`. -/
lemma integrable_Hr (s : ℂ) (θ : ℝ) (hs : 0 < s.re) (hθ : |θ| < Real.pi / 2) :
    Integrable (Hr s θ) := by
  have hφ : (fun x : ℝ => Hr s θ x) = fun x => cexp (-((I * (θ : ℂ)) * s)) * phi (Jr s θ) x := by
    funext x
    exact GRBase.Hr_smul s θ x
  change Integrable (fun x : ℝ => Hr s θ x)
  rw [hφ]
  have hf : Integrable (phi (Jr s θ)) := integrable_comp_exp (Jr s θ) (integrable_Jr s hs hθ)
  exact hf.const_mul (cexp (-((I * (θ : ℂ)) * s)))

end
end GRSubst

open Complex Filter MeasureTheory Set
open scoped Real Topology Interval
open GRBase
open GRVert
open GRSubst
namespace GRRect

open GRBase
open GRVert
open GRSubst

noncomputable section

/-- `F s z = e^{-e^z}·e^{s·z}` (the pullback of the Γ integrand to the `z`-plane). -/
noncomputable def F (s : ℂ) (z : ℂ) : ℂ := cexp (-cexp z) * cexp (s * z)

/-- `F s` is entire. -/
lemma F_differentiable (s : ℂ) : Differentiable ℂ (F s) := by
  unfold F
  fun_prop

/-- The finite-rectangle boundary identity, expanded in the horizontal/vertical edge integrals.
The corners are `z = -T` (bottom-left) and `w = T - iθ` (top-right). -/
lemma rectBoundary_horizontal (s : ℂ) (θ : ℝ) (T : ℝ) :
    AfeRect.rectBoundary (-(T : ℂ)) ((T : ℂ) - (θ : ℂ) * I) (F s)
      = (∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x)
        + I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y) := by
  unfold AfeRect.rectBoundary
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_I_re, Complex.mul_I_im, zero_sub, neg_zero, sub_zero]
  have h1 : (∫ x in (-T)..T, F s ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) = ∫ x in (-T)..T, Hs s x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have harg : (x : ℂ) + ((0 : ℝ) : ℂ) * I = (x : ℂ) := by norm_num
    simp only [F, Hs, harg]
  have h2 : (∫ x in (-T)..T, F s ((x : ℂ) + ((-θ : ℝ) : ℂ) * I)) = ∫ x in (-T)..T, Hr s θ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have harg : (x : ℂ) + ((-θ : ℝ) : ℂ) * I = (x : ℂ) - (θ : ℂ) * I := by
      rw [Complex.ofReal_neg]
      ring
    simp only [F, Hr, harg]
  have h3 : (∫ y in 0..(-θ), F s (((T : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) = ∫ y in 0..(-θ), V s T y := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [F, V]
  have h4 : (∫ y in 0..(-θ), F s ((((-T : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * I)) = ∫ y in 0..(-θ), V s (-T) y := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [F, V]
  rw [h1, h2, h3, h4]

/-- bottom edge of the Γ-contour rectangle tends to `Γ(s)` as `T → ∞`. -/
lemma tendsto_bottom (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hs s x) atTop (𝓝 (Complex.Gamma s)) := by
  have h : Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hs s x) atTop
      (𝓝 (∫ x : ℝ, Hs s x)) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral (integrable_Hs s hs)
      tendsto_neg_atTop_atBot tendsto_id
  simpa [integral_Hs s hs] using h

/-- top edge of the Γ-contour rectangle tends to `e^{-iθs}·∫ Jr` as `T → ∞`. -/
lemma tendsto_top (s : ℂ) (θ : ℝ) (hs : 0 < s.re) (hθ : |θ| < Real.pi / 2) :
    Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hr s θ x) atTop
      (𝓝 (cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) := by
  have h : Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hr s θ x) atTop
      (𝓝 (∫ x : ℝ, Hr s θ x)) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral (integrable_Hr s θ hs hθ)
      tendsto_neg_atTop_atBot tendsto_id
  simpa [integral_Hr s θ hs hθ] using h

/-- **T1**: the rotated-contour identity `Γ(s) = e^{-iθs}·∫_{(0,∞)} e^{-r e^{-iθ}} r^{s-1} dr`. -/
theorem gamma_eq_Jr_integral (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Complex.Gamma s = cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r) := by
  have hrect : ∀ T : ℝ, AfeRect.rectBoundary (-(T : ℂ)) ((T : ℂ) - (θ : ℂ) * I) (F s) = 0 := by
    intro T
    exact AfeRect.rectBoundary_eq_zero_of_differentiableOn (F s) (-(T : ℂ))
      ((T : ℂ) - (θ : ℂ) * I) (F_differentiable s).differentiableOn
  let E : ℝ → ℂ := fun T => ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
      + (I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y))
  have hE0 : ∀ T : ℝ, E T = 0 := by
    intro T
    have hz := hrect T
    rw [rectBoundary_horizontal s θ T] at hz
    dsimp [E]
    calc
      ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
          + (I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y))
          = ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
            + I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y) := by ring
      _ = 0 := hz
  have hEconst : Tendsto E atTop (𝓝 (0 : ℂ)) := by
    refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 (0 : ℂ))).congr' ?_
    exact Filter.Eventually.of_forall (fun T => (hE0 T).symm)
  have hBv := tendsto_bottom s hs
  have hPv := tendsto_top s θ hs hθ
  have hRv : Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s T y) atTop (𝓝 0) :=
    right_edge_tendsto s hs hθ
  have hLv : Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s (-T) y) atTop (𝓝 0) :=
    GRVert.left_edge_tendsto s hs hθ
  have htot : Tendsto E atTop
      (𝓝 (Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) := by
    have hsub : Tendsto (fun T : ℝ => (∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x)) atTop
        (𝓝 (Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) :=
      hBv.sub hPv
    have hR2 : Tendsto (fun T : ℝ => I • (∫ y in 0..(-θ), V s T y)) atTop (𝓝 (0 : ℂ)) := by
      simpa using hRv.const_smul I
    have hL2 : Tendsto (fun T : ℝ => I • (∫ y in 0..(-θ), V s (-T) y)) atTop (𝓝 (0 : ℂ)) := by
      simpa using hLv.const_smul I
    have hvert : Tendsto (fun T : ℝ =>
        I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y)) atTop (𝓝 (0 : ℂ)) := by
      simpa using hR2.sub hL2
    have htot' : Tendsto (fun T : ℝ => ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
        + (I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y))) atTop
        (𝓝 (Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) := by
      simpa using hsub.add hvert
    exact htot'.congr' (Filter.Eventually.of_forall (fun T => by rfl))
  have heq : (0 : ℂ) = Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r) :=
    tendsto_nhds_unique hEconst htot
  exact sub_eq_zero.mp heq.symm

/-- The norm form of the rotation identity (`rot_estimate`):
`|Γ(s)| ≤ Γ(Re s)·e^{θ·Im s}·(cos θ)^{-Re s}`. -/
theorem rot_estimate (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    ‖Complex.Gamma s‖ ≤ (Real.Gamma s.re) * Real.exp (θ * s.im) * (Real.cos θ) ^ (-s.re) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hmain := gamma_eq_Jr_integral s hs hθ
  have hnorm_exp : ‖cexp (-((I * (θ : ℂ)) * s))‖ = Real.exp (θ * s.im) := by
    rw [Complex.norm_exp]
    congr 1
    have h₂ : re ((I * (θ : ℂ)) * s) = -(θ * s.im) := by
      rw [show (I * (θ : ℂ)) * s = I * ((θ : ℂ) * s) by ring]
      rw [Complex.I_mul_re]
      congr 1
      simp
    rw [Complex.neg_re, h₂]
    ring
  have hJr : (∫ r in Ioi 0, ‖Jr s θ r‖) = ∫ r in Ioi 0, Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    exact norm_Jr s θ r hr
  have hval : (∫ r in Ioi 0, Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1))
      = (Real.cos θ) ^ (-s.re) * Real.Gamma s.re := by
    have hlib := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s.re) (r := Real.cos θ) hs hcos
    -- hlib : ∫ t in Ioi 0, t ^ (s.re - 1) * exp (-(cos θ * t)) = (1 / cos θ) ^ s.re * Gamma s.re
    have hrew : (1 / Real.cos θ) ^ s.re = (Real.cos θ) ^ (-s.re) := by
      rw [one_div, Real.inv_rpow (le_of_lt hcos), (Real.rpow_neg (le_of_lt hcos) s.re).symm]
    calc
      (∫ r in Ioi 0, Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1))
          = ∫ r in Ioi 0, r ^ (s.re - 1) * Real.exp (-(Real.cos θ * r)) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro r hr
            congr 2
            ring
      _ = (1 / Real.cos θ) ^ s.re * Real.Gamma s.re := hlib
      _ = (Real.cos θ) ^ (-s.re) * Real.Gamma s.re := by rw [hrew]
  calc
    ‖Complex.Gamma s‖ = ‖cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r)‖ := by
      rw [hmain]
    _ = ‖cexp (-((I * (θ : ℂ)) * s))‖ * ‖(∫ r in Ioi 0, Jr s θ r)‖ := by rw [norm_mul]
    _ = Real.exp (θ * s.im) * ‖(∫ r in Ioi 0, Jr s θ r)‖ := by rw [hnorm_exp]
    _ ≤ Real.exp (θ * s.im) * (∫ r in Ioi 0, ‖Jr s θ r‖) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
      exact MeasureTheory.norm_integral_le_integral_norm (fun r => Jr s θ r)
    _ = Real.exp (θ * s.im) * ((Real.cos θ) ^ (-s.re) * Real.Gamma s.re) := by
      rw [hJr, hval]
    _ = Real.exp (θ * s.im) * (Real.Gamma s.re) * (Real.cos θ) ^ (-s.re) := by ring
    _ = (Real.Gamma s.re) * Real.exp (θ * s.im) * (Real.cos θ) ^ (-s.re) := by ring


end
end GRRect

open Filter
open scoped Real Topology
namespace AngleChoice

/-- Jordan-type bound: for `0 < σ` and `0 < d ≤ 1`,
`(sin d)^{-σ} ≤ (π/2)^σ · (1/d)^σ`.
Used twice: `d = 1/(1+|t|)`, so `1/d = 1 + |t|`. -/
private lemma sin_pow_neg_le (σ : ℝ) (hσ : 0 < σ) {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1) :
    (Real.sin d) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 / d) ^ σ := by
  have hdpi : d ≤ Real.pi / 2 := by linarith [hd', Real.two_le_pi]
  have hdpi' : d < Real.pi := by linarith [hd', Real.two_le_pi]
  have hsinpos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd hdpi'
  let a : ℝ := (2 / Real.pi) * d
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha_sin : a ≤ Real.sin d := by
    dsimp [a]
    exact Real.mul_le_sin hd.le hdpi
  have hsininv_le : (Real.sin d)⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hsinpos ha).2 ha_sin
  have ha_inv : a⁻¹ = (Real.pi / 2) * (1 / d) := by
    dsimp [a]
    field_simp [Real.pi_ne_zero, hd.ne']
  calc
    (Real.sin d) ^ (-σ) = (Real.sin d)⁻¹ ^ σ := by rw [Real.rpow_neg_eq_inv_rpow]
    _ ≤ a⁻¹ ^ σ := Real.rpow_le_rpow (inv_nonneg.mpr hsinpos.le) hsininv_le (le_of_lt hσ)
    _ = (Real.pi / 2 * (1 / d)) ^ σ := by rw [ha_inv]
    _ = (Real.pi / 2) ^ σ * (1 / d) ^ σ := Real.mul_rpow (le_of_lt Real.pi_div_two_pos) (by positivity)

/-- The case `0 ≤ t`: choose `θ = -π/2 + 1/(1+t)` (i.e. rotate clockwise by a little less
than a right angle). -/
private lemma bound_nonneg (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  rw [abs_of_nonneg ht]
  let θ : ℝ := -(Real.pi / 2) + 1 / (1 + t)
  have h1pt : 0 < 1 + t := by linarith
  have hu0 : 0 < 1 / (1 + t) := by exact div_pos zero_lt_one h1pt
  have hu1 : 1 / (1 + t) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + t)) := by
    dsimp [θ]
    rw [show -(Real.pi / 2) + 1 / (1 + t) = -(Real.pi / 2 - 1 / (1 + t)) by ring]
    rw [Real.cos_neg, Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + t))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := sin_pow_neg_le σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + t)) = 1 + t := by
    field_simp [h1pt.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + t) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + t))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + t) ^ σ := by rw [hrec]
  have hut : (1 / (1 + t)) * t ≤ 1 := by
    field_simp [h1pt.ne']
    linarith
  have hθt : θ * t ≤ -(Real.pi / 2) * t + 1 := by
    dsimp [θ]
    calc
      (-(Real.pi / 2) + 1 / (1 + t)) * t
          = -(Real.pi / 2) * t + (1 / (1 + t)) * t := by ring
      _ ≤ -(Real.pi / 2) * t + 1 := add_le_add_right hut (-(Real.pi / 2) * t)
  have hA : Real.exp (θ * t) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by
    calc
      Real.exp (θ * t) ≤ Real.exp (-(Real.pi / 2) * t + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * t) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * t))).le
  have hcomb : Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + t) ^ σ * Real.exp (-(Real.pi / 2) * t) := by ring⟩

/-- The case `t ≤ 0`: choose `θ = π/2 - 1/(1-t)` (rotate counterclockwise). -/
private lemma bound_nonpos (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : t ≤ 0) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  let s : ℝ := -t
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hts : t = -s := by dsimp [s]; ring
  have habs : |t| = s := by
    dsimp [s]
    rw [abs_of_nonpos ht]
  rw [habs, hts]
  let θ : ℝ := Real.pi / 2 - 1 / (1 + s)
  have h1ps : 0 < 1 + s := by linarith
  have hu0 : 0 < 1 / (1 + s) := by exact div_pos zero_lt_one h1ps
  have hu1 : 1 / (1 + s) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
    · dsimp [θ]; linarith
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + s)) := by
    dsimp [θ]
    rw [Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + s))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := sin_pow_neg_le σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + s)) = 1 + s := by
    field_simp [h1ps.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + s) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + s))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + s) ^ σ := by rw [hrec]
  have hus : (1 / (1 + s)) * s ≤ 1 := by
    field_simp [h1ps.ne']
    linarith
  have hθt : θ * (-s) ≤ -(Real.pi / 2) * s + 1 := by
    dsimp [θ]
    calc
      (Real.pi / 2 - 1 / (1 + s)) * (-s)
          = -(Real.pi / 2) * s + (1 / (1 + s)) * s := by ring
      _ ≤ -(Real.pi / 2) * s + 1 := add_le_add_right hus (-(Real.pi / 2) * s)
  have hA : Real.exp (θ * (-s)) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by
    calc
      Real.exp (θ * (-s)) ≤ Real.exp (-(Real.pi / 2) * s + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * s) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * s))).le
  have hcomb : Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + s) ^ σ * Real.exp (-(Real.pi / 2) * s) := by ring⟩

/-- The rotation-angle bound: for every `σ > 0` there is `C > 0` such that for every real `t`
there is an admissible rotation angle `θ` (`|θ| < π/2`, `cos θ > 0`) with

`e^{θt}·(cos θ)^{-σ} ≤ C·(1+|t|)^σ·e^{-π|t|/2}`. -/
theorem angle_choice (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∃ θ : ℝ,
      |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
        Real.exp (θ * t) * (Real.cos θ) ^ (-σ)
          ≤ C * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  refine ⟨Real.exp 1 * (Real.pi / 2) ^ σ, ?_, ?_⟩
  · exact mul_pos (Real.exp_pos 1) (Real.rpow_pos_of_pos Real.pi_div_two_pos σ)
  · intro t
    rcases le_total 0 t with ht | ht
    · exact bound_nonneg σ hσ ht
    · exact bound_nonpos σ hσ ht

end AngleChoice

/--
Uniform exponential decay of the Gamma function on the vertical line
`Re s = σ > 0`: `|Γ(σ + i t)| ≤ C(σ)·(1+|t|)^σ·e^{−π|t|/2}` for all real `t`.

## Proof outline

* **rotated contour.**  In `AfeRect`/`GRBase`/`GRVert`/`GRRealInt`/`GRSubst`/`GRRect`
  we prove, for `0 < Re s` and `|θ| < π/2`, the contour-rotation estimate
  `‖Γ(s)‖ ≤ Γ(Re s)·e^{θ·Im s}·(cos θ)^{-Re s}` (`GRRect.rot_estimate`): it follows
  from Cauchy-Goursat on the rectangle with corners `(-T,0)`, `(T,-θ)` for the entire
  integrand `e^{-e^z}·e^{s z}`, whose horizontal edges are the real-line pullbacks of the
  unrotated / rotated Euler integrands and whose vertical edges tend to zero.

* **optimizing the angle.**  In `AngleChoice.angle_choice` we choose
  `θ = ∓(π/2 - 1/(1+|t|))`, which yields
  `e^{θt}·(cos θ)^{-σ} ≤ C(σ)·(1+|t|)^σ·e^{-π|t|/2}` by elementary trigonometry.

* The final theorem composes the two estimates.
-/
theorem gamma_vertical_exp_decay (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ ≤
        C * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  rcases AngleChoice.angle_choice σ hσ with ⟨C₀, hC₀, hC₀body⟩
  refine ⟨Real.Gamma σ * C₀, mul_pos (Real.Gamma_pos_of_pos hσ) hC₀, ?_⟩
  intro t
  rcases hC₀body t with ⟨θ, hθabs, hθcos, hθb⟩
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hs0 : 0 < s.re := by
    dsimp [s]; simp [hσ]
  have hest := GRRect.rot_estimate s hs0 hθabs
  have h₁ : ‖Complex.Gamma s‖ ≤
      (Real.Gamma σ) * (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) := by
    have hre : s.re = σ := by simp [s]
    have him : s.im = t := by simp [s]
    rw [hre, him] at hest
    rw [← mul_assoc]
    exact hest
  have h₂ : (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) ≤
      C₀ * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
    simpa [mul_assoc] using hθb
  calc
    ‖Complex.Gamma s‖ ≤ (Real.Gamma σ) * (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) := h₁
    _ ≤ (Real.Gamma σ) * (C₀ * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|)) := by
      exact mul_le_mul_of_nonneg_left h₂ (le_of_lt (Real.Gamma_pos_of_pos hσ))
    _ = (Real.Gamma σ * C₀) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
      ring


end

end Commons.Analysis.SpecialFunctions.Gamma