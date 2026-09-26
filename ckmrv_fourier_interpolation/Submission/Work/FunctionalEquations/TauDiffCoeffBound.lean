import Mathlib
import Submission.Work.FunctionalEquations.TauDiffSetup

/-!
# Bound on the Dirichlet coefficients of `F(τ+1,x) - F(τ,x)`

The function `τ ↦ diffF S x τ = F(τ+1,x) - F(τ,x)` is `1`-periodic and holomorphic on
the upper half plane, hence expands as a Dirichlet series in `e^{2π i (k+1) τ}` with
coefficients

`c k = ∫ t in (0)..1, diffF S x (t + i y) * e^{-2π i (k+1) (t + i y)}`

(independently of the height `y > 0`).  Here we bound those coefficients using only the
strip bound on `F`: the integrand `τ ↦ diffF S x τ * e^{-2π i (k+1) τ}` is holomorphic
and `1`-periodic, so the integral over one period may be computed at the *halved* height
`y/2` (Cauchy's theorem on a rectangle, the two vertical sides cancelling by
periodicity).  At height `y/2` the strip bound gives `‖diffF‖ ≤ 2α (y/2)^{-β}` while the
exponential contributes `e^{2π(k+1)(y/2)} = e^{π(k+1)y}`, which is the statement.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap Interval

variable {n : ℕ} [NeZero n]

/-- The integrand `τ ↦ (F(τ+1,x) - F(τ,x)) e^{-2π i (k+1) τ}` of the `k`-th coefficient
integral. -/
noncomputable def coeffKernel (S : FunctionalEquationSolution n) (x : E n) (k : ℕ) : ℂ → ℂ :=
  fun τ => diffF S x τ * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ))

/-- The coefficient kernel is holomorphic on the upper half plane. -/
lemma coeffKernel_differentiableOn (S : FunctionalEquationSolution n) (x : E n) (k : ℕ) :
    DifferentiableOn ℂ (coeffKernel S x k) {τ : ℂ | 0 < τ.im} := by
  have hd : DifferentiableOn ℂ (diffF S x) {τ : ℂ | 0 < τ.im} := diffF_differentiableOn S x
  unfold coeffKernel
  exact hd.mul (by fun_prop)

/-- `e^{-2π i (k+1) (τ+1)} = e^{-2π i (k+1) τ}`. -/
lemma exp_shift_one (k : ℕ) (τ : ℂ) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * (τ + 1)))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)) := by
  have hone : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1))) = 1 := by
    have hcast : -(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1))
        = ((-(k : ℤ) - 1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hcast, Complex.exp_int_mul_two_pi_mul_I]
  have hsplit : -(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * (τ + 1))
      = -(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)
        + (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1))) := by ring
  rw [hsplit, Complex.exp_add, hone, mul_one]

/-- The coefficient kernel is `1`-periodic on the upper half plane. -/
lemma coeffKernel_periodic (S : FunctionalEquationSolution n) (x : E n) (k : ℕ) :
    ∀ τ : ℂ, 0 < τ.im → coeffKernel S x k (τ + 1) = coeffKernel S x k τ := by
  intro τ hτ
  have h1 : diffF S x (τ + 1) = diffF S x τ := diffF_periodic S x τ hτ
  unfold coeffKernel
  rw [h1, exp_shift_one k τ]

/-- **Contour shift for a holomorphic `1`-periodic function.**  The integral over one
period of a holomorphic `1`-periodic function on the upper half plane does not depend on
the height.  The proof applies Cauchy's theorem to the rectangle with corners `(y/2) i`
and `1 + y i`; the two horizontal sides give the two candidate values and the two
vertical sides cancel by periodicity. -/
lemma integral_shift_of_periodic (h : ℂ → ℂ)
    (hdiff : DifferentiableOn ℂ h {τ : ℂ | 0 < τ.im})
    (hper : ∀ τ : ℂ, 0 < τ.im → h (τ + 1) = h τ)
    {y : ℝ} (hy : 0 < y) :
    (∫ t in (0 : ℝ)..1, h ((t : ℂ) + (y : ℂ) * Complex.I))
      = ∫ t in (0 : ℝ)..1, h ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) := by
  have hset : ([[(((y / 2 : ℝ) : ℂ) * Complex.I).re, (1 + (y : ℂ) * Complex.I).re]]
        ×ℂ [[(((y / 2 : ℝ) : ℂ) * Complex.I).im, (1 + (y : ℂ) * Complex.I).im]])
      = ([[(0 : ℝ), 1]] ×ℂ [[(y / 2 : ℝ), y]]) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    norm_num
  have hrect0 : DifferentiableOn ℂ h ([[(0 : ℝ), 1]] ×ℂ [[(y / 2 : ℝ), y]]) := by
    refine hdiff.mono ?_
    intro τ hτ
    show 0 < τ.im
    rw [Complex.mem_reProdIm] at hτ
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),
      Set.uIcc_of_le (by linarith : y / 2 ≤ y), Set.mem_Icc] at hτ
    linarith [hτ.2.1]
  have hrect : DifferentiableOn ℂ h
      ([[(((y / 2 : ℝ) : ℂ) * Complex.I).re, (1 + (y : ℂ) * Complex.I).re]]
        ×ℂ [[(((y / 2 : ℝ) : ℂ) * Complex.I).im, (1 + (y : ℂ) * Complex.I).im]]) := by
    rw [hset]; exact hrect0
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h
    (((y / 2 : ℝ) : ℂ) * Complex.I) (1 + (y : ℂ) * Complex.I) hrect
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, add_zero, zero_add, sub_self] at hC
  have h34 : (∫ y' in (y / 2)..y, h (((1:ℝ):ℂ) + (y':ℂ) * Complex.I))
      = ∫ y' in (y / 2)..y, h (((0:ℝ):ℂ) + (y':ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y' hy'
    have hy'ge : y / 2 ≤ y' := by
      rw [Set.uIcc_of_le (by linarith : y / 2 ≤ y), Set.mem_Icc] at hy'
      exact hy'.1
    have hpos : 0 < ((y':ℂ) * Complex.I).im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero]
      linarith
    have hh := hper ((y':ℂ) * Complex.I) hpos
    simpa [Complex.ofReal_one, Complex.ofReal_zero, add_comm] using hh
  have h0 : (∫ x in (0:ℝ)..1, h ((x:ℂ) + ((y/2:ℝ):ℂ) * Complex.I))
      - (∫ x in (0:ℝ)..1, h ((x:ℂ) + (y:ℂ) * Complex.I)) = 0 := by
    rw [h34] at hC
    linear_combination hC
  exact (sub_eq_zero.mp h0).symm

/-- Pointwise bound for the coefficient kernel at height `y/2`: the strip hypothesis
bounds `‖diffF‖` by `2α (y/2)^{-β}` and the exponential has modulus
`e^{2π(k+1)(y/2)} = e^{π(k+1)y}`. -/
lemma coeffKernel_norm_le (S : FunctionalEquationSolution n) (x : E n) (k : ℕ)
    {α β : ℝ} (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β))
    {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖coeffKernel S x k ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by
  have hτim : ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I).im = y / 2 := by simp
  have hpos : 0 < ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I).im := by rw [hτim]; linarith
  have hF := norm_diffF_le S x hstrip _ hpos
  rw [hτim] at hF
  rw [coeffKernel, norm_mul, norm_exp_neg_two_pi_I_nat k t (y / 2)]
  have hexp : Real.exp (2 * Real.pi * ((k : ℝ) + 1) * (y / 2))
      = Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by congr 1; ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right hF (Real.exp_pos _).le

theorem TauDiffCoeffBound {n : ℕ} [NeZero n]
    (S : Work.FE.FunctionalEquationSolution n) (x : Work.FE.E n) (c : ℕ → ℂ)
    (hc : ∀ (k : ℕ) (y : ℝ), 0 < y → c k = ∫ t in (0 : ℝ)..1,
      Work.FunctionalEquations.diffF S x ((t : ℂ) + (y : ℂ) * Complex.I) * Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * ((t : ℂ) + (y : ℂ) * Complex.I))))
    {α β : ℝ}
    (hstrip : ∀ (τ : ℂ) (z : Work.FE.E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β))
    (k : ℕ) (y : ℝ) (hy : 0 < y) :
    ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by
  have hck : c k = ∫ t in (0 : ℝ)..1, coeffKernel S x k ((t : ℂ) + (y : ℂ) * Complex.I) := by
    rw [hc k y hy]
    simp only [coeffKernel]
  rw [hck, integral_shift_of_periodic (coeffKernel S x k) (coeffKernel_differentiableOn S x k)
    (coeffKernel_periodic S x k) hy]
  calc ‖∫ t in (0:ℝ)..1, coeffKernel S x k ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)‖
      ≤ (2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y)) * |1 - (0:ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun t _ => coeffKernel_norm_le S x k hstrip hy t)
    _ = 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by
        rw [sub_zero, abs_one, mul_one]

end Work.FunctionalEquations
