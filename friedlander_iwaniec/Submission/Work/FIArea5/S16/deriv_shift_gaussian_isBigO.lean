import Mathlib

/-!
# Decay of the `a`-th derivative of a shifted Gaussian

The entire function `w ↦ A^{-1/2} e^{-(π/A)(w+ib)²}` (for `re A > 0`) and all of its derivatives
decay faster than any power of `|ξ|` along the real axis.

The proof is Cauchy's estimate for derivatives: the `a`-th derivative at a real point `ξ` is
bounded by `a!` times the supremum of the modulus on the circle of radius `1` about `ξ`, and that
supremum is `≤ const · e^{-σ ξ²}` with `σ > 0`, since the real part of the quadratic exponent is
a negative definite quadratic form; exponentials beat every power.
-/

namespace Work.FIArea5.S16

open scoped Topology
open Filter Asymptotics
open Complex

/-- Cauchy's estimate for the `n`-th derivative of an entire function, on the circle of radius
`1`: if `‖f‖ ≤ C` on that circle then `‖f^{(n)}‖ ≤ n! · C` at the centre. -/
private lemma iteratedDeriv_le_of_sphere {f : ℂ → ℂ} (hdiff : Differentiable ℂ f) (n : ℕ)
    {c : ℂ} {C : ℝ} (hC : ∀ z ∈ Metric.sphere c 1, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) n
    (show (0:ℝ) < 1 by norm_num) hdiff.diffContOnCl hC
  simpa using h

/-- Explicit form of the real part of the quadratic exponent `-(π/A)(z+ib)²`. -/
private lemma re_neg_div_mul_sq (A b z : ℂ) :
    (-Real.pi / A * (z + Complex.I * b) ^ 2).re
      = -((Real.pi / A).re) * (z.re - b.im) ^ 2 + ((Real.pi / A).re) * (z.im + b.re) ^ 2
        + 2 * ((Real.pi / A).im) * (z.re - b.im) * (z.im + b.re) := by
  set u : ℂ := z + Complex.I * b with hu
  have hre : u.re = z.re - b.im := by
    rw [hu]; simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]; ring
  have him : u.im = z.im + b.re := by
    rw [hu]; simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]; ring
  rw [← hre, ← him]
  rw [neg_div, Complex.mul_re, Complex.neg_re, Complex.neg_im, pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- Completing the square: for `c > 0` and `|Y| ≤ M`,
`-c X² + c Y² + 2 d X Y ≤ -(c/2) X² + (c M² + 2 d² M² / c)`. -/
private lemma quad_est (c d M X Y : ℝ) (hc : 0 < c) (hY : |Y| ≤ M) :
    -c * X ^ 2 + c * Y ^ 2 + 2 * d * X * Y ≤ -(c / 2) * X ^ 2 + (c * M ^ 2 + 2 * d ^ 2 * M ^ 2 / c) := by
  have h1 : 2 * d * X * Y ≤ (c / 2) * X ^ 2 + (2 * d ^ 2 / c) * Y ^ 2 := by
    have hmain : c * (2 * d * X * Y) ≤ c * ((c / 2) * X ^ 2 + (2 * d ^ 2 / c) * Y ^ 2) := by
      have heq : c * ((c / 2) * X ^ 2 + (2 * d ^ 2 / c) * Y ^ 2) = (c ^ 2 / 2) * X ^ 2 + 2 * d ^ 2 * Y ^ 2 := by
        field_simp
      rw [heq]
      nlinarith [sq_nonneg (c * X - 2 * d * Y)]
    exact le_of_mul_le_mul_left hmain hc
  have hY2 : Y ^ 2 ≤ M ^ 2 := by
    nlinarith [abs_nonneg Y, le_abs_self Y, neg_abs_le Y, sq_abs Y, sq_abs M]
  have h2 : (c + 2 * d ^ 2 / c) * Y ^ 2 ≤ c * M ^ 2 + 2 * d ^ 2 * M ^ 2 / c := by
    have heq : (c + 2 * d ^ 2 / c) * M ^ 2 = c * M ^ 2 + 2 * d ^ 2 * M ^ 2 / c := by
      field_simp
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hY2 (by positivity)
  linarith [h1, h2]

private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

/-- Pointwise bound for the exponential factor on the circle of radius `1` about a real `ξ`. -/
private lemma sphere_shift_gaussian_bound' {A : ℂ} (hA : 0 < A.re) (b : ℂ) {ξ : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (ξ : ℂ) 1) (hξ : 2 * (1 + |b.im|) ≤ |ξ|) :
    ‖Complex.exp (-Real.pi / A * (z + Complex.I * b) ^ 2)‖
      ≤ Real.exp (-((Real.pi / A).re / 8) * ξ ^ 2)
          * Real.exp ((Real.pi / A).re * (1 + |b.re|) ^ 2
              + 2 * (Real.pi / A).im ^ 2 * (1 + |b.re|) ^ 2 / (Real.pi / A).re) := by
  have hA0 : A ≠ 0 := by intro h; rw [h] at hA; simp at hA
  have hc : 0 < (Real.pi / A).re := by
    have hn : 0 < Complex.normSq A := Complex.normSq_pos.mpr hA0
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    positivity
  have hd := hz
  rw [Metric.mem_sphere, Complex.dist_eq] at hd
  have hzim : |z.im| ≤ 1 := by
    have h := Complex.abs_im_le_norm (z - (ξ : ℂ))
    rw [hd] at h
    simpa using h
  have hzre : |z.re - ξ| ≤ 1 := by
    have h := Complex.abs_re_le_norm (z - (ξ : ℂ))
    rw [hd] at h
    simpa using h
  have hX : |ξ| / 2 ≤ |z.re - b.im| := by
    have hA1 : |(z.re - ξ) - b.im| ≤ 1 + |b.im| := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hzre, le_abs_self (z.re - ξ), neg_abs_le (z.re - ξ),
        le_abs_self b.im, neg_abs_le b.im]
    have heq : ξ = (z.re - b.im) - ((z.re - ξ) - b.im) := by ring
    have hB1 : |ξ| ≤ |z.re - b.im| + (1 + |b.im|) := by
      calc |ξ| = |(z.re - b.im) - ((z.re - ξ) - b.im)| := congrArg (fun t : ℝ => |t|) heq
        _ ≤ |z.re - b.im| + |(z.re - ξ) - b.im| := abs_sub_le_abs_add _ _
        _ ≤ |z.re - b.im| + (1 + |b.im|) := by linarith
    linarith
  have hY : |z.im + b.re| ≤ 1 + |b.re| := by
    calc |z.im + b.re| ≤ |z.im| + |b.re| := abs_add_le _ _
      _ ≤ 1 + |b.re| := by linarith
  have hquad : -((Real.pi / A).re) * (z.re - b.im) ^ 2 + ((Real.pi / A).re) * (z.im + b.re) ^ 2
      + 2 * ((Real.pi / A).im) * (z.re - b.im) * (z.im + b.re)
      ≤ -((Real.pi / A).re / 8) * ξ ^ 2
        + ((Real.pi / A).re * (1 + |b.re|) ^ 2
            + 2 * ((Real.pi / A).im) ^ 2 * (1 + |b.re|) ^ 2 / (Real.pi / A).re) := by
    have h := quad_est ((Real.pi / A).re) ((Real.pi / A).im) (1 + |b.re|) (z.re - b.im) (z.im + b.re) hc hY
    have hsq : ξ ^ 2 / 4 ≤ (z.re - b.im) ^ 2 := by
      nlinarith [abs_nonneg (z.re - b.im), abs_nonneg ξ, sq_abs (z.re - b.im), sq_abs ξ, hX]
    nlinarith [h, hsq, hc]
  rw [Complex.norm_exp, re_neg_div_mul_sq, ← Real.exp_add, Real.exp_le_exp]
  exact hquad

/-- A Gaussian decays faster than any power of `|ξ|` along the cocompact filter. -/
private lemma exp_neg_sq_isBigO_rpow (σ : ℝ) (hσ : 0 < σ) (B : ℝ) :
    (fun ξ : ℝ => Real.exp (-σ * ξ ^ 2)) =O[Filter.cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-B)) := by
  have h1 : ∀ᶠ y : ℝ in atTop, y ^ B * Real.exp (-σ * y ^ 2) ≤ 1 := by
    have hlit : (fun y : ℝ => y ^ B * Real.exp (-σ * y ^ 2)) =o[atTop]
        (fun y : ℝ => Real.exp (-(1/2) * y)) := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hσ B
    have htend : Tendsto (fun y : ℝ => Real.exp (-(1/2) * y)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/2))
      simpa [Function.comp_def, neg_mul] using h
    have hlim := hlit.tendsto_zero_of_tendsto htend
    have := hlim.eventually (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))
    filter_upwards [this] with y hy
    exact le_of_lt hy
  have h2 : ∀ᶠ ξ : ℝ in Filter.cocompact ℝ, ‖ξ‖ ^ B * Real.exp (-σ * ‖ξ‖ ^ 2) ≤ 1 :=
    tendsto_norm_cocompact_atTop.eventually h1
  have h3 : ∀ᶠ ξ : ℝ in Filter.cocompact ℝ, (1 : ℝ) ≤ ‖ξ‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h2, h3] with ξ h2 h3
  simp only [Real.norm_eq_abs, sq_abs] at h2 h3 ⊢
  have hxpos : 0 < |ξ| := by linarith
  have htB : 0 < |ξ| ^ B := Real.rpow_pos_of_pos hxpos B
  rw [abs_of_nonneg (Real.exp_pos _).le,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) (-B)), one_mul]
  have key : Real.exp (-σ * ξ ^ 2) ≤ 1 / |ξ| ^ B := by
    rw [le_div_iff₀ htB]
    linarith [h2]
  rwa [one_div, ← Real.rpow_neg (abs_nonneg ξ) B] at key

/-- The `a`-th derivative of the shifted Gaussian `w ↦ A^{-1/2} e^{-(π/A)(w+ib)²}` (an entire function of `w`, restricted to the real axis) decays faster than any power of `|ξ|`. Equivalently the Fourier transform of `x ↦ x^a e^{-πAx²+2πbx}` decays faster than any power, since by `Work.FIArea5.S16.fourier_gaussian_poly` the two differ by the constant `(i/2π)^a`. Proved by Cauchy's estimate for derivatives on the circle of radius `1` about `ξ`. -/
theorem deriv_shift_gaussian_isBigO {A : ℂ} (hA : 0 < A.re) (b : ℂ) (a : ℕ) {B : ℝ} :
    (fun ξ : ℝ => iteratedDeriv a (fun w : ℂ =>
        (1 / A ^ (1 / 2 : ℂ)) * Complex.exp (-Real.pi / A * (w + Complex.I * b) ^ 2)) (ξ : ℂ))
      =O[Filter.cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-B)) := by
  set F : ℂ → ℂ := fun w => (1 / A ^ (1/2 : ℂ)) * Complex.exp (-Real.pi / A * (w + Complex.I * b)^2) with hF
  have hFdiff : Differentiable ℂ F := by rw [hF]; fun_prop
  have hA0 : A ≠ 0 := by intro h; rw [h] at hA; simp at hA
  have hc : 0 < (Real.pi / A).re := by
    have hn : 0 < Complex.normSq A := Complex.normSq_pos.mpr hA0
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    positivity
  have hcauchy : ∀ ξ : ℝ, 2 * (1 + |b.im|) ≤ |ξ| →
      ‖iteratedDeriv a F (ξ : ℂ)‖
        ≤ (a.factorial * ‖(1 / A ^ (1/2 : ℂ))‖ * Real.exp ((Real.pi/A).re * (1+|b.re|)^2
            + 2*((Real.pi/A).im)^2*(1+|b.re|)^2/((Real.pi/A).re)))
          * Real.exp (-((Real.pi/A).re/8) * ξ^2) := by
    intro ξ hξ
    have h1 : ‖iteratedDeriv a F (ξ : ℂ)‖ ≤ a.factorial *
        (‖(1 / A ^ (1/2 : ℂ))‖ * (Real.exp (-((Real.pi/A).re/8) * ξ^2)
          * Real.exp ((Real.pi/A).re * (1+|b.re|)^2 + 2*((Real.pi/A).im)^2*(1+|b.re|)^2/((Real.pi/A).re)))) := by
      refine iteratedDeriv_le_of_sphere hFdiff a (fun z hz => ?_)
      rw [hF, norm_mul]
      exact mul_le_mul_of_nonneg_left (sphere_shift_gaussian_bound' hA b hz hξ) (norm_nonneg _)
    calc ‖iteratedDeriv a F (ξ : ℂ)‖
        ≤ a.factorial * (‖(1 / A ^ (1/2 : ℂ))‖ * (Real.exp (-((Real.pi/A).re/8) * ξ^2)
          * Real.exp ((Real.pi/A).re * (1+|b.re|)^2 + 2*((Real.pi/A).im)^2*(1+|b.re|)^2/((Real.pi/A).re)))) := h1
      _ = (a.factorial * ‖(1 / A ^ (1/2 : ℂ))‖ * Real.exp ((Real.pi/A).re * (1+|b.re|)^2
            + 2*((Real.pi/A).im)^2*(1+|b.re|)^2/((Real.pi/A).re)))
          * Real.exp (-((Real.pi/A).re/8) * ξ^2) := by ring
  have hT : ∀ᶠ ξ : ℝ in Filter.cocompact ℝ, 2 * (1 + |b.im|) ≤ |ξ| := by
    have h := (tendsto_norm_cocompact_atTop (E := ℝ)).eventually (eventually_ge_atTop (2*(1+|b.im|)))
    simpa [Real.norm_eq_abs] using h
  have hstep : (fun ξ : ℝ => iteratedDeriv a F (ξ : ℂ)) =O[Filter.cocompact ℝ]
      (fun ξ : ℝ => (a.factorial * ‖(1 / A ^ (1/2 : ℂ))‖ * Real.exp ((Real.pi/A).re * (1+|b.re|)^2
            + 2*((Real.pi/A).im)^2*(1+|b.re|)^2/((Real.pi/A).re))) * Real.exp (-((Real.pi/A).re/8) * ξ^2)) := by
    refine IsBigO.of_bound' ?_
    filter_upwards [hT] with ξ hξ
    have h := hcauchy ξ hξ
    have hnorm : ‖(a.factorial * ‖(1 / A ^ (1/2 : ℂ))‖ * Real.exp ((Real.pi/A).re * (1+|b.re|)^2
            + 2*((Real.pi/A).im)^2*(1+|b.re|)^2/((Real.pi/A).re))) * Real.exp (-((Real.pi/A).re/8) * ξ^2)‖
        = (a.factorial * ‖(1 / A ^ (1/2 : ℂ))‖ * Real.exp ((Real.pi/A).re * (1+|b.re|)^2
            + 2*((Real.pi/A).im)^2*(1+|b.re|)^2/((Real.pi/A).re))) * Real.exp (-((Real.pi/A).re/8) * ξ^2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
    rw [hnorm]
    exact h
  exact hstep.trans ((exp_neg_sq_isBigO_rpow ((Real.pi/A).re/8) (by positivity) B).const_mul_left _)

end Work.FIArea5.S16
