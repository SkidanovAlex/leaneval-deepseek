import Mathlib
import Submission.Work.Asymptotics.CuspDecay.PsiDefs
import Submission.Work.Asymptotics.CuspDecay.E4Fun_second_order_im_ge_two
import Submission.Work.Asymptotics.CuspDecay.E6Fun_second_order_im_ge_two

/-!
# Quantitative bounds for `Ψ = q j` on the region `Im ≥ 2`

On `Im u ≥ 2` we have `x := ‖q u‖ ≤ e^{-4π} ≤ 10^{-5}`, so the `q`-expansions of `E₄`, `E₆`
(second order, with **explicit** constants) give

* `Λ u := Δ u / q u` satisfies `‖Λ u - 1‖ ≤ 400 x`, hence also `1/2 ≤ ‖Λ u‖ ≤ 2`,
* `Ψ u = E₄ u³ / Λ u` satisfies `‖Ψ u - 1‖ ≤ 1/4`,
* `‖D Ψ u‖ ≤ 800 ‖q u‖` where `D Ψ = E₄² (q/Δ) (E₄ - E₆)` (`normalizedDeriv_Psi`).

The last two are the inputs to the Lipschitz bound for `Ψ` on `Im ≥ 2` used in
`j_sub_lower_lattice`.  The key algebraic identity is
`Δ = (E₄³ - E₆²)/1728` together with `E₄ = 1 + 240q + r₄`, `E₆ = 1 - 504q + r₆` where
`‖r₄‖ ≤ 4000 x²` and `‖r₆‖ ≤ 40000 x²`.
-/

noncomputable section

open UpperHalfPlane
open scoped Manifold

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-- `‖q u‖ = e^{-2π Im u}`. -/
lemma norm_qParamFun_eq_exp (u : UpperHalfPlane) :
    ‖qParamFun u‖ = Real.exp (-(2 * Real.pi * u.im)) := by
  rw [qParamFun_eq_exp, Complex.norm_exp]
  congr 1
  have hrw : 2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)
      = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (u : ℂ)) := by push_cast; ring
  rw [hrw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_mul_re,
    Complex.I_mul_im, UpperHalfPlane.coe_im]
  ring

/-- `e^{-4π} ≤ 10^{-5}`. -/
lemma exp_neg_four_pi_le : Real.exp (-(4 * Real.pi)) ≤ 1 / 100000 := by
  have h12 : (100000 : ℝ) ≤ Real.exp 12 := by
    have h6 : (400 : ℝ) ≤ Real.exp 6 := by
      have h : Real.exp 6 = (Real.exp 1) ^ 6 := by
        rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h]
      have h' : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
      have h'' : (400 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
      linarith
    have h : Real.exp 12 = (Real.exp 6) ^ 2 := by
      rw [show (12 : ℝ) = (2 : ℕ) * 6 by norm_num, Real.exp_nat_mul]
    rw [h]; nlinarith
  have hle : Real.exp (-(4 * Real.pi)) ≤ Real.exp (-12) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_gt_three]
  have hprod : Real.exp 12 * Real.exp (-12) = 1 := by rw [← Real.exp_add]; norm_num
  have hpos : 0 < Real.exp (-12) := Real.exp_pos _
  have : Real.exp (-12) ≤ 1 / 100000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h12
  linarith

/-- `‖q u‖ ≤ 10^{-5}` for `Im u ≥ 2`. -/
lemma norm_qParamFun_le_1e5 (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖qParamFun u‖ ≤ 1 / 100000 := by
  rw [norm_qParamFun_eq_exp]
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_four_pi_le
  nlinarith [Real.pi_pos, hu]

/-- The `q`-parameter is nonzero. -/
lemma qParamFun_ne_zero (u : UpperHalfPlane) : qParamFun u ≠ 0 :=
  Complex.exp_ne_zero _

/-- `Ψ u = E₄ u³ / Λ u` with `Λ u = Δ u / q u`. -/
lemma Psi_eq_E4_cube_div_Lambda (u : UpperHalfPlane) :
    Psi u = E4Fun u ^ 3 / (DeltaFun u / qParamFun u) := by
  rw [Psi_apply, show jInvariantFun u = E4Fun u ^ 3 / DeltaFun u from rfl]
  field_simp

/-- `Λ - 1 = O(q)` with explicit constant, where `Λ u = Δ u / q u`. -/
lemma DeltaFun_div_q_sub_one_le (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖DeltaFun u / qParamFun u - 1‖ ≤ 400 * ‖qParamFun u‖ := by
  have hxle : ‖qParamFun u‖ ≤ 1 / 100000 := norm_qParamFun_le_1e5 u hu
  have hx0 : 0 ≤ ‖qParamFun u‖ := norm_nonneg _
  have hqne : qParamFun u ≠ 0 := qParamFun_ne_zero u
  set q := qParamFun u with hq
  set r4 := E4Fun u - 1 - 240 * q with hr4
  set r6 := E6Fun u - 1 + 504 * q with hr6
  have h4 : ‖r4‖ ≤ 4000 * ‖q‖ ^ 2 := E4Fun_second_order_im_ge_two u hu
  have h6 : ‖r6‖ ≤ 40000 * ‖q‖ ^ 2 := E6Fun_second_order_im_ge_two u hu
  have hE4 : E4Fun u = 1 + 240 * q + r4 := by rw [hr4]; ring
  have hE6 : E6Fun u = 1 - 504 * q + r6 := by rw [hr6]; ring
  have hDelta : DeltaFun u = (E4Fun u ^ 3 - E6Fun u ^ 2) / 1728 := by
    have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq u
    simpa [Work.Kernels.DeltaFun, Work.Kernels.E4Fun, Work.Kernels.E6Fun] using h
  -- the polynomial identity `Δ/q - 1 = N/(1728 q)`
  have hkey : DeltaFun u / q - 1
      = (3 * r4 - 2 * r6 + 3 * (240 * q + r4) ^ 2 + (240 * q + r4) ^ 3
          - (-504 * q + r6) ^ 2) / (1728 * q) := by
    rw [hDelta, hE4, hE6]
    field_simp
    ring
  have h1728 : ‖(1728 : ℂ)‖ = 1728 := by norm_num
  rw [hkey, norm_div, norm_mul, h1728]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 1728 * ‖q‖)]
  -- bounds for the pieces
  have hX : ‖(240 : ℂ) * q + r4‖ ≤ 241 * ‖q‖ := by
    have h1 : ‖(240 : ℂ) * q + r4‖ ≤ ‖(240 : ℂ) * q‖ + ‖r4‖ := norm_add_le _ _
    have h2 : ‖(240 : ℂ) * q‖ = 240 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h3 : 4000 * ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith
    linarith
  have hY : ‖(-504 : ℂ) * q + r6‖ ≤ 505 * ‖q‖ := by
    have h1 : ‖(-504 : ℂ) * q + r6‖ ≤ ‖(-504 : ℂ) * q‖ + ‖r6‖ := norm_add_le _ _
    have h2 : ‖(-504 : ℂ) * q‖ = 504 * ‖q‖ := by rw [norm_mul]; norm_num
    have h3 : 40000 * ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith
    linarith
  have hnum : ‖3 * r4 - 2 * r6 + 3 * (240 * q + r4) ^ 2 + (240 * q + r4) ^ 3
      - (-504 * q + r6) ^ 2‖ ≤ 540000 * ‖q‖ ^ 2 := by
    have h3r4 : ‖3 * r4‖ ≤ 12000 * ‖q‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have h2r6 : ‖2 * r6‖ ≤ 80000 * ‖q‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have h3X : ‖3 * (240 * q + r4) ^ 2‖ ≤ 180000 * ‖q‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      have := pow_le_pow_left₀ (norm_nonneg ((240 : ℂ) * q + r4)) hX 2
      nlinarith
    have hX3 : ‖(240 * q + r4) ^ 3‖ ≤ 200 * ‖q‖ ^ 2 := by
      rw [norm_pow]
      have := pow_le_pow_left₀ (norm_nonneg ((240 : ℂ) * q + r4)) hX 3
      nlinarith
    have hY2 : ‖(-504 * q + r6) ^ 2‖ ≤ 260000 * ‖q‖ ^ 2 := by
      rw [norm_pow]
      have := pow_le_pow_left₀ (norm_nonneg ((-504 : ℂ) * q + r6)) hY 2
      nlinarith
    have hsplit1 : ‖3 * r4 - 2 * r6 + 3 * (240 * q + r4) ^ 2 + (240 * q + r4) ^ 3
        - (-504 * q + r6) ^ 2‖
        ≤ ‖3 * r4 - 2 * r6 + 3 * (240 * q + r4) ^ 2 + (240 * q + r4) ^ 3‖
          + ‖(-504 * q + r6) ^ 2‖ := norm_sub_le _ _
    have hsplit2 : ‖3 * r4 - 2 * r6 + 3 * (240 * q + r4) ^ 2 + (240 * q + r4) ^ 3‖
        ≤ ‖3 * r4 - 2 * r6 + 3 * (240 * q + r4) ^ 2‖ + ‖(240 * q + r4) ^ 3‖ :=
      norm_add_le _ _
    have hsplit3 : ‖3 * r4 - 2 * r6 + 3 * (240 * q + r4) ^ 2‖
        ≤ ‖3 * r4 - 2 * r6‖ + ‖3 * (240 * q + r4) ^ 2‖ := norm_add_le _ _
    have hsplit4 : ‖3 * r4 - 2 * r6‖ ≤ ‖3 * r4‖ + ‖2 * r6‖ := norm_sub_le _ _
    linarith [hsplit1, hsplit2, hsplit3, hsplit4, h3r4, h2r6, h3X, hX3, hY2, sq_nonneg ‖q‖]
  have hgoal : 400 * ‖q‖ * (1728 * ‖q‖) = 691200 * ‖q‖ ^ 2 := by ring
  rw [hgoal]
  nlinarith [sq_nonneg ‖q‖, hnum]

/-- `‖E₄ u - 1‖ ≤ 241 ‖q u‖` for `Im u ≥ 2`. -/
lemma E4_sub_one_le (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖E4Fun u - 1‖ ≤ 241 * ‖qParamFun u‖ := by
  have h := E4Fun_second_order_im_ge_two u hu
  have hx0 : 0 ≤ ‖qParamFun u‖ := norm_nonneg _
  have hxle : ‖qParamFun u‖ ≤ 1 / 100000 := norm_qParamFun_le_1e5 u hu
  have hsplit : E4Fun u - 1
      = (E4Fun u - 1 - 240 * qParamFun u) + 240 * qParamFun u := by ring
  rw [hsplit]
  have h2 : ‖(240 : ℂ) * qParamFun u‖ = 240 * ‖qParamFun u‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E4Fun u - 1 - 240 * qParamFun u) + 240 * qParamFun u‖
      ≤ ‖E4Fun u - 1 - 240 * qParamFun u‖ + ‖(240 : ℂ) * qParamFun u‖ := norm_add_le _ _
    _ = ‖E4Fun u - 1 - 240 * qParamFun u‖ + 240 * ‖qParamFun u‖ := by rw [h2]
    _ ≤ 4000 * ‖qParamFun u‖ ^ 2 + 240 * ‖qParamFun u‖ := by linarith
    _ ≤ 241 * ‖qParamFun u‖ := by nlinarith [hx0, hxle]

/-- `‖E₆ u - 1‖ ≤ 505 ‖q u‖` for `Im u ≥ 2`. -/
lemma E6_sub_one_le (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖E6Fun u - 1‖ ≤ 505 * ‖qParamFun u‖ := by
  have h := E6Fun_second_order_im_ge_two u hu
  have hx0 : 0 ≤ ‖qParamFun u‖ := norm_nonneg _
  have hxle : ‖qParamFun u‖ ≤ 1 / 100000 := norm_qParamFun_le_1e5 u hu
  have hsplit : E6Fun u - 1
      = (E6Fun u - 1 + 504 * qParamFun u) - 504 * qParamFun u := by ring
  rw [hsplit]
  have h2 : ‖(504 : ℂ) * qParamFun u‖ = 504 * ‖qParamFun u‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E6Fun u - 1 + 504 * qParamFun u) - 504 * qParamFun u‖
      ≤ ‖E6Fun u - 1 + 504 * qParamFun u‖ + ‖(504 : ℂ) * qParamFun u‖ := norm_sub_le _ _
    _ = ‖E6Fun u - 1 + 504 * qParamFun u‖ + 504 * ‖qParamFun u‖ := by rw [h2]
    _ ≤ 40000 * ‖qParamFun u‖ ^ 2 + 504 * ‖qParamFun u‖ := by linarith
    _ ≤ 505 * ‖qParamFun u‖ := by nlinarith [hx0, hxle]

/-- `‖E₄ u - E₆ u‖ ≤ 745 ‖q u‖` for `Im u ≥ 2`. -/
lemma E4_sub_E6_le (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖E4Fun u - E6Fun u‖ ≤ 745 * ‖qParamFun u‖ := by
  have h4 := E4Fun_second_order_im_ge_two u hu
  have h6 := E6Fun_second_order_im_ge_two u hu
  have hx0 : 0 ≤ ‖qParamFun u‖ := norm_nonneg _
  have hxle : ‖qParamFun u‖ ≤ 1 / 100000 := norm_qParamFun_le_1e5 u hu
  have hsplit : E4Fun u - E6Fun u
      = 744 * qParamFun u + (E4Fun u - 1 - 240 * qParamFun u)
          - (E6Fun u - 1 + 504 * qParamFun u) := by ring
  rw [hsplit]
  have h2 : ‖(744 : ℂ) * qParamFun u‖ = 744 * ‖qParamFun u‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖744 * qParamFun u + (E4Fun u - 1 - 240 * qParamFun u)
        - (E6Fun u - 1 + 504 * qParamFun u)‖
      ≤ ‖744 * qParamFun u + (E4Fun u - 1 - 240 * qParamFun u)‖
        + ‖E6Fun u - 1 + 504 * qParamFun u‖ := norm_sub_le _ _
    _ ≤ (‖(744 : ℂ) * qParamFun u‖ + ‖E4Fun u - 1 - 240 * qParamFun u‖)
        + ‖E6Fun u - 1 + 504 * qParamFun u‖ := by
        have := norm_add_le ((744 : ℂ) * qParamFun u) (E4Fun u - 1 - 240 * qParamFun u)
        linarith
    _ = (744 * ‖qParamFun u‖ + ‖E4Fun u - 1 - 240 * qParamFun u‖)
        + ‖E6Fun u - 1 + 504 * qParamFun u‖ := by rw [h2]
    _ ≤ (744 * ‖qParamFun u‖ + 4000 * ‖qParamFun u‖ ^ 2) + 40000 * ‖qParamFun u‖ ^ 2 := by
        linarith
    _ ≤ 745 * ‖qParamFun u‖ := by nlinarith [hx0, hxle]

/-- `1 - 400‖q u‖ ≤ ‖Δ u / q u‖` for `Im u ≥ 2`. -/
lemma one_sub_le_norm_Delta_div_q (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    1 - 400 * ‖qParamFun u‖ ≤ ‖DeltaFun u / qParamFun u‖ := by
  have h := abs_norm_sub_norm_le (1 : ℂ) (DeltaFun u / qParamFun u)
  rw [norm_one, abs_le] at h
  have h2 := DeltaFun_div_q_sub_one_le u hu
  have h3 := h.2
  rw [norm_sub_rev] at h3
  linarith

/-- `‖E₄ u‖ ≤ 1 + 241 ‖q u‖` for `Im u ≥ 2`. -/
lemma norm_E4Fun_le (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖E4Fun u‖ ≤ 1 + 241 * ‖qParamFun u‖ := by
  have hE4 := E4_sub_one_le u hu
  have h1 : E4Fun u = (E4Fun u - 1) + 1 := by ring
  rw [h1]
  calc ‖(E4Fun u - 1) + 1‖ ≤ ‖E4Fun u - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖E4Fun u - 1‖ + 1 := by rw [norm_one]
    _ ≤ 241 * ‖qParamFun u‖ + 1 := by linarith
    _ = 1 + 241 * ‖qParamFun u‖ := by ring

/-- `Ψ u = 1 + O(q)` on `Im ≥ 2`. -/
lemma Psi_sub_one_le_quarter (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖Psi u - 1‖ ≤ 1 / 4 := by
  have hxle : ‖qParamFun u‖ ≤ 1 / 100000 := norm_qParamFun_le_1e5 u hu
  have hx0 : 0 ≤ ‖qParamFun u‖ := norm_nonneg _
  have hLam : ‖DeltaFun u / qParamFun u - 1‖ ≤ 400 * ‖qParamFun u‖ :=
    DeltaFun_div_q_sub_one_le u hu
  have hLam_lb : (1 : ℝ) / 2 ≤ ‖DeltaFun u / qParamFun u‖ := by
    have h := one_sub_le_norm_Delta_div_q u hu
    nlinarith
  have hE4 := E4_sub_one_le u hu
  have hE4ub := norm_E4Fun_le u hu
  have hE4cube : ‖E4Fun u ^ 3 - 1‖ ≤ 730 * ‖qParamFun u‖ := by
    have hfac : E4Fun u ^ 3 - 1 = (E4Fun u - 1) * (E4Fun u ^ 2 + E4Fun u + 1) := by ring
    rw [hfac, norm_mul]
    have hb2 : ‖E4Fun u ^ 2 + E4Fun u + 1‖ ≤ 3.01 := by
      have h1 : ‖E4Fun u ^ 2‖ ≤ (1 + 241 * ‖qParamFun u‖) ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4ub 2
      have h2 : ‖E4Fun u ^ 2 + E4Fun u + 1‖ ≤ ‖E4Fun u ^ 2‖ + ‖E4Fun u‖ + 1 := by
        have ha := norm_add_le (E4Fun u ^ 2 + E4Fun u) 1
        have hb := norm_add_le (E4Fun u ^ 2) (E4Fun u)
        rw [norm_one] at ha
        linarith
      nlinarith [hx0, hxle]
    calc ‖E4Fun u - 1‖ * ‖E4Fun u ^ 2 + E4Fun u + 1‖
        ≤ (241 * ‖qParamFun u‖) * 3.01 :=
          mul_le_mul hE4 hb2 (norm_nonneg _) (by positivity)
      _ ≤ 730 * ‖qParamFun u‖ := by nlinarith [hx0]
  have hnum : ‖E4Fun u ^ 3 - DeltaFun u / qParamFun u‖ ≤ 1200 * ‖qParamFun u‖ := by
    have hsplit : E4Fun u ^ 3 - DeltaFun u / qParamFun u
        = (E4Fun u ^ 3 - 1) + (1 - DeltaFun u / qParamFun u) := by ring
    rw [hsplit]
    have h1 : ‖1 - DeltaFun u / qParamFun u‖ ≤ 400 * ‖qParamFun u‖ := by
      rw [norm_sub_rev]; exact hLam
    calc ‖(E4Fun u ^ 3 - 1) + (1 - DeltaFun u / qParamFun u)‖
        ≤ ‖E4Fun u ^ 3 - 1‖ + ‖1 - DeltaFun u / qParamFun u‖ := norm_add_le _ _
      _ ≤ 730 * ‖qParamFun u‖ + 400 * ‖qParamFun u‖ := by linarith
      _ ≤ 1200 * ‖qParamFun u‖ := by linarith
  have hkey : Psi u - 1 = (E4Fun u ^ 3 - DeltaFun u / qParamFun u)
      / (DeltaFun u / qParamFun u) := by
    rw [Psi_eq_E4_cube_div_Lambda u]
    have hne : DeltaFun u / qParamFun u ≠ 0 := by
      refine div_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero u) ?_
      exact qParamFun_ne_zero u
    have hD : DeltaFun u ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero u
    field_simp
  rw [hkey, norm_div]
  calc ‖E4Fun u ^ 3 - DeltaFun u / qParamFun u‖ / ‖DeltaFun u / qParamFun u‖
      ≤ (1200 * ‖qParamFun u‖) / (1 / 2) :=
        div_le_div₀ (by positivity) hnum (by norm_num) hLam_lb
    _ = 2400 * ‖qParamFun u‖ := by ring
    _ ≤ 1 / 4 := by nlinarith [hxle]

/-- `‖D Ψ u‖ ≤ 800 ‖q u‖` on `Im ≥ 2`. -/
lemma norm_normalizedDeriv_Psi_le (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖Derivative.normalizedDerivOfComplex Psi u‖ ≤ 800 * ‖qParamFun u‖ := by
  rw [normalizedDeriv_Psi]
  have hxle : ‖qParamFun u‖ ≤ 1 / 100000 := norm_qParamFun_le_1e5 u hu
  have hx0 : 0 ≤ ‖qParamFun u‖ := norm_nonneg _
  have hE4 := E4_sub_one_le u hu
  have hE4E6 := E4_sub_E6_le u hu
  have hE4ub := norm_E4Fun_le u hu
  have hΛpos : 0 < 1 - 400 * ‖qParamFun u‖ := by nlinarith
  have hqD : ‖qParamFun u / DeltaFun u‖ ≤ 1 / (1 - 400 * ‖qParamFun u‖) := by
    have hLam_lb := one_sub_le_norm_Delta_div_q u hu
    have heq : qParamFun u / DeltaFun u = (DeltaFun u / qParamFun u)⁻¹ := (inv_div _ _).symm
    rw [heq, norm_inv]
    have h := one_div_le_one_div_of_le hΛpos hLam_lb
    simpa [one_div] using h
  rw [norm_mul, norm_mul, norm_pow]
  have h1 : ‖E4Fun u‖ ^ 2 ≤ (1 + 241 * ‖qParamFun u‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hE4ub 2
  have hbound : ‖E4Fun u‖ ^ 2 * ‖qParamFun u / DeltaFun u‖ * ‖E4Fun u - E6Fun u‖
      ≤ (1 + 241 * ‖qParamFun u‖) ^ 2 * (1 / (1 - 400 * ‖qParamFun u‖))
        * (745 * ‖qParamFun u‖) := by
    have h2 : ‖E4Fun u‖ ^ 2 * ‖qParamFun u / DeltaFun u‖
        ≤ (1 + 241 * ‖qParamFun u‖) ^ 2 * (1 / (1 - 400 * ‖qParamFun u‖)) :=
      mul_le_mul h1 hqD (norm_nonneg _) (by positivity)
    exact mul_le_mul h2 hE4E6 (norm_nonneg _) (by positivity)
  refine le_trans hbound ?_
  have hfac : (1 + 241 * ‖qParamFun u‖) ^ 2 * (1 / (1 - 400 * ‖qParamFun u‖)) ≤ 1.012 := by
    have hinv : 1 / (1 - 400 * ‖qParamFun u‖) ≤ 1.005 := by
      rw [div_le_iff₀ hΛpos]
      nlinarith
    have hsq : (1 + 241 * ‖qParamFun u‖) ^ 2 ≤ 1.006 := by nlinarith
    nlinarith [norm_nonneg (qParamFun u)]
  nlinarith [norm_nonneg (qParamFun u)]

end Work.Asymptotics.CuspDecay
