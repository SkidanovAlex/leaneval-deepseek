import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.E4FunSecondOrder

namespace Work.Asymptotics

open UpperHalfPlane

/-- Elementary second-order expansion of the *cube* of a function from the second-order
expansion of the function itself: if `z = 1 + 240 q + O(‖q‖²)` with `‖q‖ ≤ 1`, then
`z³ = 1 + 720 q + O(‖q‖²)`.

Writing `r = z - 1 - 240 q` (so `‖r‖ ≤ A ‖q‖²`) and `s = z - 1 = r + 240 q`
(so `‖s‖ ≤ (240 + A) ‖q‖`), the identity
`z³ - 1 - 720 q = 3 r + 3 s² + s³` together with `‖q‖² ≤ ‖q‖` gives the claim. -/
private lemma cube_second_order {z q : ℂ} {A : ℝ} (hA : 0 ≤ A) (hq : ‖q‖ ≤ 1)
    (hz : ‖z - 1 - 240 * q‖ ≤ A * ‖q‖ ^ 2) :
    ‖z ^ 3 - 1 - 720 * q‖ ≤ (3 * A + 3 * (240 + A) ^ 2 + (240 + A) ^ 3) * ‖q‖ ^ 2 := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hs : ‖z - 1‖ ≤ (240 + A) * ‖q‖ := by
    have hsplit : z - 1 = (z - 1 - 240 * q) + 240 * q := by ring
    rw [hsplit]
    have h1 : ‖(z - 1 - 240 * q) + 240 * q‖ ≤ ‖z - 1 - 240 * q‖ + ‖240 * q‖ :=
      norm_add_le _ _
    have h2 : ‖(240 : ℂ) * q‖ = 240 * ‖q‖ := by rw [norm_mul]; norm_num
    have h4 : A * ‖q‖ ^ 2 + 240 * ‖q‖ ≤ (240 + A) * ‖q‖ := by
      have hAq : A * ‖q‖ ^ 2 ≤ A * ‖q‖ := by
        calc A * ‖q‖ ^ 2 = A * (‖q‖ * ‖q‖) := by ring
          _ ≤ A * (1 * ‖q‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hq0) hA
          _ = A * ‖q‖ := by ring
      linarith
    calc ‖(z - 1 - 240 * q) + 240 * q‖ ≤ ‖z - 1 - 240 * q‖ + ‖240 * q‖ := h1
      _ = ‖z - 1 - 240 * q‖ + 240 * ‖q‖ := by rw [h2]
      _ ≤ (240 + A) * ‖q‖ := by linarith
  have hid : z ^ 3 - 1 - 720 * q
      = 3 * (z - 1 - 240 * q) + (3 * (z - 1) ^ 2 + (z - 1) ^ 3) := by ring
  have e1 : ‖3 * (z - 1 - 240 * q)‖ = 3 * ‖z - 1 - 240 * q‖ := by rw [norm_mul]; norm_num
  have e2 : ‖3 * (z - 1) ^ 2‖ = 3 * ‖z - 1‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
  have e3 : ‖(z - 1) ^ 3‖ = ‖z - 1‖ ^ 3 := norm_pow _ _
  rw [hid]
  have hn1 : ‖3 * (z - 1 - 240 * q) + (3 * (z - 1) ^ 2 + (z - 1) ^ 3)‖
      ≤ ‖3 * (z - 1 - 240 * q)‖ + ‖3 * (z - 1) ^ 2 + (z - 1) ^ 3‖ := norm_add_le _ _
  have hn2 : ‖3 * (z - 1) ^ 2 + (z - 1) ^ 3‖ ≤ ‖3 * (z - 1) ^ 2‖ + ‖(z - 1) ^ 3‖ :=
    norm_add_le _ _
  have hmain : ‖3 * (z - 1 - 240 * q) + (3 * (z - 1) ^ 2 + (z - 1) ^ 3)‖
      ≤ 3 * ‖z - 1 - 240 * q‖ + (3 * ‖z - 1‖ ^ 2 + ‖z - 1‖ ^ 3) := by
    simp only [e1, e2, e3] at hn1 hn2
    linarith
  have hsq : 3 * ‖z - 1‖ ^ 2 ≤ 3 * ((240 + A) * ‖q‖) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hs 2
    linarith
  have hcu : ‖z - 1‖ ^ 3 ≤ ((240 + A) * ‖q‖) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hs 3
  have haux : ‖3 * (z - 1 - 240 * q) + (3 * (z - 1) ^ 2 + (z - 1) ^ 3)‖
      ≤ 3 * (A * ‖q‖ ^ 2) + 3 * ((240 + A) * ‖q‖) ^ 2 + ((240 + A) * ‖q‖) ^ 3 := by
    have hb : 3 * ‖z - 1 - 240 * q‖ ≤ 3 * (A * ‖q‖ ^ 2) := by linarith
    linarith [hmain, hb, hsq, hcu]
  refine le_trans haux ?_
  have hq2 : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith
  have hq3 : ‖q‖ ^ 3 ≤ ‖q‖ ^ 2 := by
    have : ‖q‖ ^ 3 = ‖q‖ ^ 2 * ‖q‖ := by ring
    rw [this]; nlinarith
  have h240 : (0 : ℝ) ≤ 240 + A := by linarith
  nlinarith [hq2, hq3, hq0, mul_nonneg (pow_nonneg h240 3) (sub_nonneg.mpr hq3),
    mul_nonneg (mul_nonneg (pow_nonneg h240 2) (by norm_num : (0 : ℝ) ≤ 3))
      (sub_nonneg.mpr hq2)]

/-- The norm of the `q`-parameter in the region `Im τ ≥ 1` is at most `1`. -/
private lemma norm_qParamFun_le_one (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  have hqnorm : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Work.Kernels.qParamFun, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      UpperHalfPlane.coe_im]
  rw [hqnorm, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])

/-- Second-order cusp expansion of `E₄³`: on `Im τ ≥ 1`,
`E₄(τ)³ = 1 + 720 q + O(‖q‖²)`, obtained by cubing the second-order expansion
`E₄ = 1 + 240 q + O(‖q‖²)` of `Work.Residues.E4FunSecondOrder`. -/
theorem E4cube_cusp_second : ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖Work.Kernels.E4Fun τ ^ 3 - 1 - 720 * Work.Kernels.qParamFun τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := Work.Residues.E4FunSecondOrder
  refine ⟨3 * A + 3 * (240 + A) ^ 2 + (240 + A) ^ 3 + 1, by positivity, fun τ hτ => ?_⟩
  have hmain := cube_second_order hA0.le (norm_qParamFun_le_one τ hτ) (hA τ hτ)
  have hC : 3 * A + 3 * (240 + A) ^ 2 + (240 + A) ^ 3
      ≤ 3 * A + 3 * (240 + A) ^ 2 + (240 + A) ^ 3 + 1 := by linarith
  calc ‖Work.Kernels.E4Fun τ ^ 3 - 1 - 720 * Work.Kernels.qParamFun τ‖
      ≤ (3 * A + 3 * (240 + A) ^ 2 + (240 + A) ^ 3) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := hmain
    _ ≤ (3 * A + 3 * (240 + A) ^ 2 + (240 + A) ^ 3 + 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hC (sq_nonneg _)

end Work.Asymptotics
