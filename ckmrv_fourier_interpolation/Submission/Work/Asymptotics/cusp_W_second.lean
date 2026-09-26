import Mathlib
import Submission.Work.Residues.ThetaExpansion

namespace Work.Asymptotics

open UpperHalfPlane

/-- The third-order cusp expansion of `W = θ₀₁⁴`: with `E = Ept z = e^{πiz}` (`‖E‖ = e^{-π Im z}`),

  `W(z) = 1 - 8 E(z) + 24 E(z)² + O(‖E(z)‖³)`.

This mirrors `Work.Asymptotics.cusp_U_second`: the expansion `θ₀₀ = 1 + 2E + d`, `‖d‖ ≤ C‖E‖⁴`
of `Work.Residues.theta00Fun_expansion`, transported by `τ ↦ τ + 1` (where `θ₀₀ ↦ θ₀₁` and
`E ↦ -E`), gives `θ₀₁ = 1 - 2E + d` with the same bound for `d`; raising to the fourth power,
the `d`-linear terms contribute `4d - 24Ed + O(‖E‖³)` and the remaining terms `4x³ + x⁴`,
`x = -2E + d`, are of order `‖E‖³`. -/
theorem cusp_W_second : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
    ‖Work.Kernels.WFun z - (1 - 8 * Work.Residues.Ept z + 24 * (Work.Residues.Ept z) ^ 2)‖ ≤
      C * ‖Work.Residues.Ept z‖ ^ 3 := by
  obtain ⟨C₀, hC₀, h₀⟩ := Work.Residues.theta00Fun_expansion
  refine ⟨4 * C₀ + 24 * C₀ + 6 * C₀ ^ 2 + 4 * (2 + C₀) ^ 3 + (2 + C₀) ^ 4, by positivity, ?_⟩
  intro z hz
  set e : ℂ := Work.Residues.Ept z with he
  set d : ℂ := Work.Kernels.theta01Fun z - 1 + 2 * e with hd
  set x : ℂ := Work.Kernels.theta01Fun z - 1 with hxx
  have hxd : x = -(2 * e) + d := by rw [hxx, hd]; ring
  have hxe : (1 : ℂ) + x = Work.Kernels.theta01Fun z := by rw [hxx]; ring
  have he0 : 0 ≤ ‖e‖ := norm_nonneg _
  have he1 : ‖e‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one z)
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_of_lt hC₀
  -- `θ₀₁ = 1 - 2E + d` with `‖d‖ ≤ C₀‖E‖⁴`, obtained from the expansion of `θ₀₀` at `T • z`
  have hdb : ‖d‖ ≤ C₀ * ‖e‖ ^ 4 := by
    have hz' : (1 : ℝ) ≤ (ModularGroup.T • z).im := by
      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_im]; exact hz
    have h := h₀ (ModularGroup.T • z) hz'
    rw [Work.Kernels.theta00Fun_T z, Work.Residues.Ept_T z, norm_neg] at h
    rw [hd, he]
    convert h using 2
    ring
  have hxb : ‖x‖ ≤ (2 + C₀) * ‖e‖ := by
    have h1 : ‖x‖ ≤ ‖-(2 * e)‖ + ‖d‖ := by rw [hxd]; exact norm_add_le _ _
    have h2 : ‖-(2 * e)‖ = 2 * ‖e‖ := by
      rw [norm_neg, norm_mul, Complex.norm_ofNat]
    have h3 : C₀ * ‖e‖ ^ 4 ≤ C₀ * ‖e‖ := mul_le_mul_of_nonneg_left
      (by simpa using pow_le_pow_of_le_one he0 he1 (by norm_num : 1 ≤ 4)) hC₀0
    calc ‖x‖ ≤ 2 * ‖e‖ + C₀ * ‖e‖ ^ 4 := by rw [h2] at h1; linarith
      _ ≤ 2 * ‖e‖ + C₀ * ‖e‖ := by linarith
      _ = (2 + C₀) * ‖e‖ := by ring
  have h2C₀ : (0 : ℝ) ≤ 2 + C₀ := by linarith
  -- the five pieces, each of order `‖e‖³`
  have t1 : ‖4 * d‖ ≤ 4 * C₀ * ‖e‖ ^ 3 := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 4 * ‖d‖ ≤ 4 * (C₀ * ‖e‖ ^ 3) := mul_le_mul_of_nonneg_left
          (le_trans hdb (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one he0 he1 (by norm_num : 3 ≤ 4)) hC₀0)) (by norm_num)
      _ = 4 * C₀ * ‖e‖ ^ 3 := by ring
  have t2 : ‖24 * e * d‖ ≤ 24 * C₀ * ‖e‖ ^ 3 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc 24 * ‖e‖ * ‖d‖ ≤ 24 * ‖e‖ * (C₀ * ‖e‖ ^ 4) :=
          mul_le_mul_of_nonneg_left hdb (by positivity)
      _ = 24 * C₀ * ‖e‖ ^ 5 := by ring
      _ ≤ 24 * C₀ * ‖e‖ ^ 3 := mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one he0 he1 (by norm_num : 3 ≤ 5))
            (mul_nonneg (by norm_num) hC₀0)
  have t3 : ‖6 * d ^ 2‖ ≤ 6 * C₀ ^ 2 * ‖e‖ ^ 3 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg d) hdb 2
    calc 6 * ‖d‖ ^ 2 ≤ 6 * (C₀ * ‖e‖ ^ 4) ^ 2 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 6 * C₀ ^ 2 * ‖e‖ ^ 8 := by ring
      _ ≤ 6 * C₀ ^ 2 * ‖e‖ ^ 3 := mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one he0 he1 (by norm_num : 3 ≤ 8))
            (by positivity)
  have t4 : ‖4 * x ^ 3‖ ≤ 4 * (2 + C₀) ^ 3 * ‖e‖ ^ 3 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg x) hxb 3
    calc 4 * ‖x‖ ^ 3 ≤ 4 * ((2 + C₀) * ‖e‖) ^ 3 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 4 * (2 + C₀) ^ 3 * ‖e‖ ^ 3 := by ring
  have t5 : ‖x ^ 4‖ ≤ (2 + C₀) ^ 4 * ‖e‖ ^ 3 := by
    rw [norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg x) hxb 4
    calc ‖x‖ ^ 4 ≤ ((2 + C₀) * ‖e‖) ^ 4 := h
      _ = (2 + C₀) ^ 4 * ‖e‖ ^ 4 := by ring
      _ ≤ (2 + C₀) ^ 4 * ‖e‖ ^ 3 := mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one he0 he1 (by norm_num : 3 ≤ 4)) (pow_nonneg h2C₀ 4)
  have hkey : (1 + x) ^ 4 - (1 - 8 * e + 24 * e ^ 2)
      = 4 * d - 24 * e * d + 6 * d ^ 2 + 4 * x ^ 3 + x ^ 4 := by
    rw [hxd]; ring
  have hW : Work.Kernels.WFun z = (1 + x) ^ 4 := by
    rw [show Work.Kernels.WFun z = Work.Kernels.theta01Fun z ^ 4 from rfl, ← hxe]
  have hfin : ‖4 * d - 24 * e * d + 6 * d ^ 2 + 4 * x ^ 3 + x ^ 4‖
      ≤ (4 * C₀ + 24 * C₀ + 6 * C₀ ^ 2 + 4 * (2 + C₀) ^ 3 + (2 + C₀) ^ 4) * ‖e‖ ^ 3 := by
    have a := norm_add_le (4 * d - 24 * e * d + 6 * d ^ 2 + 4 * x ^ 3) (x ^ 4)
    have b := norm_add_le (4 * d - 24 * e * d + 6 * d ^ 2) (4 * x ^ 3)
    have c := norm_add_le (4 * d - 24 * e * d) (6 * d ^ 2)
    have dd : ‖4 * d - 24 * e * d‖ ≤ ‖4 * d‖ + ‖24 * e * d‖ := norm_sub_le _ _
    have h4r : (0 : ℝ) ≤ ‖e‖ ^ 3 := pow_nonneg he0 3
    nlinarith [a, b, c, dd, t1, t2, t3, t4, t5, h4r]
  rw [hW, hkey]
  exact hfin

end Work.Asymptotics
