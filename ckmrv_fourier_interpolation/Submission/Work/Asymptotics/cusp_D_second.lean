import Mathlib
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Asymptotics.cusp_U_second

namespace Work.Asymptotics

open UpperHalfPlane

/-- The third-order cusp expansion of `D = U² - V²`, with `E = Ept z = e^{πiz}`
(`‖E‖ = e^{-π Im z}`):

  `U(z)² - V(z)² = 1 + 16 E(z) - 144 E(z)² + O(‖E(z)‖³)`.

Indeed the explicit theta series give `θ₀₀⁴ = 1 + 8E + 24E² + O(E³)` (so
`U² = θ₀₀⁸ = 1 + 16E + 112E² + O(E³)`) and `V = θ₁₀⁴ = 16E + O(E³)` (so
`V² = 256E² + O(E³)`); subtracting, `112 - 256 = -144`. -/
theorem cusp_D_second : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
    ‖(Work.Kernels.UFun z) ^ 2 - (Work.Kernels.VFun z) ^ 2 -
        (1 + 16 * Work.Residues.Ept z - 144 * (Work.Residues.Ept z) ^ 2)‖ ≤
      C * ‖Work.Residues.Ept z‖ ^ 3 := by
  obtain ⟨C₁, hC₁, hU⟩ := cusp_U_second
  obtain ⟨C₂, hC₂, hV⟩ := Work.Residues.VFun_expansion
  refine ⟨960 + 66 * C₁ + C₁^2 + 32 * C₂ + C₂^2, by positivity, ?_⟩
  intro z hz
  have hC₁0 : 0 ≤ C₁ := le_of_lt hC₁
  have hC₂0 : 0 ≤ C₂ := le_of_lt hC₂
  have hUz := hU z hz
  have hVz := hV z hz
  set e : ℂ := Work.Residues.Ept z with he
  set A : ℂ := Work.Kernels.UFun z - (1 + 8 * e + 24 * e^2) with hAdef
  set B : ℂ := Work.Kernels.VFun z - 16 * e with hBdef
  have hr0 : 0 ≤ ‖e‖ := norm_nonneg _
  have hr1 : ‖e‖ ≤ 1 := by rw [he]; exact le_of_lt (Work.Residues.norm_Ept_lt_one z)
  have hpow43 : ‖e‖^4 ≤ ‖e‖^3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hpow63 : ‖e‖^6 ≤ ‖e‖^3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hu0n : ‖(1:ℂ) + 8*e + 24*e^2‖ ≤ 33 := by
    have h8 : ‖(8:ℂ)*e‖ = 8*‖e‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h24 : ‖(24:ℂ)*e^2‖ = 24*‖e‖^2 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have a := norm_add_le ((1:ℂ) + 8*e) (24*e^2)
    have b := norm_add_le (1:ℂ) (8*e)
    rw [norm_one] at b
    rw [h24] at a
    rw [h8] at b
    nlinarith [a, b, hr0, hr1]
  have hUdef : Work.Kernels.UFun z = (1 + 8 * e + 24 * e^2) + A := by rw [hAdef]; ring
  have hVdef : Work.Kernels.VFun z = 16 * e + B := by rw [hBdef]; ring
  have hkey : Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - (1 + 16 * e - 144 * e^2)
      = (384 * e^3 + 576 * e^4) + 2 * (1 + 8 * e + 24 * e^2) * A + A^2 - 32 * e * B - B^2 := by
    rw [hUdef, hVdef]; ring
  have t0 : ‖(384:ℂ) * e^3 + 576 * e^4‖ ≤ 960 * ‖e‖^3 := by
    have h3 : ‖(384:ℂ) * e^3‖ = 384 * ‖e‖^3 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h4 : ‖(576:ℂ) * e^4‖ = 576 * ‖e‖^4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have a := norm_add_le ((384:ℂ) * e^3) ((576:ℂ) * e^4)
    rw [h3, h4] at a
    nlinarith [a, hpow43]
  have t1 : ‖(2:ℂ) * (1 + 8 * e + 24 * e^2) * A‖ ≤ 66 * C₁ * ‖e‖^3 := by
    have h2 : ‖(2:ℂ) * (1 + 8 * e + 24 * e^2) * A‖ = 2 * ‖(1:ℂ) + 8*e + 24*e^2‖ * ‖A‖ := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
    rw [h2]
    calc 2 * ‖(1:ℂ) + 8*e + 24*e^2‖ * ‖A‖ ≤ 2 * 33 * (C₁ * ‖e‖^3) := by
          apply mul_le_mul
          · nlinarith [hu0n]
          · exact hUz
          · exact norm_nonneg A
          · norm_num
      _ = 66 * C₁ * ‖e‖^3 := by ring
  have t2 : ‖A^2‖ ≤ C₁^2 * ‖e‖^3 := by
    rw [norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg A) hUz 2
    calc ‖A‖^2 ≤ (C₁ * ‖e‖^3)^2 := h
      _ = C₁^2 * ‖e‖^6 := by ring
      _ ≤ C₁^2 * ‖e‖^3 := mul_le_mul_of_nonneg_left hpow63 (sq_nonneg C₁)
  have t3 : ‖(32:ℂ) * e * B‖ ≤ 32 * C₂ * ‖e‖^3 := by
    have h2 : ‖(32:ℂ) * e * B‖ = 32 * ‖e‖ * ‖B‖ := by rw [norm_mul, norm_mul, Complex.norm_ofNat]
    rw [h2]
    calc 32 * ‖e‖ * ‖B‖ ≤ 32 * ‖e‖ * (C₂ * ‖e‖^3) :=
          mul_le_mul_of_nonneg_left hVz (by nlinarith [hr0])
      _ = 32 * C₂ * ‖e‖^4 := by ring
      _ ≤ 32 * C₂ * ‖e‖^3 := mul_le_mul_of_nonneg_left hpow43 (by nlinarith [hC₂0])
  have t4 : ‖B^2‖ ≤ C₂^2 * ‖e‖^3 := by
    rw [norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg B) hVz 2
    calc ‖B‖^2 ≤ (C₂ * ‖e‖^3)^2 := h
      _ = C₂^2 * ‖e‖^6 := by ring
      _ ≤ C₂^2 * ‖e‖^3 := mul_le_mul_of_nonneg_left hpow63 (sq_nonneg C₂)
  have hP : ‖(384:ℂ) * e^3 + 576 * e^4 + (2:ℂ) * (1 + 8 * e + 24 * e^2) * A + A^2
      - (32:ℂ) * e * B - B^2‖ ≤ (960 + 66 * C₁ + C₁^2 + 32 * C₂ + C₂^2) * ‖e‖^3 := by
    have e1 : ‖(384:ℂ) * e^3 + 576 * e^4 + (2:ℂ) * (1 + 8 * e + 24 * e^2) * A + A^2
        - (32:ℂ) * e * B - B^2‖
        ≤ ‖(384:ℂ) * e^3 + 576 * e^4 + (2:ℂ) * (1 + 8 * e + 24 * e^2) * A + A^2
            - (32:ℂ) * e * B‖ + ‖B^2‖ := norm_sub_le _ _
    have e2 : ‖(384:ℂ) * e^3 + 576 * e^4 + (2:ℂ) * (1 + 8 * e + 24 * e^2) * A + A^2
        - (32:ℂ) * e * B‖
        ≤ ‖(384:ℂ) * e^3 + 576 * e^4 + (2:ℂ) * (1 + 8 * e + 24 * e^2) * A + A^2‖
          + ‖(32:ℂ) * e * B‖ := norm_sub_le _ _
    have hs1 : ‖(384:ℂ) * e^3 + 576 * e^4 + (2:ℂ) * (1 + 8 * e + 24 * e^2) * A + A^2‖
        ≤ ‖(384:ℂ) * e^3 + 576 * e^4‖ + ‖(2:ℂ) * (1 + 8 * e + 24 * e^2) * A‖ + ‖A^2‖ := by
      have a := norm_add_le ((384:ℂ) * e^3 + 576 * e^4 + (2:ℂ) * (1 + 8 * e + 24 * e^2) * A) (A^2)
      have b := norm_add_le ((384:ℂ) * e^3 + 576 * e^4) ((2:ℂ) * (1 + 8 * e + 24 * e^2) * A)
      linarith
    nlinarith [e1, e2, hs1, t0, t1, t2, t3, t4, pow_nonneg hr0 3]
  rw [hkey]
  exact hP

end Work.Asymptotics
