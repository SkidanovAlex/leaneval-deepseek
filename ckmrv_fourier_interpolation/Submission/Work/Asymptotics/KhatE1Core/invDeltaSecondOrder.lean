/-
# The second-order cusp expansion of `1/Δ(z)`

`Work.Asymptotics.cusp_invDelta` gives the *first*-order expansion
`‖1/Δ(z) - (Ept z)⁻² - 24‖ ≤ C ‖Ept z‖²`.  This module refines it by one term:

  `1/Δ(z) = q(z)⁻¹ + 24 + 324 q(z) + O(q(z)²)`,  `q(z) = qParamFun z = (Ept z)²`,

i.e. `‖1/Δ(z) - (Ept z)⁻² - 24 - 324 qParamFun z‖ ≤ C ‖Ept z‖⁴` for `Im z ≥ 1`.  The
coefficient `324 = 576 - 252` is the second-order term of the reciprocal of the `q`-expansion
`Δ = q - 24q² + 252q³ + O(q⁴)` (`Work.Asymptotics.DeltaFun_fourth_order`); it is forced by
`j = E₄³/Δ = q⁻¹ + 744 + 196884 q + …` (`720 + 24 = 744`, `179280 + 720·24 + 324 = 196884`).

This is one of the refined `z`-atom deviation expansions needed to read off the `E(z)^k`-
coefficients of the `d = 24` bracket from its reference + deviation form.
-/
import Mathlib
import Submission.Work.Asymptotics.funnel_tauAtom_second_order
import Submission.Work.Asymptotics.Tile.DeltaFun_lower_region
import Submission.Work.Residues.KMinusCuspDefs

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

/-- `1/Δ(z) = q⁻¹ + 24 + 324 q + O(q²)`, i.e. the second-order refinement of
`Work.Asymptotics.cusp_invDelta`. -/
theorem invDeltaSecondOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖(Work.Kernels.DeltaFun z)⁻¹ - ((Work.Residues.Ept z)⁻¹ ^ 2 + 24
          + 324 * Work.Kernels.qParamFun z)‖
        ≤ C * ‖Work.Residues.Ept z‖ ^ 4 := by
  obtain ⟨C₄, hC₄, hΔ⟩ := Work.Asymptotics.DeltaFun_fourth_order
  obtain ⟨c, hc, hlow⟩ := Work.Asymptotics.Tile.DeltaFun_lower_region
  refine ⟨(1728 + 81648 + C₄ * 349) / c + 1, by positivity, fun z hz => ?_⟩
  set q : ℂ := Work.Kernels.qParamFun z with hq
  set E : ℂ := Work.Residues.Ept z with hE
  have hqE : q = E ^ 2 := by
    rw [hq, hE, Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
    congr 1; ring
  have hEne : E ≠ 0 := by rw [hE]; exact Work.Residues.Ept_ne_zero z
  have hqne : q ≠ 0 := by rw [hqE]; exact pow_ne_zero 2 hEne
  have hDne : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hqnorm : ‖q‖ = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [hqE, norm_pow, Work.Residues.norm_Ept]
    rw [show Real.exp (-(Real.pi * z.im)) ^ 2 = Real.exp (-(2 * Real.pi * z.im)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  have hEnorm : ‖E‖ ^ 2 = ‖q‖ := by rw [hqE, norm_pow]
  have hq1 : ‖q‖ ≤ 1 := by
    rw [hqnorm, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
  have hq0 : (0 : ℝ) < ‖q‖ := by rw [hqnorm]; exact Real.exp_pos _
  -- the numerator identity
  have hR : ‖Work.Kernels.DeltaFun z - (q - 24 * q ^ 2 + 252 * q ^ 3)‖ ≤ C₄ * ‖q‖ ^ 4 := by
    rw [hq]; exact hΔ z hz
  have hnum : ‖1 - Work.Kernels.DeltaFun z * (q⁻¹ + 24 + 324 * q)‖
      ≤ (1728 + 81648 + C₄ * 349) * ‖q‖ ^ 3 := by
    have hsplit : 1 - Work.Kernels.DeltaFun z * (q⁻¹ + 24 + 324 * q)
        = 1728 * q ^ 3 - 81648 * q ^ 4
          - (Work.Kernels.DeltaFun z - (q - 24 * q ^ 2 + 252 * q ^ 3))
              * (q⁻¹ + 24 + 324 * q) := by
      have h1 : Work.Kernels.DeltaFun z * (q⁻¹ + 24 + 324 * q)
          = (Work.Kernels.DeltaFun z - (q - 24 * q ^ 2 + 252 * q ^ 3))
              * (q⁻¹ + 24 + 324 * q) + (q - 24 * q ^ 2 + 252 * q ^ 3) * (q⁻¹ + 24 + 324 * q) := by
        ring
      have h2 : (q - 24 * q ^ 2 + 252 * q ^ 3) * (q⁻¹ + 24 + 324 * q)
          = 1 - 1728 * q ^ 3 + 81648 * q ^ 4 := by
        field_simp
        ring
      rw [h1, h2]; ring
    rw [hsplit]
    have h3 : ‖(Work.Kernels.DeltaFun z - (q - 24 * q ^ 2 + 252 * q ^ 3)) * (q⁻¹ + 24 + 324 * q)‖
        ≤ C₄ * 349 * ‖q‖ ^ 3 := by
      rw [norm_mul]
      have h4 : ‖q⁻¹ + 24 + 324 * q‖ ≤ ‖q‖⁻¹ + 24 + 324 * ‖q‖ := by
        have h5 : ‖q⁻¹‖ ≤ ‖q‖⁻¹ := by rw [norm_inv]
        calc ‖q⁻¹ + 24 + 324 * q‖ ≤ ‖q⁻¹ + 24‖ + ‖324 * q‖ := norm_add_le _ _
          _ ≤ (‖q⁻¹‖ + ‖(24 : ℂ)‖) + ‖324 * q‖ := by
              linarith [norm_add_le (q⁻¹) (24 : ℂ)]
          _ = ‖q⁻¹‖ + 24 + 324 * ‖q‖ := by
              rw [norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
          _ ≤ ‖q‖⁻¹ + 24 + 324 * ‖q‖ := by linarith
      refine le_trans (mul_le_mul hR h4 (norm_nonneg _) (by positivity)) ?_
      have h6 : C₄ * ‖q‖ ^ 4 * (‖q‖⁻¹ + 24 + 324 * ‖q‖)
          = C₄ * (‖q‖ ^ 3 + 24 * ‖q‖ ^ 4 + 324 * ‖q‖ ^ 5) := by
        field_simp
      rw [h6]
      have h7 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 3 := by
        nlinarith [pow_nonneg (norm_nonneg q) 3, hq1, hq0]
      have h8 : ‖q‖ ^ 5 ≤ ‖q‖ ^ 3 := by
        nlinarith [pow_nonneg (norm_nonneg q) 3, hq1, hq0]
      nlinarith [h7, h8, pow_nonneg (norm_nonneg q) 3, hC₄.le]
    have h10 : ‖1728 * q ^ 3 - 81648 * q ^ 4‖ ≤ (1728 + 81648) * ‖q‖ ^ 3 := by
      have h11 : ‖(1728 : ℂ) * q ^ 3‖ = 1728 * ‖q‖ ^ 3 := by
        rw [norm_mul, Complex.norm_ofNat, norm_pow]
      have h12 : ‖(81648 : ℂ) * q ^ 4‖ = 81648 * ‖q‖ ^ 4 := by
        rw [norm_mul, Complex.norm_ofNat, norm_pow]
      calc ‖1728 * q ^ 3 - 81648 * q ^ 4‖
          ≤ ‖(1728 : ℂ) * q ^ 3‖ + ‖(81648 : ℂ) * q ^ 4‖ := norm_sub_le _ _
        _ = 1728 * ‖q‖ ^ 3 + 81648 * ‖q‖ ^ 4 := by rw [h11, h12]
        _ ≤ (1728 + 81648) * ‖q‖ ^ 3 := by
            nlinarith [pow_nonneg (norm_nonneg q) 3, hq1, hq0]
    calc ‖1728 * q ^ 3 - 81648 * q ^ 4
          - (Work.Kernels.DeltaFun z - (q - 24 * q ^ 2 + 252 * q ^ 3)) * (q⁻¹ + 24 + 324 * q)‖
        ≤ ‖1728 * q ^ 3 - 81648 * q ^ 4‖
          + ‖(Work.Kernels.DeltaFun z - (q - 24 * q ^ 2 + 252 * q ^ 3)) * (q⁻¹ + 24 + 324 * q)‖ :=
          norm_sub_le _ _
      _ ≤ (1728 + 81648) * ‖q‖ ^ 3 + C₄ * 349 * ‖q‖ ^ 3 := add_le_add h10 h3
      _ = (1728 + 81648 + C₄ * 349) * ‖q‖ ^ 3 := by ring
  -- the denominator bound and the conclusion
  have hlow' : c * ‖q‖ ≤ ‖Work.Kernels.DeltaFun z‖ := by
    have h := hlow z hz
    rwa [← hqnorm] at h
  have hkey : (Work.Kernels.DeltaFun z)⁻¹ - (q⁻¹ + 24 + 324 * q)
      = (1 - Work.Kernels.DeltaFun z * (q⁻¹ + 24 + 324 * q)) / Work.Kernels.DeltaFun z := by
    field_simp
  have hEinv : E⁻¹ ^ 2 = q⁻¹ := by rw [hqE, inv_pow]
  rw [hEinv, hkey, norm_div]
  have hnum0 : (0 : ℝ) ≤ (1728 + 81648 + C₄ * 349) * ‖q‖ ^ 3 := by positivity
  have hDpos : 0 < ‖Work.Kernels.DeltaFun z‖ := lt_of_lt_of_le (by positivity) hlow'
  calc ‖1 - Work.Kernels.DeltaFun z * (q⁻¹ + 24 + 324 * q)‖ / ‖Work.Kernels.DeltaFun z‖
      ≤ ((1728 + 81648 + C₄ * 349) * ‖q‖ ^ 3) / (c * ‖q‖) := by
        exact div_le_div₀ hnum0 hnum (by positivity) hlow'
    _ = (1728 + 81648 + C₄ * 349) / c * ‖q‖ ^ 2 := by
        field_simp
    _ ≤ ((1728 + 81648 + C₄ * 349) / c + 1) * ‖E‖ ^ 4 := by
        have h1 : ‖q‖ ^ 2 = ‖E‖ ^ 4 := by
          rw [hqE, norm_pow]; ring
        rw [h1]
        have h2 : (0 : ℝ) ≤ (1728 + 81648 + C₄ * 349) / c := by positivity
        nlinarith [h2, pow_nonneg (norm_nonneg E) 4]

end Work.Asymptotics.KhatE1Core
