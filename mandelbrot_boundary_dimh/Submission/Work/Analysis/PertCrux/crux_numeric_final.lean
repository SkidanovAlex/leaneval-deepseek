import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Analysis.PertCrux.crux_bounds
import Submission.Work.Analysis.PertCrux.sqrt_two_delta0_bound
import Submission.Work.Analysis.PertCrux.inv_alpha_re_ge
import Submission.Work.Analysis.PertCrux.two_dtau_two_MK_lt_inv
import Submission.Work.Analysis.PertCrux.eight_Cgl_Rsc_sq_le

namespace Work.Analysis.PertCrux

/-- The final numeric crux of the perturbation argument: the four scalar bounds that the
rest of the assembly consumes.  Every hypothesis is a published interface hypothesis of
the perturbation area; the essential mechanism is that `Ξ' ≥ 1 + 64π` is a *large*
constant (`Ξ' > 193`), while `Λ` is polynomially bounded in `Ξ'` and `Rsc`, `dtau`, `m`
in turn polynomially bounded in `Λ`, so all the "small" quantities are dominated by
`Ξ'^40`, and `1/‖α‖ ≳ Ξ'^40` by hypothesis. -/
theorem crux_numeric_final {Ξ' ρ₁ δ δ₀ Rsc Λ MK CW RG dtau εs Cgl : ℝ} {σ : ℂ} {m : ℕ} {α : ℂ}
    (hΞ' : 1 + 64 * Real.pi ≤ Ξ')
    (hρ₁pos : 0 < ρ₁) (hρ₁Ξ : ρ₁ ≤ Ξ') (hδ : 0 < δ) (hδΞ : δ ≤ Ξ')
    (hMK0 : 0 ≤ MK) (hCW0 : 0 ≤ CW) (hRG2 : 2 ≤ RG)
    (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRGΞ : RG ≤ Ξ')
    (hCgl0 : 0 < Cgl) (hCglΞ : Cgl ≤ Ξ')
    (hΛ64 : 64 ≤ Λ) (hΛΞ : Ξ' ≤ Λ) (hΛMK : MK ≤ Λ) (hΛCW : CW ≤ Λ) (hΛRG : RG ≤ Λ / 8)
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 + 10 ^ 6)
    (hdtau0 : 0 ≤ dtau) (hdtauΛ : dtau ≤ Λ / 16)
    (hRsc0 : 0 < Rsc) (hRscUB : Rsc ≤ 200 * Λ ^ 2)
    (hmUB : (m : ℝ) ≤ (Ξ' + 3 * Λ + MK + 5 * CW + 2) ^ 2 + 2)
    (hδ₀ : δ₀ ≤ ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200))
    (hσ : ‖σ‖ ≤ Real.sqrt (2 * δ₀))
    (hεs0 : 0 < εs) (hεss : εs ≤ δ / (10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20))
    (hαne : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hαinv : (Ξ' ^ 2 + 1) ^ 20 ≤ 1 / ‖α‖) :
    ‖σ‖ < (1 / 2) / Rsc ∧
    (2 * dtau + 2 * MK + 12 < 1 / ‖α‖) ∧
    ((m : ℝ) + MK + dtau + Ξ' + 2 * RG + 4 < (1 / α).re) ∧
    (8 * Cgl * Rsc ^ 2 ≤ 10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20) := by
  -- `Ξ' ≥ 1 + 64π > 193`: from now on `Ξ'` is a large constant.
  have hX193 : 193 < Ξ' := by nlinarith [Real.pi_gt_three]
  have hXpos : (0 : ℝ) < Ξ' := by linarith
  have hX1 : (1 : ℝ) ≤ Ξ' := by linarith
  have hX10 : (10 : ℝ) ≤ Ξ' := by linarith
  -- All the individual quantities are polynomially controlled by `Ξ'`.
  obtain ⟨hLam, hdtauB, hRscB, hmB⟩ :=
    crux_bounds hX10 hMKΞ hCWΞ hRGΞ hΛ64 hΛUB hdtauΛ hRscUB hmUB
  -- The `√(2δ₀)` bound and the domination of the "small" quantities by `Ξ'^40`.
  have hsqrt : Real.sqrt (2 * δ₀) ≤ 2 / (10 ^ 50 * Ξ' ^ 198) :=
    sqrt_two_delta0_bound hX10 hδ hρ₁pos hρ₁Ξ hδΞ hδ₀
  have hX40exp : Ξ' ^ 40 ≤ (Ξ' ^ 2 + 1) ^ 20 := by
    have h2 : Ξ' ^ 2 ≤ Ξ' ^ 2 + 1 := by linarith [sq_nonneg Ξ']
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Ξ' ^ 2) h2 20
    have he : (Ξ' ^ 2) ^ 20 = Ξ' ^ 40 := by ring
    rwa [he] at h
  have hX40 : Ξ' ^ 40 ≤ 1 / ‖α‖ := le_trans hX40exp hαinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) `‖σ‖ < (1/2)/Rsc`: the tiny `√(2δ₀) ≤ 2/(10^50 Ξ'^198)` beats `Rsc ≤ 9.6·10^17 Ξ'^6`.
    have hX6le198 : Ξ' ^ 6 ≤ Ξ' ^ 198 := pow_le_pow_right₀ hX1 (by norm_num)
    have hRsc198 : Rsc ≤ 960000000000000000 * Ξ' ^ 198 :=
      le_trans hRscB (mul_le_mul_of_nonneg_left hX6le198 (by norm_num))
    have hprod : ‖σ‖ * Rsc < 1 / 2 := by
      have h1 : ‖σ‖ * Rsc ≤ Real.sqrt (2 * δ₀) * Rsc :=
        mul_le_mul_of_nonneg_right hσ (le_of_lt hRsc0)
      have h2 : Real.sqrt (2 * δ₀) * Rsc
          ≤ (2 / (10 ^ 50 * Ξ' ^ 198)) * (960000000000000000 * Ξ' ^ 198) :=
        mul_le_mul hsqrt hRsc198 (le_of_lt hRsc0) (by positivity)
      have h3 : (2 / (10 ^ 50 * Ξ' ^ 198)) * (960000000000000000 * Ξ' ^ 198)
          = 1920000000000000000 / 10 ^ 50 := by
        rw [div_mul_eq_mul_div,
          show 2 * (960000000000000000 * Ξ' ^ 198)
            = (2 * 960000000000000000) * Ξ' ^ 198 from by ring,
          mul_div_mul_right _ _ (ne_of_gt (pow_pos hXpos 198))]
        norm_num
      have h4 : (1920000000000000000 : ℝ) / 10 ^ 50 < 1 / 2 := by norm_num
      linarith
    rw [lt_div_iff₀ hRsc0]
    exact hprod
  · -- (2) `2·dtau + 2·MK + 12 < 1/‖α‖`, since the left side is `≤ 10^7 Ξ'^3 ≪ Ξ'^40`.
    exact two_dtau_two_MK_lt_inv hX193 hMKΞ hdtauB hX40
  · -- (3) `m + MK + dtau + Ξ' + 2RG + 4 < (1/α).re`, with `(1/α).re ≥ Ξ'^40/2`.
    have hre : (1 / 2) * (Ξ' ^ 2 + 1) ^ 20 ≤ (1 / α).re :=
      inv_alpha_re_ge hαne hinf hαinv
    have hX3le6 : Ξ' ^ 3 ≤ Ξ' ^ 6 := pow_le_pow_right₀ hX1 (by norm_num)
    have hXle6 : Ξ' ≤ Ξ' ^ 6 := by
      have h := pow_le_pow_right₀ hX1 (show (1 : ℕ) ≤ 6 by norm_num)
      simpa using h
    have hX6ge1 : (1 : ℝ) ≤ Ξ' ^ 6 := one_le_pow₀ hX1
    have hLHS : (m : ℝ) + MK + dtau + Ξ' + 2 * RG + 4
        ≤ 46100000000000000 * Ξ' ^ 6 := by
      have h1 : (m : ℝ) + MK + dtau + Ξ' + 2 * RG + 4
          ≤ 46000000000000000 * Ξ' ^ 6 + Ξ' + 4400000 * Ξ' ^ 3 + Ξ' + 2 * Ξ' + 4 := by
        linarith
      have h2 : 46000000000000000 * Ξ' ^ 6 + Ξ' + 4400000 * Ξ' ^ 3 + Ξ' + 2 * Ξ' + 4
          ≤ 46000000000000000 * Ξ' ^ 6 + Ξ' ^ 6 + 4400000 * Ξ' ^ 6 + Ξ' ^ 6
            + 2 * Ξ' ^ 6 + 4 * Ξ' ^ 6 := by
        linarith [hXle6, hX3le6, hX6ge1]
      linarith
    have hX34 : 193 ^ 34 ≤ Ξ' ^ 34 := pow_le_pow_left₀ (by norm_num) (le_of_lt hX193) 34
    have hX6pos : 0 < Ξ' ^ 6 := pow_pos hXpos 6
    have hbig : 46100000000000000 * Ξ' ^ 6 < (Ξ' ^ 2 + 1) ^ 20 / 2 := by
      have h40 : Ξ' ^ 40 = Ξ' ^ 6 * Ξ' ^ 34 := by ring
      have hmid : 46100000000000000 * Ξ' ^ 6 < Ξ' ^ 40 / 2 := by
        rw [h40]
        have hnum : (46100000000000000 : ℝ) < 193 ^ 34 / 2 := by norm_num
        calc (46100000000000000 : ℝ) * Ξ' ^ 6 < (193 ^ 34 / 2) * Ξ' ^ 6 :=
              mul_lt_mul_of_pos_right hnum hX6pos
          _ ≤ (Ξ' ^ 34 / 2) * Ξ' ^ 6 := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hX6pos)
              exact div_le_div_of_nonneg_right hX34 (by norm_num)
          _ = Ξ' ^ 6 * Ξ' ^ 34 / 2 := by ring
      linarith [hX40exp]
    linarith
  · -- (4) `8·Cgl·Rsc^2 ≤ 10^9 (Ξ'^2+1)^20`: `Cgl ≤ Ξ'`, `Rsc ≤ 9.6·10^17 Ξ'^6`,
    -- so the left side is `≤ 7.4·10^36 Ξ'^13 ≪ 10^9 Ξ'^40`.
    exact eight_Cgl_Rsc_sq_le hX193 hCgl0 hCglΞ hRsc0 hRscB

end Work.Analysis.PertCrux
