import Mathlib
import Submission.Work.GM.Affine.region_II_vocab

/-!
# GM §9: the window integral of `Bsum`

The region-II reduction rewrites `∫ ‖ĝ(ξ)‖² dξ` by the change of variables
`ξ = m·(ℓ + τ/M₃)`, `dξ = (m/M₃) dτ`, on each resonant window
`|ξ - mℓ| ≤ 2|m|/M₃`.  This file records the resulting *exact* identity for the
`m₂`-sum `Bsum`: for `m ≠ 0`,

`∫_{mℓ - 2|m|/M₃}^{mℓ + 2|m|/M₃} ‖Bsum f M₂ (ξ/m)‖² dξ
   = (|m|/M₃) · ∫_{-2}^{2} ‖Hfun f M₂ M₃ ℓ τ‖² dτ`,

which is just the affine substitution `ξ = mℓ + (m/M₃)τ` (no approximation).

The two elementary ingredients are `window_affine` (the substitution `∫_{d-2c}^{d+2c} F = c ∫_{-2}^2 F(d+c·)`)
and `window_affine_abs` (the same with `|c|` in place of `c`, so that the sign of `c` is immaterial).
-/

open MeasureTheory

namespace Work.GM.Affine

/-- Affine change of variables on a window centred at `d` of half-width `2c`:
`∫_{d-2c}^{d+2c} F x dx = c · ∫_{-2}^{2} F (d + c τ) dτ` for `c ≠ 0`. -/
lemma window_affine (F : ℝ → ℝ) {c d : ℝ} (hc : c ≠ 0) :
    (∫ x in (d - 2*c)..(d + 2*c), F x) = c * (∫ τ in (-2:ℝ)..2, F (d + c*τ)) := by
  have h := intervalIntegral.integral_comp_add_mul (a := (-2:ℝ)) (b := 2) (c := c) F hc d
  rw [show d + c * (-2:ℝ) = d - 2*c by ring, show d + c * (2:ℝ) = d + 2*c by ring] at h
  rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The sign-free form of `window_affine`, with the half-width written `2|c|`:
`∫_{d-2|c|}^{d+2|c|} F x dx = |c| · ∫_{-2}^{2} F (d + c τ) dτ` for `c ≠ 0`. -/
lemma window_affine_abs (F : ℝ → ℝ) {c d : ℝ} (hc : c ≠ 0) :
    (∫ x in (d - 2*|c|)..(d + 2*|c|), F x) = |c| * (∫ τ in (-2:ℝ)..2, F (d + c*τ)) := by
  rcases le_or_gt 0 c with hc0 | hc0
  · rw [abs_of_nonneg hc0]
    exact window_affine F hc
  · rw [abs_of_neg hc0]
    rw [show d - 2 * -c = d + 2*c by ring, show d + 2 * -c = d - 2*c by ring]
    rw [intervalIntegral.integral_symm, window_affine F hc]
    ring

/-- The change of variables `ξ = m·(ℓ + τ/M₃)` on the resonant window
`|ξ - mℓ| ≤ 2|m|/M₃`, in the exact form used in the region-II reduction. -/
theorem window_integral_Bsum {M₂ M₃ : ℝ} (hM₃ : 0 < M₃) (f : ℝ → ℝ) (ℓ : ℤ) {m : ℤ}
    (hm : m ≠ 0) :
    (∫ ξ in Set.Icc ((m:ℝ)*(ℓ:ℝ) - 2*|(m:ℝ)|/M₃) ((m:ℝ)*(ℓ:ℝ) + 2*|(m:ℝ)|/M₃),
        ‖Bsum f M₂ (ξ/(m:ℝ))‖^2)
      = (|(m:ℝ)|/M₃) * (∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2) := by
  have hmR : (m:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hM₃ne : M₃ ≠ 0 := ne_of_gt hM₃
  set c : ℝ := (m:ℝ)/M₃ with hc
  set d : ℝ := (m:ℝ)*(ℓ:ℝ) with hd
  have hcne : c ≠ 0 := by rw [hc]; exact div_ne_zero hmR hM₃ne
  have habsc : |c| = |(m:ℝ)|/M₃ := by rw [hc, abs_div, abs_of_pos hM₃]
  set F : ℝ → ℝ := fun ξ => ‖Bsum f M₂ (ξ/(m:ℝ))‖^2 with hF
  have hAB : d - 2*|c| = (m:ℝ)*(ℓ:ℝ) - 2*|(m:ℝ)|/M₃ := by rw [hd, habsc]; ring
  have hAB' : d + 2*|c| = (m:ℝ)*(ℓ:ℝ) + 2*|(m:ℝ)|/M₃ := by rw [hd, habsc]; ring
  have hle : d - 2*|c| ≤ d + 2*|c| := by have := abs_nonneg c; linarith
  have hIcc : (∫ ξ in Set.Icc (d - 2*|c|) (d + 2*|c|), F ξ)
      = ∫ ξ in (d - 2*|c|)..(d + 2*|c|), F ξ := by
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  have hkey := window_affine_abs F (c := c) (d := d) hcne
  have hint : (∫ τ in (-2:ℝ)..2, F (d + c*τ)) = ∫ τ in (-2:ℝ)..2, ‖Hfun f M₂ M₃ ℓ τ‖^2 := by
    apply intervalIntegral.integral_congr
    intro τ _
    have harg : (d + c*τ)/(m:ℝ) = (ℓ:ℝ) + τ/M₃ := by
      have hdm : d + c*τ = (m:ℝ) * ((ℓ:ℝ) + τ/M₃) := by rw [hd, hc]; ring
      rw [hdm, mul_div_cancel_left₀ _ hmR]
    simp only [hF, Hfun_eq_Bsum, harg]
  rw [← hAB, ← hAB', hIcc, hkey, hint, habsc]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (-2:ℝ) ≤ 2),
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]

end Work.GM.Affine
