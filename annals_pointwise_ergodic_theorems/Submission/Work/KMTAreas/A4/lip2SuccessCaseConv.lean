import Mathlib

namespace Work.KMTAreas.A4

/-- For `x > 0` and real `y`, `x ^ (-y) = (x⁻¹) ^ y`. -/
lemma rpow_neg_eq_inv_rpow (x : ℝ) (hx : 0 < x) (y : ℝ) : x ^ (-y) = (x⁻¹) ^ y := by
  rw [Real.rpow_neg hx.le, Real.inv_rpow hx.le]

/-- Success-case conversion of the `lip-2` tail chain: the truncated length `q`, the
truncation cut-off `S`/`L` and the Diophantine error `X` all gain the same weight
`ε ^ (-K')`, and the error also gains the full `M ^ (-d)` decay. -/
theorem lip2SuccessCaseConv (Cip Kip CB K' : ℝ) (hCip : 0 < Cip) (hKip : 0 < Kip) (hCB : 1 ≤ CB) (d : ℕ) (hK' : Kip + d ≤ K') : ∃ C' : ℝ, 0 < C' ∧ ∀ (q S L M ε X : ℝ), 0 < ε → ε ≤ 1 → 0 < L → 0 < S → S ≤ L → L ≤ CB * M → ε * M / CB ≤ S → 0 < q → q ≤ Cip * (S / L) ^ (-Kip) → |X| ≤ Cip * (S / L) ^ (-Kip) / L ^ d → q ≤ C' * ε ^ (-K') ∧ |X| ≤ C' * ε ^ (-K') / M ^ d := by
  have hCB0 : 0 < CB := lt_of_lt_of_le one_pos hCB
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  refine ⟨Cip * CB ^ (2 * Kip + (d:ℝ)), ?_, ?_⟩
  · exact mul_pos hCip (Real.rpow_pos_of_pos hCB0 _)
  · intro q S L M ε X hε0 hε1 hL hS hSL hLM hSM hq hqle hX
    have hM0 : 0 < M := pos_of_mul_pos_right (lt_of_lt_of_le hL hLM) hCB0.le
    have hSLpos : 0 < S / L := div_pos hS hL
    have hLSpos : 0 < L / S := div_pos hL hS
    have hεinv1 : (1:ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε0).mpr hε1
    have hswap : (S / L) ^ (-Kip) = (L / S) ^ Kip := by
      rw [rpow_neg_eq_inv_rpow (S/L) hSLpos Kip, inv_div]
    -- `M` is small compared with `S * CB`, i.e. `M ≤ S * CB * ε⁻¹`
    have hM' : M ≤ S * CB * ε⁻¹ := by
      have h1 : ε * M ≤ S * CB := (div_le_iff₀ hCB0).mp hSM
      have h2 : M * ε ≤ S * CB := by rw [mul_comm M ε]; exact h1
      have h3 : M ≤ S * CB / ε := (le_div_iff₀ hε0).mpr h2
      rwa [div_eq_mul_inv] at h3
    have hpow : (S / L) ^ (-Kip) ≤ CB ^ (2*Kip) * ε ^ (-Kip) := by
      rw [hswap]
      have hls : L / S ≤ CB * (CB * ε⁻¹) := by
        rw [div_le_iff₀ hS]
        calc L ≤ CB * M := hLM
          _ ≤ CB * (S * CB * ε⁻¹) := mul_le_mul_of_nonneg_left hM' hCB0.le
          _ = (CB * (CB * ε⁻¹)) * S := by ring
      have h2 : (CB * (CB * ε⁻¹))^Kip = CB^(2*Kip) * ε^(-Kip) := by
        rw [Real.mul_rpow hCB0.le (mul_nonneg hCB0.le (inv_nonneg.mpr hε0.le)),
            Real.mul_rpow hCB0.le (inv_nonneg.mpr hε0.le)]
        rw [← mul_assoc, ← Real.rpow_add hCB0, ← rpow_neg_eq_inv_rpow ε hε0 Kip]
        rw [show Kip + Kip = 2 * Kip by ring]
      exact le_trans (Real.rpow_le_rpow hLSpos.le hls hKip.le) (le_of_eq h2)
    have hεKK : ε ^ (-Kip) ≤ ε ^ (-K') := by
      rw [rpow_neg_eq_inv_rpow ε hε0 Kip, rpow_neg_eq_inv_rpow ε hε0 K']
      exact Real.rpow_le_rpow_of_exponent_le hεinv1 (le_trans (le_add_of_nonneg_right hd0) hK')
    have hCB2e : CB ^ (2*Kip) ≤ CB ^ (2*Kip + (d:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hCB (le_add_of_nonneg_right hd0)
    refine ⟨?_, ?_⟩
    · calc q ≤ Cip * (S / L) ^ (-Kip) := hqle
        _ ≤ Cip * (CB^(2*Kip) * ε^(-Kip)) := mul_le_mul_of_nonneg_left hpow hCip.le
        _ = Cip * CB^(2*Kip) * ε^(-Kip) := by ring
        _ ≤ Cip * CB^(2*Kip) * ε^(-K') := mul_le_mul_of_nonneg_left hεKK (mul_nonneg hCip.le (Real.rpow_nonneg hCB0.le _))
        _ ≤ Cip * CB^(2*Kip + (d:ℝ)) * ε^(-K') :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCB2e hCip.le) (Real.rpow_nonneg hε0.le _)
    · have hεd : (ε^d)⁻¹ = ε^(-(d:ℝ)) := by rw [← Real.rpow_natCast ε d, ← Real.rpow_neg hε0.le]
      have hMLe : M / L ≤ CB * ε⁻¹ := by
        rw [div_le_iff₀ hL]
        have h6 : S * CB * ε⁻¹ ≤ L * CB * ε⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSL hCB0.le) (inv_nonneg.mpr hε0.le)
        have h7 : (CB * ε⁻¹) * L = L * CB * ε⁻¹ := by ring
        linarith [hM', h6, h7]
      have hMLd : (M / L)^d ≤ CB^d * ε^(-(d:ℝ)) := by
        have h1 : (M/L)^d ≤ (CB * ε⁻¹)^d := pow_le_pow_left₀ (div_nonneg hM0.le hL.le) hMLe d
        have h2 : (CB * ε⁻¹)^d = CB^d * ε^(-(d:ℝ)) := by rw [mul_pow, inv_pow, hεd]
        exact le_trans h1 (le_of_eq h2)
      have hXm : |X| * M^d ≤ Cip * (S / L)^(-Kip) * (M / L)^d := by
        calc |X| * M^d ≤ (Cip * (S / L)^(-Kip) / L^d) * M^d :=
              mul_le_mul_of_nonneg_right hX (pow_nonneg hM0.le d)
          _ = Cip * (S / L)^(-Kip) * (M^d / L^d) := by rw [div_eq_mul_inv]; ring
          _ = Cip * (S / L)^(-Kip) * (M / L)^d := by rw [div_pow]
      have hXm2 : |X| * M^d ≤ Cip * (CB^(2*Kip) * ε^(-Kip)) * (CB^d * ε^(-(d:ℝ))) := by
        refine le_trans hXm ?_
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hpow hCip.le
        · exact hMLd
        · exact pow_nonneg (div_nonneg hM0.le hL.le) d
        · exact mul_nonneg hCip.le (mul_nonneg (Real.rpow_nonneg hCB0.le _) (Real.rpow_nonneg hε0.le _))
      have hprod1 : CB^(2*Kip) * CB^d = CB^(2*Kip + (d:ℝ)) := by
        rw [← Real.rpow_natCast CB d, ← Real.rpow_add hCB0]
      have hprod2 : ε^(-Kip) * ε^(-(d:ℝ)) = ε^(-(Kip + (d:ℝ))) := by
        rw [← Real.rpow_add hε0]
        congr 1
        ring
      have hXfin : |X| * M^d ≤ Cip * CB^(2*Kip + (d:ℝ)) * ε^(-K') := by
        calc |X| * M^d ≤ Cip * (CB^(2*Kip) * ε^(-Kip)) * (CB^d * ε^(-(d:ℝ))) := hXm2
          _ = Cip * (CB^(2*Kip) * CB^d) * (ε^(-Kip) * ε^(-(d:ℝ))) := by ring
          _ = Cip * CB^(2*Kip + (d:ℝ)) * ε^(-(Kip + (d:ℝ))) := by rw [hprod1, hprod2]
          _ ≤ Cip * CB^(2*Kip + (d:ℝ)) * ε^(-K') := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCip.le (Real.rpow_nonneg hCB0.le _))
                rw [rpow_neg_eq_inv_rpow ε hε0 (Kip + (d:ℝ)), rpow_neg_eq_inv_rpow ε hε0 K']
                exact Real.rpow_le_rpow_of_exponent_le hεinv1 hK'
      exact (le_div_iff₀ (pow_pos hM0 d)).mpr hXfin

end Work.KMTAreas.A4
