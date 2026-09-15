import Mathlib
import Submission.Commons.Analysis.Calculus.exists_monotone_AC_cusp_bound

namespace Commons.Analysis.Inequalities

open Real

theorem final_interpolation {c₂ κ A₀ Clat CW U V t : ℝ} (d : ℕ)
    (hc₂ : 0 < c₂) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hA₀ : 0 < A₀) (hClat : 1 ≤ Clat)
    (hCW : 0 < CW) (hU : 0 ≤ U) (hV : 0 ≤ V) (ht : 0 ≤ t)
    (hsmall : (4 : ℝ) ^ d * (A₀ * Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ * t ^ (2 * κ)
        + t ^ 2 * CW * Clat) ≤ c₂ ^ 2 / 2)
    (hbound : c₂ ^ 2 * V ≤ (4 : ℝ) ^ d * (A₀ * (Clat * V) ^ (1 - κ)
        * (2 * CW ^ 2 * Clat * U + 2 * t ^ 2 * CW ^ 2 * Clat * V) ^ κ + t ^ 2 * CW * Clat * V)) :
    Real.sqrt V ≤ (2 * (4 : ℝ) ^ d * A₀ * Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ / c₂ ^ 2)
        ^ (1 / (2 * κ)) * Real.sqrt U := by
  have hClat_pos : 0 < Clat := lt_of_lt_of_le one_pos hClat
  have hc2sq_pos : 0 < c₂ ^ 2 := pow_pos hc₂ 2
  by_cases hVz : V = 0
  · rw [hVz, Real.sqrt_zero]
    apply mul_nonneg
    · exact Real.rpow_nonneg (by positivity) _
    · exact Real.sqrt_nonneg U
  have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hVz)
  set B : ℝ := (4 : ℝ) ^ d * A₀ * Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ with hBdef
  set C : ℝ := (4 : ℝ) ^ d * t ^ 2 * CW * Clat with hCdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hsmall_eq : (4 : ℝ) ^ d * (A₀ * Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ * t ^ (2 * κ)
        + t ^ 2 * CW * Clat) = B * t ^ (2 * κ) + C := by
    rw [hBdef, hCdef]; ring
  have hsmall' : B * t ^ (2 * κ) + C ≤ c₂ ^ 2 / 2 := by
    rw [← hsmall_eq]; exact hsmall
  have hclatV : (Clat * V) ^ (1 - κ) = Clat ^ (1 - κ) * V ^ (1 - κ) :=
    Real.mul_rpow (le_of_lt hClat_pos) hV
  have hbase : 2 * CW ^ 2 * Clat * U + 2 * t ^ 2 * CW ^ 2 * Clat * V
      = (2 * CW ^ 2 * Clat) * (U + t ^ 2 * V) := by ring
  have h2 : (2 * CW ^ 2 * Clat * U + 2 * t ^ 2 * CW ^ 2 * Clat * V) ^ κ
      = (2 * CW ^ 2 * Clat) ^ κ * (U + t ^ 2 * V) ^ κ := by
    rw [hbase, Real.mul_rpow (by positivity) (by positivity)]
  have hbound_eq : (4 : ℝ) ^ d * (A₀ * (Clat * V) ^ (1 - κ)
        * (2 * CW ^ 2 * Clat * U + 2 * t ^ 2 * CW ^ 2 * Clat * V) ^ κ + t ^ 2 * CW * Clat * V)
      = B * V ^ (1 - κ) * (U + t ^ 2 * V) ^ κ + C * V := by
    rw [hBdef, hCdef, hclatV, h2]; ring
  have hbound' : c₂ ^ 2 * V ≤ B * V ^ (1 - κ) * (U + t ^ 2 * V) ^ κ + C * V := by
    rw [← hbound_eq]; exact hbound
  have hsub : (U + t ^ 2 * V) ^ κ ≤ U ^ κ + (t ^ 2 * V) ^ κ :=
    Commons.Analysis.Calculus.rpow_add_le_add_rpow_real hU (by positivity) (le_of_lt hκ0) hκ1
  have ht2pow : (t ^ 2) ^ κ = t ^ (2 * κ) := by
    rw [← Real.rpow_natCast t 2]
    exact (Real.rpow_mul ht 2 κ).symm
  have htVpow : (t ^ 2 * V) ^ κ = t ^ (2 * κ) * V ^ κ := by
    have h1 : (t ^ 2 * V) ^ κ = (t ^ 2) ^ κ * V ^ κ := Real.mul_rpow (by positivity) hV
    rw [h1, ht2pow]
  have hVpow : V ^ (1 - κ) * V ^ κ = V := by
    rw [← Real.rpow_add hVpos (1 - κ) κ]
    rw [show (1 - κ) + κ = 1 by ring, Real.rpow_one]
  have hterm4 : B * V ^ (1 - κ) * (t ^ (2 * κ) * V ^ κ) = B * t ^ (2 * κ) * V := by
    rw [show B * V ^ (1 - κ) * (t ^ (2 * κ) * V ^ κ) = (V ^ (1 - κ) * V ^ κ) * (B * t ^ (2 * κ)) by ring]
    rw [hVpow]; ring
  have hmain : c₂ ^ 2 * V ≤ B * V ^ (1 - κ) * U ^ κ + (c₂ ^ 2 / 2) * V := by
    calc c₂ ^ 2 * V
        ≤ B * V ^ (1 - κ) * (U + t ^ 2 * V) ^ κ + C * V := hbound'
      _ ≤ B * V ^ (1 - κ) * (U ^ κ + (t ^ 2 * V) ^ κ) + C * V := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left hsub; positivity
            · exact le_refl _
      _ = B * V ^ (1 - κ) * U ^ κ + B * V ^ (1 - κ) * (t ^ 2 * V) ^ κ + C * V := by ring
      _ = B * V ^ (1 - κ) * U ^ κ + B * t ^ (2 * κ) * V + C * V := by rw [htVpow, hterm4]
      _ = B * V ^ (1 - κ) * U ^ κ + (B * t ^ (2 * κ) + C) * V := by ring
      _ ≤ B * V ^ (1 - κ) * U ^ κ + (c₂ ^ 2 / 2) * V := by
            apply add_le_add
            · exact le_refl _
            · exact mul_le_mul_of_nonneg_right hsmall' hV
  have hpre : (c₂ ^ 2 / 2) * V ≤ B * V ^ (1 - κ) * U ^ κ := by linarith [hmain]
  have hVm1 : V * V ^ (κ - 1) = V ^ κ := by
    have h := Real.rpow_add hVpos 1 (κ - 1)
    rw [Real.rpow_one, show (1 : ℝ) + (κ - 1) = κ by ring] at h
    exact h.symm
  have hVcancel : V ^ (1 - κ) * V ^ (κ - 1) = 1 := by
    have h := Real.rpow_add hVpos (1 - κ) (κ - 1)
    rw [show (1 - κ) + (κ - 1) = 0 by ring, Real.rpow_zero] at h
    exact h.symm
  have hmul := mul_le_mul_of_nonneg_right hpre (Real.rpow_nonneg hV (κ - 1))
  have hL : (c₂ ^ 2 / 2) * V * V ^ (κ - 1) = (c₂ ^ 2 / 2) * V ^ κ := by
    rw [mul_assoc, hVm1]
  have hR : (B * V ^ (1 - κ) * U ^ κ) * V ^ (κ - 1) = B * U ^ κ := by
    rw [show (B * V ^ (1 - κ) * U ^ κ) * V ^ (κ - 1)
          = B * U ^ κ * (V ^ (1 - κ) * V ^ (κ - 1)) by ring, hVcancel, mul_one]
  rw [hL, hR] at hmul
  have h11 : (2 / c₂ ^ 2) * (c₂ ^ 2 / 2) = 1 := by field_simp
  have hgoal2 : V ^ κ ≤ (2 * B / c₂ ^ 2) * U ^ κ := by
    have h := mul_le_mul_of_nonneg_left hmul (by positivity : (0:ℝ) ≤ 2 / c₂ ^ 2)
    rw [show (2 / c₂ ^ 2) * ((c₂ ^ 2 / 2) * V ^ κ) = V ^ κ by rw [← mul_assoc, h11]; ring,
        show (2 / c₂ ^ 2) * (B * U ^ κ) = (2 * B / c₂ ^ 2) * U ^ κ by ring] at h
    exact h
  have hκe : κ * (1 / (2 * κ)) = 1 / 2 := by
    field_simp
  have he_pos : 0 < 1 / (2 * κ) := by positivity
  have key := Real.rpow_le_rpow (Real.rpow_nonneg hV κ) hgoal2 (le_of_lt he_pos)
  rw [← Real.rpow_mul hV κ (1/(2*κ)), Real.mul_rpow (by positivity) (Real.rpow_nonneg hU κ),
      ← Real.rpow_mul hU κ (1/(2*κ))] at key
  rw [hκe] at key
  rw [← Real.sqrt_eq_rpow V, ← Real.sqrt_eq_rpow U] at key
  have hcoeff : (2 * B / c₂ ^ 2) = (2 * (4 : ℝ) ^ d * A₀ * Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ / c₂ ^ 2) := by
    rw [hBdef]; ring
  rw [hcoeff] at key
  exact key

end Commons.Analysis.Inequalities
