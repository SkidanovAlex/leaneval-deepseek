import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Numerical verifications for `completion_of_sums`

The two case distinctions `η'H ≤ 100` and `100 < η'H` of the completion-of-sums argument,
reduced to explicit real inequalities.
-/

open Real

namespace Work.BMF

/-- Numerical verification for the `η'H ≤ 100` case. -/
lemma case1_bounds (Kphi η' H A D near far : ℝ) (hK : 0 ≤ Kphi) (hη : 0 < η') (hη1 : η' ≤ 1)
    (hH : 1 ≤ H) (hηH : η' * H ≤ 100)
    (hA : A ≤ H + 3)
    (hD : D = Kphi / (2 * Real.pi ^ 2))
    (hnear : near ≤ 4 * Real.sqrt (A * D))
    (hfar : far ≤ 2 * D / ((256 * (Kphi + 1) + 64) / (η' ^ 2 * H))) :
    (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * near + (H + 1) * far < η' * H := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hηHpos : 0 < η' * H := mul_pos hη hHpos
  have hK1 : 0 < Kphi + 1 := by linarith
  have hσpos : 0 < Real.sqrt (Kphi + 1) := Real.sqrt_pos.mpr hK1
  have hCxpos : 0 < 256 * (Kphi + 1) + 64 := by linarith
  have hπ2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  -- Step 1: A * D ≤ 9 * (Kphi/η')
  have hH3 : H + 3 ≤ 103 / η' := by
    rw [le_div_iff₀ hη]
    nlinarith [hηH, hη1]
  have hAD : A * D ≤ 9 * (Kphi / η') := by
    have h1 : A * D ≤ (103 / η') * (Kphi / (2 * Real.pi ^ 2)) := by
      rw [hD]
      exact mul_le_mul_of_nonneg_right (le_trans hA hH3) (div_nonneg hK (by positivity))
    have h2 : (103 / η') * (Kphi / (2 * Real.pi ^ 2)) ≤ 9 * (Kphi / η') := by
      have hpi : (103 : ℝ) / (2 * Real.pi ^ 2) ≤ 9 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hπ2]
      have hkey : (103 / η') * (Kphi / (2 * Real.pi ^ 2))
          = (103 / (2 * Real.pi ^ 2)) * (Kphi / η') := by ring_nf
      rw [hkey]
      exact mul_le_mul_of_nonneg_right hpi (div_nonneg hK hη.le)
    linarith
  have hsqrtAD : Real.sqrt (A * D) ≤ 3 * Real.sqrt (Kphi / η') := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h2 : (3 * Real.sqrt (Kphi / η')) ^ 2 = 9 * (Kphi / η') := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hK hη.le)]
      norm_num
    rw [h2]
    exact hAD
  have hnear' : near ≤ 12 * Real.sqrt (Kphi / η') := by linarith
  -- Step 2: key square-root inequality
  have hkey : 48 * η' ^ 3 * Real.sqrt (Kphi / η') ≤ 1000 * Real.sqrt (Kphi + 1) := by
    have h1 : 48 * η' ^ 3 * Real.sqrt (Kphi / η')
        = Real.sqrt ((48 * η' ^ 3) ^ 2 * (Kphi / η')) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : 1000 * Real.sqrt (Kphi + 1) = Real.sqrt ((1000 : ℝ) ^ 2 * (Kphi + 1)) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h1, h2]
    apply Real.sqrt_le_sqrt
    have h3 : (48 * η' ^ 3) ^ 2 * (Kphi / η') = 2304 * η' ^ 5 * Kphi := by
      field_simp
      ring
    rw [h3]
    have hp2 : η' ^ 2 ≤ 1 := by nlinarith [hη1, hη, sq_nonneg η']
    have hp3 : η' ^ 3 ≤ 1 := by nlinarith [hη1, hη, hp2, sq_nonneg η']
    have hp5 : η' ^ 5 ≤ 1 := by
      calc η' ^ 5 = η' ^ 3 * η' ^ 2 := by ring
        _ ≤ 1 * 1 := mul_le_mul hp3 hp2 (by positivity) (by norm_num)
        _ = 1 := by ring
    have h4 : 2304 * η' ^ 5 * Kphi ≤ 2304 * Kphi := by nlinarith [hp5, hK]
    nlinarith [h4, hK]
  -- Term 1
  have ht1 : (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * near ≤ η' * H / 4 := by
    have hcoef : 0 ≤ (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H :=
      mul_nonneg (mul_nonneg (div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) hσpos)))
        (pow_nonneg hη.le 4)) hHpos.le
    calc (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * near
        ≤ (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * (12 * Real.sqrt (Kphi / η')) :=
          mul_le_mul_of_nonneg_left hnear' hcoef
      _ = η' * H * (12 * η' ^ 3 * Real.sqrt (Kphi / η') / (1000 * Real.sqrt (Kphi + 1))) := by
          ring_nf
      _ ≤ η' * H * (1 / 4) := by
          refine mul_le_mul_of_nonneg_left ?_ hηHpos.le
          rw [div_le_iff₀ (by positivity)]
          linarith [hkey]
      _ = η' * H / 4 := by ring
  -- Term 2
  have ht2 : (H + 1) * far ≤ η' * H / 4 := by
    have hfarC : far ≤ 2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64) := by
      have hEq : 2 * D / ((256 * (Kphi + 1) + 64) / (η' ^ 2 * H))
          = 2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64) := by
        field_simp
      rw [← hEq]
      exact hfar
    have h1 : (H + 1) * far ≤ (H + 1) * (2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64)) :=
      mul_le_mul_of_nonneg_left hfarC (by linarith)
    have h2 : (H + 1) * (2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64)) ≤ η' * H / 4 := by
      rw [show (H + 1) * (2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64))
          = (H + 1) * (2 * D * η' ^ 2 * H) / (256 * (Kphi + 1) + 64) from by ring,
        div_le_iff₀ hCxpos]
      have heq : (H + 1) * (2 * D * η' ^ 2 * H)
          = ((H + 1) * η' / Real.pi ^ 2) * (η' * H * Kphi) := by
        rw [hD]; ring_nf
      rw [heq]
      have hratio : (H + 1) * η' / Real.pi ^ 2 ≤ 64 := by
        have h1 : (H + 1) * η' ≤ 101 := by nlinarith [hηH, hη1]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
        nlinarith [h1, hπ2]
      have h3 : 0 ≤ η' * H * Kphi := mul_nonneg (mul_nonneg hη.le hHpos.le) hK
      calc ((H + 1) * η' / Real.pi ^ 2) * (η' * H * Kphi)
          ≤ 64 * (η' * H * Kphi) := mul_le_mul_of_nonneg_right hratio h3
        _ ≤ η' * H / 4 * (256 * (Kphi + 1) + 64) := by nlinarith [hηHpos, hK]
    linarith
  linarith [ht1, ht2, hηHpos]


/-- Numerical verification for the `100 < η'H` case. -/
lemma case2_bounds (Kphi η' H A D near far E : ℝ) (hK : 0 ≤ Kphi) (hη : 0 < η') (hη1 : η' ≤ 1)
    (hH : 1 ≤ H) (hηH : 100 < η' * H)
    (hA : A ≤ H + η' * H / 16 + 1)
    (hD : D = (2 * Kphi / (η' * H / 16)) / (4 * Real.pi ^ 2))
    (hnear : near ≤ 4 * Real.sqrt (A * D))
    (hfar : far ≤ 2 * D / ((256 * (Kphi + 1) + 64) / (η' ^ 2 * H)))
    (hE : E ≤ 3 / 2 * (η' * H / 16) + 3) :
    (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * near + (H + 1) * far + 2 * E
      < η' * H := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hηHpos : 0 < η' * H := mul_pos hη hHpos
  have hK1 : 0 < Kphi + 1 := by linarith
  have hσpos : 0 < Real.sqrt (Kphi + 1) := Real.sqrt_pos.mpr hK1
  have hCxpos : 0 < 256 * (Kphi + 1) + 64 := by linarith
  have hπ2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hHne : H ≠ 0 := ne_of_gt hHpos
  have hηne : η' ≠ 0 := ne_of_gt hη
  -- Step 1: A * D ≤ 3 * (Kphi/η')
  have hAub : A ≤ 49 / 16 * H := by nlinarith [hA, hη1, hH, hη]
  have h2D : D = 8 * Kphi / (Real.pi ^ 2 * η' * H) := by rw [hD]; ring_nf
  have hAD : A * D ≤ 3 * (Kphi / η') := by
    have h1 : A * D ≤ (49 / 16 * H) * (8 * Kphi / (Real.pi ^ 2 * η' * H)) := by
      rw [h2D]
      exact mul_le_mul_of_nonneg_right hAub (by positivity)
    have h4 : (49 / 2) / Real.pi ^ 2 ≤ 3 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hπ2]
    calc A * D ≤ (49 / 16 * H) * (8 * Kphi / (Real.pi ^ 2 * η' * H)) := h1
      _ = ((49 / 2) / Real.pi ^ 2) * (Kphi / η') := by field_simp; ring
      _ ≤ 3 * (Kphi / η') := mul_le_mul_of_nonneg_right h4 (div_nonneg hK hη.le)
  have hsqrtAD : Real.sqrt (A * D) ≤ 2 * Real.sqrt (Kphi / η') := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h2 : (2 * Real.sqrt (Kphi / η')) ^ 2 = 4 * (Kphi / η') := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hK hη.le)]
      norm_num
    rw [h2]
    linarith [hAD, div_nonneg hK hη.le]
  have hnear' : near ≤ 8 * Real.sqrt (Kphi / η') := by linarith
  -- Step 2: key square-root inequality
  have hkey : 32 * η' ^ 3 * Real.sqrt (Kphi / η') ≤ 1000 * Real.sqrt (Kphi + 1) := by
    have h1 : 32 * η' ^ 3 * Real.sqrt (Kphi / η')
        = Real.sqrt ((32 * η' ^ 3) ^ 2 * (Kphi / η')) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : 1000 * Real.sqrt (Kphi + 1) = Real.sqrt ((1000 : ℝ) ^ 2 * (Kphi + 1)) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h1, h2]
    apply Real.sqrt_le_sqrt
    have h3 : (32 * η' ^ 3) ^ 2 * (Kphi / η') = 1024 * η' ^ 5 * Kphi := by
      field_simp
      ring
    rw [h3]
    have hp2 : η' ^ 2 ≤ 1 := by nlinarith [hη1, hη, sq_nonneg η']
    have hp3 : η' ^ 3 ≤ 1 := by nlinarith [hη1, hη, hp2, sq_nonneg η']
    have hp5 : η' ^ 5 ≤ 1 := by
      calc η' ^ 5 = η' ^ 3 * η' ^ 2 := by ring
        _ ≤ 1 * 1 := mul_le_mul hp3 hp2 (by positivity) (by norm_num)
        _ = 1 := by ring
    have h4 : 1024 * η' ^ 5 * Kphi ≤ 1024 * Kphi := by nlinarith [hp5, hK]
    nlinarith [h4, hK]
  -- Term 1
  have ht1 : (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * near ≤ η' * H / 4 := by
    have hcoef : 0 ≤ (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H :=
      mul_nonneg (mul_nonneg (div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) hσpos)))
        (pow_nonneg hη.le 4)) hHpos.le
    calc (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * near
        ≤ (1 / (1000 * Real.sqrt (Kphi + 1))) * η' ^ 4 * H * (8 * Real.sqrt (Kphi / η')) :=
          mul_le_mul_of_nonneg_left hnear' hcoef
      _ = η' * H * (8 * η' ^ 3 * Real.sqrt (Kphi / η') / (1000 * Real.sqrt (Kphi + 1))) := by
          ring_nf
      _ ≤ η' * H * (1 / 4) := by
          refine mul_le_mul_of_nonneg_left ?_ hηHpos.le
          rw [div_le_iff₀ (by positivity)]
          linarith [hkey]
      _ = η' * H / 4 := by ring
  -- Term 2
  have ht2 : (H + 1) * far ≤ η' * H / 4 := by
    have hfarC : far ≤ 2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64) := by
      have hEq : 2 * D / ((256 * (Kphi + 1) + 64) / (η' ^ 2 * H))
          = 2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64) := by
        field_simp
      rw [← hEq]
      exact hfar
    have h1 : (H + 1) * far ≤ (H + 1) * (2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64)) :=
      mul_le_mul_of_nonneg_left hfarC (by linarith)
    have h2 : (H + 1) * (2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64)) ≤ η' * H / 4 := by
      rw [show (H + 1) * (2 * D * η' ^ 2 * H / (256 * (Kphi + 1) + 64))
          = (H + 1) * (2 * D * η' ^ 2 * H) / (256 * (Kphi + 1) + 64) from by ring,
        div_le_iff₀ hCxpos]
      have heq : (H + 1) * (2 * D * η' ^ 2 * H)
          = 16 * (H + 1) * Kphi * η' / Real.pi ^ 2 := by
        rw [hD]; field_simp; ring
      rw [heq]
      have hratio : 16 * (H + 1) / Real.pi ^ 2 ≤ 64 * H := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
        nlinarith [hπ2, hH]
      calc 16 * (H + 1) * Kphi * η' / Real.pi ^ 2
          = (16 * (H + 1) / Real.pi ^ 2) * (Kphi * η') := by ring
        _ ≤ (64 * H) * (Kphi * η') := mul_le_mul_of_nonneg_right hratio (by positivity)
        _ ≤ η' * H / 4 * (256 * (Kphi + 1) + 64) := by nlinarith [hηHpos, hK]
    linarith
  -- Term 3
  have ht3 : 2 * E ≤ η' * H / 4 := by nlinarith [hE, hηH]
  linarith [ht1, ht2, ht3, hηHpos]

end Work.BMF
