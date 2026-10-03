import Mathlib

namespace Work.FIArea4

set_option maxHeartbeats 2000000 in
lemma flat_numeric (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    ((10 * (R * (2 * S + 2) / D + 4 * min R S + 1) : ℕ) : ℝ) * Real.sqrt (2 * D)
      ≤ 200 * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
          + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) := by
  have hDℝ1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDℝ0 : (0 : ℝ) < (D : ℝ) := by linarith
  have hRℝ1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hSℝ1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hLcast : ((10 * (R * (2 * S + 2) / D + 4 * min R S + 1) : ℕ) : ℝ)
      = 10 * (((R * (2 * S + 2) / D : ℕ) : ℝ) + 4 * ((min R S : ℕ) : ℝ) + 1) := by
    push_cast; ring
  have hsqrt2D : Real.sqrt ((2 : ℝ) * (D : ℝ)) = Real.sqrt 2 * Real.sqrt (D : ℝ) :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (D : ℝ)
  have hsqrtRS : Real.sqrt ((R : ℝ) * (S : ℝ))
      = Real.sqrt (R : ℝ) * Real.sqrt (S : ℝ) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (R : ℝ)) (S : ℝ)
  rw [hLcast, hsqrt2D, hsqrtRS]
  set A : ℝ := ((R * (2 * S + 2) / D : ℕ) : ℝ) with hAdef
  set m : ℝ := ((min R S : ℕ) : ℝ) with hmdef
  set s : ℝ := Real.sqrt (D : ℝ) with hsdef
  set P : ℝ := Real.sqrt (R : ℝ) * Real.sqrt (S : ℝ) with hPdef
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hDℝ0
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr hDℝ1
  have hssq : s ^ 2 = (D : ℝ) := by rw [hsdef]; exact Real.sq_sqrt hDℝ0.le
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hm0 : 0 ≤ m := by rw [hmdef]; positivity
  have hPn : 0 ≤ P := by rw [hPdef]; positivity
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    have h1 : (1 : ℝ) ≤ Real.sqrt (R : ℝ) := Real.one_le_sqrt.mpr hRℝ1
    have h2 : (1 : ℝ) ≤ Real.sqrt (S : ℝ) := Real.one_le_sqrt.mpr hSℝ1
    nlinarith [h1, h2]
  have hmP : m ≤ P := by
    rw [hmdef, hPdef]
    have hml : ((min R S : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast min_le_left R S
    have hms : ((min R S : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast min_le_right R S
    have h0 : (0 : ℝ) ≤ ((min R S : ℕ) : ℝ) := by positivity
    have h1 : ((min R S : ℕ) : ℝ) * ((min R S : ℕ) : ℝ)
        ≤ ((min R S : ℕ) : ℝ) * (R : ℝ) := mul_le_mul_of_nonneg_left hml h0
    have h2 : ((min R S : ℕ) : ℝ) * (R : ℝ) ≤ (S : ℝ) * (R : ℝ) :=
      mul_le_mul_of_nonneg_right hms (by linarith [hRℝ1])
    have hsq : ((min R S : ℕ) : ℝ) ^ 2 ≤ (R : ℝ) * (S : ℝ) := by nlinarith [h1, h2]
    have hle : ((min R S : ℕ) : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) :=
      Real.le_sqrt_of_sq_le hsq
    rwa [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (R : ℝ)) (S : ℝ)] at hle
  have hdiv : A ≤ 4 * ((R : ℝ) * (S : ℝ)) / (D : ℝ) := by
    rw [hAdef]
    have h1 : ((R * (2 * S + 2) / D : ℕ) : ℝ) ≤ ((R * (2 * S + 2) : ℕ) : ℝ) / (D : ℝ) :=
      Nat.cast_div_le
    have h2 : ((R * (2 * S + 2) : ℕ) : ℝ) = (R : ℝ) * (2 * (S : ℝ) + 2) := by
      push_cast; ring
    calc ((R * (2 * S + 2) / D : ℕ) : ℝ)
        ≤ ((R * (2 * S + 2) : ℕ) : ℝ) / (D : ℝ) := h1
      _ = (R : ℝ) * (2 * (S : ℝ) + 2) / (D : ℝ) := by rw [h2]
      _ ≤ 4 * ((R : ℝ) * (S : ℝ)) / (D : ℝ) := by
          apply div_le_div_of_nonneg_right _ hDℝ0.le
          nlinarith [hRℝ1, hSℝ1]
  have hAD : A * (D : ℝ) ≤ 4 * ((R : ℝ) * (S : ℝ)) := (le_div_iff₀ hDℝ0).mp hdiv
  have h2sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h80 : 40 * Real.sqrt 2 ≤ 80 := by nlinarith [h2sq, h2n]
  have h15 : 10 * Real.sqrt 2 ≤ 15 := by nlinarith [h2sq, h2n]
  have hRS1 : 1 ≤ (R : ℝ) * (S : ℝ) := by nlinarith [hRℝ1, hSℝ1]
  have hRSn : 0 ≤ (R : ℝ) * (S : ℝ) := by linarith
  have hDn : 0 ≤ (D : ℝ) := hDℝ0.le
  have hcore : 10 * Real.sqrt 2 * (A * (D : ℝ) + 4 * m * (D : ℝ) + (D : ℝ))
      ≤ 200 * ((R : ℝ) * (S : ℝ) + (D : ℝ) * P * s) := by
    have hA1 : 10 * Real.sqrt 2 * (A * (D : ℝ)) ≤ 200 * ((R : ℝ) * (S : ℝ)) := by
      have h1 : 10 * Real.sqrt 2 * (A * (D : ℝ))
          ≤ 10 * Real.sqrt 2 * (4 * ((R : ℝ) * (S : ℝ))) :=
        mul_le_mul_of_nonneg_left hAD (by positivity)
      have h2 : 10 * Real.sqrt 2 * (4 * ((R : ℝ) * (S : ℝ)))
          ≤ 80 * ((R : ℝ) * (S : ℝ)) := by
        have h40 : 40 * Real.sqrt 2 * ((R : ℝ) * (S : ℝ)) ≤ 80 * ((R : ℝ) * (S : ℝ)) :=
          mul_le_mul_of_nonneg_right h80 hRSn
        linarith [h40]
      have h3 : 80 * ((R : ℝ) * (S : ℝ)) ≤ 200 * ((R : ℝ) * (S : ℝ)) := by
        nlinarith [hRSn]
      linarith [h1, h2, h3]
    have hA2 : 10 * Real.sqrt 2 * (4 * m * (D : ℝ) + (D : ℝ)) ≤ 200 * ((D : ℝ) * P * s) := by
      have hPs1 : 1 ≤ P * s := by nlinarith [hP1, hs1]
      have hmD : m * (D : ℝ) ≤ (D : ℝ) * P * s := by
        have h1 : m * (D : ℝ) ≤ P * (D : ℝ) := mul_le_mul_of_nonneg_right hmP hDn
        have h2 : P * (D : ℝ) ≤ P * (D : ℝ) * s := by
          have := mul_le_mul_of_nonneg_left hs1 (show (0 : ℝ) ≤ P * (D : ℝ) by positivity)
          simpa using this
        calc m * (D : ℝ) ≤ P * (D : ℝ) := h1
          _ ≤ P * (D : ℝ) * s := h2
          _ = (D : ℝ) * P * s := by ring
      have hDle : (D : ℝ) ≤ (D : ℝ) * P * s := by
        have h1 : (D : ℝ) ≤ (D : ℝ) * (P * s) := by
          have := mul_le_mul_of_nonneg_left hPs1 (show (0 : ℝ) ≤ (D : ℝ) by positivity)
          simpa using this
        calc (D : ℝ) ≤ (D : ℝ) * (P * s) := h1
          _ = (D : ℝ) * P * s := by ring
      have hkey : 4 * m * (D : ℝ) + (D : ℝ) ≤ 5 * ((D : ℝ) * P * s) := by
        nlinarith [hmD, hDle]
      have hstep1 : 10 * Real.sqrt 2 * (4 * m * (D : ℝ) + (D : ℝ))
          ≤ 15 * (4 * m * (D : ℝ) + (D : ℝ)) :=
        mul_le_mul_of_nonneg_right h15 (by positivity)
      have hstep2 : 15 * (4 * m * (D : ℝ) + (D : ℝ)) ≤ 15 * (5 * ((D : ℝ) * P * s)) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)
      have hnn : 0 ≤ (D : ℝ) * P * s := by positivity
      have hstep3 : 15 * (5 * ((D : ℝ) * P * s)) ≤ 200 * ((D : ℝ) * P * s) := by
        nlinarith [hnn]
      linarith [hstep1, hstep2, hstep3]
    nlinarith [hA1, hA2]
  have heqL : 10 * (A + 4 * m + 1) * (Real.sqrt 2 * s)
      = (10 * Real.sqrt 2 * (A * (D : ℝ) + 4 * m * (D : ℝ) + (D : ℝ))) / s := by
    rw [eq_div_iff (ne_of_gt hs0)]
    linear_combination (10 * Real.sqrt 2 * (A + 4 * m + 1)) * hssq
  have heqR : 200 * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) + (D : ℝ) * P)
      = (200 * ((R : ℝ) * (S : ℝ) + (D : ℝ) * P * s)) / s := by
    have hpow : (D : ℝ) ^ (-(1 : ℝ) / 2) = 1 / s := by
      have h1 : (D : ℝ) ^ (-(1 : ℝ) / 2) = ((D : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
        rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring]
        exact Real.rpow_neg hDℝ0.le ((1 : ℝ) / 2)
      rw [h1, inv_eq_one_div]
      congr 1
      rw [← Real.sqrt_eq_rpow, ← hsdef]
    rw [hpow, eq_div_iff (ne_of_gt hs0)]
    field_simp
  calc 10 * (A + 4 * m + 1) * (Real.sqrt 2 * s)
      = (10 * Real.sqrt 2 * (A * (D : ℝ) + 4 * m * (D : ℝ) + (D : ℝ))) / s := heqL
    _ ≤ (200 * ((R : ℝ) * (S : ℝ) + (D : ℝ) * P * s)) / s :=
        div_le_div_of_nonneg_right hcore hs0.le
    _ = 200 * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) + (D : ℝ) * P) := heqR.symm

end Work.FIArea4
