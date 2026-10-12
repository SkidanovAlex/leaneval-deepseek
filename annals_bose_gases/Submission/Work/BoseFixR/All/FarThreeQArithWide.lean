import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.All.FarThreeQArithV2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.All

open scoped Real Topology BigOperators

set_option exponentiation.threshold 400
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The arithmetic core -/

/-- **The core arithmetic** of the three-slot far bound with the crude row constant `10 ^ 6·a·ℓ³`.  With the monomial data
of the honest family (`X = (μa³)^{1/323}`, `ℓ = X^{-3/2}(μa)^{-1/2}`, `M = X^{-327/4}`,
`K_H = X^{-549/4}`, `ℓ·K_L·√(μa) = X^{-12}`) the three slot constants sum to at most
`ErrRes/4`. -/
theorem FarThreeQCoreWide {a μ ρ X ℓ M KH KL : ℝ}
    (ha : 0 < a) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (hℓ0 : 0 < ℓ) (hM0 : 0 < M)
    (hℓ : ℓ = X ^ (-(3 / 2 : ℝ)) * (μ * a) ^ (-(1 / 2 : ℝ)))
    (hM : M = X ^ (-(327 / 4 : ℝ)))
    (hKH : KH = X ^ (-(549 / 4 : ℝ)))
    (hDil : μ * a ^ 3 = X ^ 323)
    (hQ : ℓ * KL * Real.sqrt (μ * a) = X ^ (-(12 : ℝ))) :
    320 * Real.pi * a * ρ * Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M
      + 512 * Real.pi * ρ * a * M
      + (2 / Real.sqrt (M / ((ρ + μ) * ℓ ^ 3))) * (ρ / ℓ ^ 3)
        * (10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3
              * (2000 * (16 * Real.pi * a * (2 * KH * a)) ^ 2 * M ^ 2)
          + 2000 * (10 ^ 6 * a * ℓ ^ 3) * M)
      ≤ 10 ^ 300 * ((ρ + μ) * a * M + (ρ + μ) ^ (3 / 2 : ℝ) * a * Real.sqrt (ℓ ^ 3 * M)) / 4 := by
  have ha0 : 0 ≤ a := ha.le
  have hℓnn : 0 ≤ ℓ := hℓ0.le
  have hMnn : 0 ≤ M := hM0.le
  have hℓ3 : 0 ≤ ℓ ^ 3 := by positivity
  have hμa0 : 0 ≤ μ * a := (mul_pos hμ ha).le
  set R := ρ + μ with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hRnn : 0 ≤ R := hR0.le
  have hρR : ρ ≤ R := by rw [hRdef]; linarith
  have hRℓ3 : 0 ≤ R * ℓ ^ 3 := mul_nonneg hRnn hℓ3
  have hRpow : R ^ (3 / 2 : ℝ) = R * Real.sqrt R := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hR0, Real.rpow_one, Real.sqrt_eq_rpow]
  set A1 := R * a * M with hA1def
  set A2 := R ^ (3 / 2 : ℝ) * a * Real.sqrt (ℓ ^ 3 * M) with hA2def
  have hA1nn : 0 ≤ A1 := by rw [hA1def]; positivity
  have hA2nn : 0 ≤ A2 := by rw [hA2def]; positivity
  -- `A2` in the `R·a·√(Rℓ³M)` form
  have hA2eq : A2 = R * a * Real.sqrt (R * ℓ ^ 3 * M) := by
    rw [hA2def, hRpow]
    have hsq : Real.sqrt R * Real.sqrt (ℓ^3*M) = Real.sqrt (R * (ℓ^3*M)) :=
      (Real.sqrt_mul hRnn (ℓ^3*M)).symm
    rw [show R * Real.sqrt R * a * Real.sqrt (ℓ^3*M)
        = R * a * (Real.sqrt R * Real.sqrt (ℓ^3*M)) by ring]
    rw [hsq]
    congr 1
    ring_nf
  have hγ : M / Real.sqrt (M / (R * ℓ ^ 3)) = Real.sqrt (M * (R * ℓ ^ 3)) :=
    div_sqrt_div_eq M (R * ℓ^3) hMnn hRℓ3
  have hγ2 : 1 / Real.sqrt (M / (R * ℓ ^ 3)) = Real.sqrt (M * (R * ℓ ^ 3)) / M := by
    have hγM : (1 / Real.sqrt (M / (R * ℓ^3))) * M = Real.sqrt (M * (R * ℓ^3)) := by
      rw [one_div, inv_mul_eq_div]
      exact hγ
    rw [eq_div_iff (ne_of_gt hM0)]
    exact hγM
  have hxy : Real.sqrt (M / (R * ℓ^3)) * Real.sqrt (M * (R * ℓ^3)) = M := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ M / (R*ℓ^3)),
        show M / (R*ℓ^3) * (M * (R*ℓ^3)) = M * M by field_simp <;> ring]
    exact Real.sqrt_mul_self hMnn
  have hx0 : 0 < Real.sqrt (M / (R * ℓ^3)) := Real.sqrt_pos.mpr (div_pos hM0 (by positivity))
  -- ## Slot 1: the linear word
  have hT1 : 320 * Real.pi * a * ρ * Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M ≤ 320 * Real.pi * A2 := by
    rw [hA2eq]
    rw [show 320 * Real.pi * a * ρ * Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M
        = 320 * Real.pi * a * ρ * (Real.sqrt (ρ * ℓ ^ 3) * Real.sqrt M) by ring]
    rw [show Real.sqrt (ρ * ℓ^3) * Real.sqrt M = Real.sqrt (ρ * (ℓ^3*M)) by
      rw [show ρ * (ℓ^3*M) = ρ * ℓ^3 * M by ring, ← Real.sqrt_mul (mul_nonneg hρ hℓ3) M]]
    rw [show R * ℓ^3 * M = R * (ℓ^3*M) by ring]
    have hkey : ρ * Real.sqrt (ρ * (ℓ^3*M)) ≤ R * Real.sqrt (R * (ℓ^3*M)) :=
      sqrt_ratio_le ρ (ℓ^3*M) R hρ hρR (mul_nonneg hℓ3 hMnn)
    have h320 : (0:ℝ) ≤ 320 * Real.pi * a := by positivity
    calc 320 * Real.pi * a * ρ * Real.sqrt (ρ * (ℓ^3*M))
        = (320 * Real.pi * a) * (ρ * Real.sqrt (ρ * (ℓ^3*M))) := by ring
      _ ≤ (320 * Real.pi * a) * (R * Real.sqrt (R * (ℓ^3*M))) :=
          mul_le_mul_of_nonneg_left hkey h320
      _ = 320 * Real.pi * (R * a * Real.sqrt (R * (ℓ^3*M))) := by ring
  -- ## Slot 2: the pairing word
  have hT2 : 512 * Real.pi * ρ * a * M ≤ 512 * Real.pi * A1 := by
    rw [hA1def]
    calc 512 * Real.pi * ρ * a * M = (512 * Real.pi * a * M) * ρ := by ring
      _ ≤ (512 * Real.pi * a * M) * R := mul_le_mul_of_nonneg_left hρR (by positivity)
      _ = 512 * Real.pi * (R * a * M) := by ring
  -- ## Slot 3, `Row` half
  have hT3B : (2 / Real.sqrt (M / (R * ℓ ^ 3))) * (ρ / ℓ ^ 3) * (2000 * (10 ^ 6 * a * ℓ ^ 3) * M)
      ≤ 4000 * 10 ^ 6 * A2 := by
    have hone : (ρ / ℓ ^ 3) * ℓ ^ 3 = ρ := by field_simp
    have hstep : (2 / Real.sqrt (M / (R * ℓ ^ 3))) * (ρ / ℓ ^ 3) * (2000 * (10 ^ 6 * a * ℓ ^ 3) * M)
        = 2 * 2000 * 10 ^ 6 * a * ρ * (M / Real.sqrt (M / (R * ℓ^3))) := by
      calc (2 / Real.sqrt (M / (R * ℓ ^ 3))) * (ρ / ℓ ^ 3) * (2000 * (10 ^ 6 * a * ℓ ^ 3) * M)
          = (2 * 2000 * 10 ^ 6 * a) * ((ρ / ℓ ^ 3) * ℓ ^ 3)
              * (M / Real.sqrt (M / (R * ℓ^3))) := by ring
        _ = (2 * 2000 * 10 ^ 6 * a) * ρ * (M / Real.sqrt (M / (R * ℓ^3))) := by rw [hone]
        _ = 2 * 2000 * 10 ^ 6 * a * ρ * (M / Real.sqrt (M / (R * ℓ^3))) := by ring
    rw [hstep, hγ]
    rw [show Real.sqrt (M * (R * ℓ^3)) = Real.sqrt (R * ℓ^3 * M) by
      rw [show M * (R * ℓ^3) = R * ℓ^3 * M by ring]]
    rw [hA2eq]
    have hcoef : (0:ℝ) ≤ 2 * 2000 * 10 ^ 6 * a * Real.sqrt (R * ℓ^3 * M) := by positivity
    calc 2 * 2000 * 10 ^ 6 * a * ρ * Real.sqrt (R * ℓ^3 * M)
        = (2 * 2000 * 10 ^ 6 * a * Real.sqrt (R * ℓ^3 * M)) * ρ := by ring
      _ ≤ (2 * 2000 * 10 ^ 6 * a * Real.sqrt (R * ℓ^3 * M)) * R :=
          mul_le_mul_of_nonneg_left hρR hcoef
      _ = 4000 * 10 ^ 6 * (R * a * Real.sqrt (R * ℓ^3 * M)) := by ring
  -- ## Slot 3, the `f_L`-count half
  have hX12 : (1:ℝ) ≤ X ^ (-(12):ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (show (-(12):ℝ) ≤ 0 by norm_num)
    simpa using h
  have hC0 : (0:ℝ) ≤ 10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3 := by
    rw [hQ]
    have h := Real.rpow_nonneg hX0.le (-(12):ℝ)
    positivity
  have hCf_le : 10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3 ≤ 8 * 10 ^ 6 * X ^ (-(36):ℝ) := by
    rw [hQ]
    have h2 : X ^ (-(12):ℝ) + 1 ≤ 2 * X ^ (-(12):ℝ) := by linarith
    have h3 : (X ^ (-(12):ℝ) + 1) ^ 3 ≤ (2 * X ^ (-(12):ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) h2 3
    have h4 : (2 * X ^ (-(12):ℝ)) ^ 3 = 8 * X ^ (-(36):ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (X ^ (-(12):ℝ)) 3, ← Real.rpow_mul hX0.le]
      norm_num
    calc 10 ^ 6 * (X ^ (-(12):ℝ) + 1) ^ 3 ≤ 10 ^ 6 * (2 * X ^ (-(12):ℝ)) ^ 3 :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 8 * 10 ^ 6 * X ^ (-(36):ℝ) := by rw [h4]; ring
  have hKH2 : KH ^ 2 = X ^ (-(549/2):ℝ) := by
    rw [hKH, ← Real.rpow_natCast (X ^ (-(549/4):ℝ)) 2, ← Real.rpow_mul hX0.le]
    norm_num
  have hA1' : (X ^ 323) ^ (3/2:ℝ) = X ^ (969/2:ℝ) := by
    rw [← Real.rpow_natCast X 323, ← Real.rpow_mul hX0.le]
    norm_num
  have hA3 : a ^ 3 * (μ * a) ^ (3/2:ℝ) = (μ * a ^ 3) ^ (3/2:ℝ) := by
    rw [Real.mul_rpow hμ.le ha.le, Real.mul_rpow hμ.le (by positivity : (0:ℝ) ≤ a^3)]
    rw [show a ^ 3 * (μ ^ (3/2:ℝ) * a ^ (3/2:ℝ)) = μ ^ (3/2:ℝ) * (a ^ 3 * a ^ (3/2:ℝ)) by ring]
    rw [← Real.rpow_natCast a 3, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
    norm_num
  have hℓ3v : ℓ ^ 3 = X ^ (-(9/2):ℝ) * (μ * a) ^ (-(3/2):ℝ) := by
    rw [hℓ, mul_pow, ← Real.rpow_natCast (X ^ (-(3/2:ℝ))) 3, ← Real.rpow_mul hX0.le,
        ← Real.rpow_natCast ((μ * a) ^ (-(1/2:ℝ))) 3, ← Real.rpow_mul hμa0]
    norm_num
  have hAM : a ^ 3 * M / ℓ ^ 3 = X ^ (1629/4:ℝ) := by
    rw [hℓ3v, hM, div_eq_mul_inv, mul_inv, ← Real.rpow_neg hX0.le, ← Real.rpow_neg hμa0]
    simp only [neg_neg]
    rw [show a ^ 3 * X ^ (-(327/4):ℝ) * (X ^ (9/2:ℝ) * (μ * a) ^ (3/2:ℝ))
        = X ^ (-(327/4):ℝ) * X ^ (9/2:ℝ) * (a ^ 3 * (μ * a) ^ (3/2:ℝ)) by ring]
    rw [hA3, hDil, hA1']
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    norm_num
  have hAM0 : (0:ℝ) ≤ a ^ 3 * M / ℓ ^ 3 := by rw [hAM]; exact Real.rpow_nonneg hX0.le _
  have hCfKH : 10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3 * KH ^ 2 * (a ^ 3 * M / ℓ ^ 3) ≤ 8 * 10 ^ 6 := by
    have hcomb : X ^ (-(36):ℝ) * X ^ (531/4:ℝ) = X ^ (387/4:ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have h531 : X ^ (-(549/2):ℝ) * X ^ (1629/4:ℝ) = X ^ (531/4:ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    calc 10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3 * KH ^ 2 * (a ^ 3 * M / ℓ ^ 3)
        = (10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3)
            * (X ^ (-(549/2):ℝ) * X ^ (1629/4:ℝ)) := by rw [hKH2, hAM]; ring
      _ = (10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3) * X ^ (531/4:ℝ) := by rw [h531]
      _ ≤ (8 * 10 ^ 6 * X ^ (-(36):ℝ)) * X ^ (531/4:ℝ) :=
          mul_le_mul_of_nonneg_right hCf_le (Real.rpow_nonneg hX0.le _)
      _ = 8 * 10 ^ 6 * X ^ (387/4:ℝ) := by rw [mul_assoc, hcomb]
      _ ≤ 8 * 10 ^ 6 := by
          have h2 : X ^ (387/4:ℝ) ≤ 1 := Real.rpow_le_one hX0.le hX1 (by norm_num)
          nlinarith [h2]
  have hT3A : (2 / Real.sqrt (M / (R * ℓ ^ 3))) * (ρ / ℓ ^ 3)
        * (10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3
              * (2000 * (16 * Real.pi * a * (2 * KH * a)) ^ 2 * M ^ 2))
      ≤ (10 ^ 300 / 8) * A2 := by
    rw [farT3A_factor (a := a) (ρ := ρ) (ℓ := ℓ) (M := M) (KH := KH)
      (C := 10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3)
      (x := Real.sqrt (M / (R * ℓ^3))) (y := Real.sqrt (M * (R * ℓ^3))) hx0 hM0 hℓ0 hxy]
    rw [show Real.sqrt (M * (R * ℓ^3)) = Real.sqrt (R * ℓ^3 * M) by
      rw [show M * (R * ℓ^3) = R * ℓ^3 * M by ring]]
    rw [hA2eq]
    have h1 : ρ * ((10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3) * KH ^ 2 * (a ^ 3 * M / ℓ ^ 3))
        ≤ R * (8 * 10 ^ 6) := by
      calc ρ * ((10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3) * KH ^ 2 * (a ^ 3 * M / ℓ ^ 3))
          ≤ R * ((10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3) * KH ^ 2 * (a ^ 3 * M / ℓ ^ 3)) :=
            mul_le_mul_of_nonneg_right hρR (mul_nonneg (mul_nonneg hC0 (sq_nonneg KH)) hAM0)
        _ ≤ R * (8 * 10 ^ 6) := mul_le_mul_of_nonneg_left hCfKH hRnn
    have hc : 2 * 2000 * 1024 * Real.pi ^ 2 * 8 * 10 ^ 6 ≤ (10:ℝ) ^ 300 / 8 := by
      have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
      have hC : (0:ℝ) ≤ 2 * 2000 * 1024 * 8 * 10 ^ 6 := by norm_num
      calc 2 * 2000 * 1024 * Real.pi ^ 2 * 8 * 10 ^ 6
          = Real.pi ^ 2 * (2 * 2000 * 1024 * 8 * 10 ^ 6) := by ring
        _ ≤ 16 * (2 * 2000 * 1024 * 8 * 10 ^ 6) := mul_le_mul_of_nonneg_right hpi2 hC
        _ ≤ (10:ℝ) ^ 300 / 8 := by norm_num
    calc 2 * ρ * a * (2000 * 1024 * Real.pi ^ 2)
            * ((10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3) * KH ^ 2 * (a ^ 3 * M / ℓ ^ 3))
            * Real.sqrt (R * ℓ ^ 3 * M)
        = (2 * a * (2000 * 1024 * Real.pi ^ 2) * Real.sqrt (R * ℓ^3 * M))
            * (ρ * ((10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3) * KH ^ 2 * (a ^ 3 * M / ℓ ^ 3))) := by
          ring
      _ ≤ (2 * a * (2000 * 1024 * Real.pi ^ 2) * Real.sqrt (R * ℓ^3 * M)) * (R * (8 * 10 ^ 6)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 * 2000 * 1024 * Real.pi ^ 2 * 8 * 10 ^ 6) * (R * a * Real.sqrt (R * ℓ^3 * M)) := by ring
      _ ≤ ((10:ℝ) ^ 300 / 8) * (R * a * Real.sqrt (R * ℓ ^ 3 * M)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
  -- ## Assembly
  have hsplit : (2 / Real.sqrt (M / (R * ℓ ^ 3))) * (ρ / ℓ ^ 3)
        * (10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3
              * (2000 * (16 * Real.pi * a * (2 * KH * a)) ^ 2 * M ^ 2)
          + 2000 * (10 ^ 6 * a * ℓ ^ 3) * M)
      = (2 / Real.sqrt (M / (R * ℓ ^ 3))) * (ρ / ℓ ^ 3)
              * (10 ^ 6 * (ℓ * KL * Real.sqrt (μ * a) + 1) ^ 3
                  * (2000 * (16 * Real.pi * a * (2 * KH * a)) ^ 2 * M ^ 2))
        + (2 / Real.sqrt (M / (R * ℓ ^ 3))) * (ρ / ℓ ^ 3)
            * (2000 * (10 ^ 6 * a * ℓ ^ 3) * M) := by
    ring
  rw [hsplit]
  have hC1 : 512 * Real.pi ≤ (10:ℝ) ^ 300 / 4 := by
    have hpi := Real.pi_lt_four
    have h1 : 512 * Real.pi ≤ 512 * 4 := by linarith
    have h2 : (512 * 4 : ℝ) ≤ (10:ℝ) ^ 300 / 4 := by norm_num
    linarith
  have hC2 : 320 * Real.pi + (10:ℝ) ^ 300 / 8 + 4000 * 10 ^ 6 ≤ (10:ℝ) ^ 300 / 4 := by
    have hpi := Real.pi_lt_four
    have h1 : 320 * Real.pi + 4000 * 10 ^ 6 ≤ 320 * 4 + 4000 * 10 ^ 6 := by linarith
    have h2 : (320 * 4 + 4000 * 10 ^ 6 : ℝ) + (10:ℝ) ^ 300 / 8 ≤ (10:ℝ) ^ 300 / 4 := by norm_num
    linarith
  have hfin : 320 * Real.pi * A2 + 512 * Real.pi * A1 + ((10:ℝ) ^ 300 / 8) * A2
        + 4000 * 10 ^ 6 * A2
      ≤ (10:ℝ) ^ 300 / 4 * A1 + (10:ℝ) ^ 300 / 4 * A2 := by
    have h1 : 320 * Real.pi * A2 + ((10:ℝ) ^ 300 / 8) * A2 + 4000 * 10 ^ 6 * A2
        ≤ (10:ℝ) ^ 300 / 4 * A2 := by
      calc 320 * Real.pi * A2 + ((10:ℝ) ^ 300 / 8) * A2 + 4000 * 10 ^ 6 * A2
          = (320 * Real.pi + (10:ℝ) ^ 300 / 8 + 4000 * 10 ^ 6) * A2 := by ring
        _ ≤ ((10:ℝ) ^ 300 / 4) * A2 := mul_le_mul_of_nonneg_right hC2 hA2nn
    have h2 : 512 * Real.pi * A1 ≤ (10:ℝ) ^ 300 / 4 * A1 :=
      mul_le_mul_of_nonneg_right hC1 hA1nn
    linarith [h1, h2]
  linarith [hT1, hT2, hT3A, hT3B, hfin]

/-! ## The honest-family instantiation -/

theorem FarThreeQArithWide {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hfar : Work.BoseBoxFock.FarCondFS v μ ρ) :
    320 * Real.pi * BoseGases.a v * ρ * Real.sqrt (ρ * (Work.BoseFixR.ell v μ) ^ 3)
        * Real.sqrt ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
      + 512 * Real.pi * ρ * BoseGases.a v
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM
      + 2 / Work.BoseFixR.All.epsFar v μ ρ * (ρ / (Work.BoseFixR.ell v μ) ^ 3)
        * (10 ^ 6
              * (Work.BoseFixR.ell v μ
                  * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
                  * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3
            * (2000 * (16 * Real.pi * BoseGases.a v
                * (2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v)) ^ 2
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM ^ 2)
          + 2000 * (10 ^ 6 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3)
            * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM)
      ≤ Work.BoseFixR.ErrRes v μ ρ / 4 := by
  obtain ⟨hg0, hmu, hell, hbigM, hbpos, hMnnE, hW1ω0nn, hellpos, hdpos, heTnn⟩ :=
    Work.BoseFixR.All.honest_view_basics hview
  unfold Work.BoseFixR.KzDatum.viewFSAll Work.BoseBoxFock.RViewFSAll at hview
  obtain ⟨hFSP, -, haSc, -⟩ := hview
  have hvE : Work.BoseB7.FSParamsView (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E :=
    Classical.choice hFSP
  have hμ : 0 < μ := hAdm.1
  have ht_dil : hvE.t = Work.BoseFixR.dil v μ := by
    rw [← hvE.mu_eq, hmu, haSc, Work.BoseFixR.dil]
  have ht_le : Work.BoseFixR.dil v μ ≤ 1 := by
    rw [Work.BoseFixR.dil]
    have h1 : μ * BoseGases.a v ^ 3 ≤ ε₀ := hAdm.2.1
    have h2 : ε₀ ≤ (10:ℝ) ^ (-(4000 : ℤ)) := hε₀
    have h3 : (10:ℝ) ^ (-(4000 : ℤ)) ≤ 1 := by
      rw [zpow_neg]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 10))
    linarith
  have ht0 : 0 < Work.BoseFixR.dil v μ := by rw [Work.BoseFixR.dil]; positivity
  have hX0 : 0 < Work.BoseFixR.fsX v μ := by
    rw [Work.BoseFixR.fsX]; exact Work.BoseBox.fsXp_pos ht0
  have hX1 : Work.BoseFixR.fsX v μ ≤ 1 := by
    rw [Work.BoseFixR.fsX]; exact Work.BoseBox.fsXp_le_one ht0 ht_le (by norm_num)
  have hfsX : ∀ c : ℝ, Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) c
      = (Work.BoseFixR.fsX v μ) ^ c := by
    intro c
    rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp_rpow (le_of_lt ht0) 1 c, one_mul]
  have hDil : μ * BoseGases.a v ^ 3 = (Work.BoseFixR.fsX v μ) ^ 323 := by
    have h1 : Work.BoseFixR.fsX v μ ^ 323
        = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) ((323:ℕ) : ℝ) := by
      rw [Work.BoseFixR.fsX, ← Real.rpow_natCast (Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1) 323,
          Work.BoseBox.fsXp_rpow (le_of_lt ht0) 1 ((323:ℕ) : ℝ)]
      norm_num
    rw [h1, show ((323:ℕ):ℝ) = (323:ℝ) by norm_num,
        ← Work.BoseBox.delta_eq_fsXp (le_of_lt ht0), Work.BoseFixR.dil]
  have hKl : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.Kl
      = (Work.BoseFixR.fsX v μ) ^ (-(3/2:ℝ)) := by
    rw [Work.BoseB7.Kl_val _ hvE, ht_dil]; exact hfsX _
  have hKL : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
      = (Work.BoseFixR.fsX v μ) ^ (-(21/2:ℝ)) := by
    rw [Work.BoseB7.KL_val _ hvE, ht_dil]; exact hfsX _
  have hKH : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH
      = (Work.BoseFixR.fsX v μ) ^ (-(549/4:ℝ)) := by
    rw [Work.BoseB7.KH_val _ hvE, ht_dil]; exact hfsX _
  have hEbigM : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM
      = (Work.BoseFixR.fsX v μ) ^ (-(327/4:ℝ)) := by
    rw [Work.BoseB7.bigM_val _ hvE, ht_dil]; exact hfsX _
  have hM : Work.BoseFixR.bigMV v μ = (Work.BoseFixR.fsX v μ) ^ (-(327/4:ℝ)) := by
    rw [← hbigM]; exact hEbigM
  have hKlT : (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
      = (Work.BoseFixR.fsX v μ) ^ (-(3/2:ℝ)) := by
    show Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-(3/2:ℝ)) = _
    rw [show μ * BoseGases.a v ^ 3 = Work.BoseFixR.dil v μ by rw [Work.BoseFixR.dil]]
    exact hfsX _
  have hℓ : Work.BoseFixR.ell v μ
      = (Work.BoseFixR.fsX v μ) ^ (-(3/2:ℝ)) * (μ * BoseGases.a v) ^ (-(1/2:ℝ)) := by
    rw [Work.BoseFixR.ell, Work.BoseBox.sideAt, Work.BoseBox.boxSide, hKlT]
  have hQ : Work.BoseFixR.ell v μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
      * Real.sqrt (μ * BoseGases.a v) = (Work.BoseFixR.fsX v μ) ^ (-(12:ℝ)) := by
    have h1 := Work.BoseK15.ell_mul_KL_sqrt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E hvE
    rw [hell, hmu, haSc] at h1
    rw [h1, hKl, hKL, ← Real.rpow_add hX0]
    norm_num
  have hMpos : 0 < Work.BoseFixR.bigMV v μ := by rw [hM]; exact Real.rpow_pos_of_pos hX0 _
  have hellpos' : 0 < Work.BoseFixR.ell v μ := by rw [← hell]; exact hellpos
  rw [hbigM, Work.BoseFixR.All.epsFar, Work.BoseFixR.ErrRes]
  exact FarThreeQCoreWide (a := BoseGases.a v) (μ := μ) (ρ := ρ) (X := Work.BoseFixR.fsX v μ)
    (ℓ := Work.BoseFixR.ell v μ) (M := Work.BoseFixR.bigMV v μ)
    (KH := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH)
    (KL := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL)
    hav hμ hρ hX0 hX1 hellpos' hMpos hℓ hM hKH hDil hQ


end Work.BoseFixR.All
