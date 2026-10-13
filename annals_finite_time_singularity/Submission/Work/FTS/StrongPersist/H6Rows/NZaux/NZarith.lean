import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/NZarith` — the numeric step of the `N`-zero-mode estimate

The final arithmetic of `NZzero6`: the `ℝ`-inequality

`9·Kcoef α M Ce Cs Cp Cu Cag · (6·(√(π/2)·M + Cf·α))
   ≤ K · (1+|Ce|+|Cs|)⁴ · α^{-9} · (1+M)⁴`

with `K := 54000·(Cp+Cu+Cag+Cf+1)·(√(π/2)+Cf+1) + 1`.  It is isolated here (rather than
inlined in `NZzero6`) because the surrounding declaration is heartbeat-limited: this way the
`ring`/`nlinarith` work happens in a small context.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The numeric step of the zero-mode estimate.** -/
theorem NZ_arith {α M Ce Cs Cp Cu Cag Cf : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M) (hCf : 0 < Cf)
    (hCp : 0 < Cp) (hCu : 0 < Cu) (hCag : 0 < Cag) :
    9 * Kcoef α M Ce Cs Cp Cu Cag * (6 * (Real.sqrt (Real.pi / 2) * M + Cf * α))
      ≤ (54000 * (Cp + Cu + Cag + Cf + 1) * (Real.sqrt (Real.pi / 2) + Cf + 1) + 1)
          * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  set X : ℝ := 1 + |Ce| + |Cs| with hX
  set B : ℝ := 1 + M with hB
  set P : ℝ := α ^ (-(9 : ℝ)) with hP
  set Cc : ℝ := Real.sqrt (Real.pi / 2) + Cf + 1 with hCc
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  -- the unfolding of `Kcoef`
  have hK : Kcoef α M Ce Cs Cp Cu Cag = 1000 * (Cp + Cu + Cag + 1) * X * α ^ (-(1 / 2 : ℝ)) * B := by
    rw [Kcoef, hX, hB]
  -- the elementary facts
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX]
    have h1 := abs_nonneg Ce
    have h2 := abs_nonneg Cs
    linarith
  have hX0 : (0 : ℝ) ≤ X := le_trans zero_le_one hX1
  have hB1 : (1 : ℝ) ≤ B := by rw [hB]; linarith
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hP0 : (0 : ℝ) ≤ P := by rw [hP]; exact Real.rpow_nonneg hα0.le _
  have hRP : α ^ (-(1 / 2 : ℝ)) ≤ P := by
    rw [hP]
    exact Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hCc1 : (1 : ℝ) ≤ Cc := by rw [hCc]; linarith [hsqrt0, hCf.le]
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans zero_le_one hCc1
  have hX4 : X ≤ X ^ 4 := by
    have h2 : (1 : ℝ) ≤ X * X := by
      have h := mul_le_mul hX1 hX1 zero_le_one hX0
      linarith
    have h3 : (1 : ℝ) ≤ X * X * X := by
      have h := mul_le_mul h2 hX1 zero_le_one (mul_nonneg hX0 hX0)
      linarith
    have h4 : (1 : ℝ) ≤ X * X * X * X := by
      have h := mul_le_mul h3 hX1 zero_le_one (mul_nonneg (mul_nonneg hX0 hX0) hX0)
      linarith
    have h5 : X * 1 ≤ X * (X * X * X) := mul_le_mul_of_nonneg_left h3 hX0
    have h6 : X ≤ X * X * X * X := by linarith
    calc X ≤ X * X * X * X := h6
      _ = X ^ 4 := by ring
  have hB4 : B * B ≤ B ^ 4 := by
    have h2 : (1 : ℝ) ≤ B * B := by
      have h := mul_le_mul hB1 hB1 zero_le_one hB0
      linarith
    have h3 : B * B ≤ (B * B) * (B * B) := by
      have h := mul_le_mul_of_nonneg_left h2 (mul_nonneg hB0 hB0)
      simpa using h
    calc B * B ≤ (B * B) * (B * B) := h3
      _ = B ^ 4 := by ring
  -- the datum factor
  have hc : Real.sqrt (Real.pi / 2) * M + Cf * α ≤ Cc * B := by
    rw [hCc, hB]
    have h1 : Real.sqrt (Real.pi / 2) * M ≤ Real.sqrt (Real.pi / 2) * (1 + M) :=
      mul_le_mul_of_nonneg_left (by linarith) hsqrt0
    have h2 : Cf * α ≤ Cf := mul_le_of_le_one_right hCf.le hα1
    have h3 : Cf ≤ Cf * (1 + M) := le_mul_of_one_le_right hCf.le (by linarith)
    nlinarith [h1, h2, h3, hsqrt0, hCf.le, hM0]
  -- the key product inequality
  have hkey : X * (α ^ (-(1 / 2 : ℝ)) * (B * (Real.sqrt (Real.pi / 2) * M + Cf * α)))
      ≤ Cc * (X ^ 4 * P * B ^ 4) := by
    have hbc : B * (Real.sqrt (Real.pi / 2) * M + Cf * α) ≤ B * (Cc * B) :=
      mul_le_mul_of_nonneg_left hc hB0
    have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
    have hinner : X * (α ^ (-(1 / 2 : ℝ)) * (B * B)) ≤ X ^ 4 * (P * B ^ 4) := by
      have h1 : X * (α ^ (-(1 / 2 : ℝ)) * (B * B))
          ≤ X ^ 4 * (α ^ (-(1 / 2 : ℝ)) * (B * B)) :=
        mul_le_mul_of_nonneg_right hX4 (mul_nonneg hr0 (mul_nonneg hB0 hB0))
      have h2 : X ^ 4 * (α ^ (-(1 / 2 : ℝ)) * (B * B)) ≤ X ^ 4 * (P * (B * B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRP (mul_nonneg hB0 hB0))
          (pow_nonneg hX0 4)
      have h3 : X ^ 4 * (P * (B * B)) ≤ X ^ 4 * (P * B ^ 4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB4 hP0) (pow_nonneg hX0 4)
      exact le_trans h1 (le_trans h2 h3)
    calc X * (α ^ (-(1 / 2 : ℝ)) * (B * (Real.sqrt (Real.pi / 2) * M + Cf * α)))
        ≤ X * (α ^ (-(1 / 2 : ℝ)) * (B * (Cc * B))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbc hr0) hX0
      _ = Cc * (X * (α ^ (-(1 / 2 : ℝ)) * (B * B))) := by ring
      _ ≤ Cc * (X ^ 4 * (P * B ^ 4)) := mul_le_mul_of_nonneg_left hinner hCc0
      _ = Cc * (X ^ 4 * P * B ^ 4) := by ring
  -- the coefficient bookkeeping
  have hA : Cp + Cu + Cag + 1 ≤ Cp + Cu + Cag + Cf + 1 := by linarith
  have hA0 : (0 : ℝ) ≤ 54000 * (Cp + Cu + Cag + 1) := by linarith
  have hQ0 : (0 : ℝ) ≤ X ^ 4 * P * B ^ 4 :=
    mul_nonneg (mul_nonneg (pow_nonneg hX0 4) hP0) (pow_nonneg hB0 4)
  rw [hK]
  calc 9 * (1000 * (Cp + Cu + Cag + 1) * X * α ^ (-(1 / 2 : ℝ)) * B)
        * (6 * (Real.sqrt (Real.pi / 2) * M + Cf * α))
      = 54000 * (Cp + Cu + Cag + 1)
          * (X * (α ^ (-(1 / 2 : ℝ)) * (B * (Real.sqrt (Real.pi / 2) * M + Cf * α)))) := by
        ring
    _ ≤ 54000 * (Cp + Cu + Cag + 1) * (Cc * (X ^ 4 * P * B ^ 4)) :=
        mul_le_mul_of_nonneg_left hkey hA0
    _ ≤ 54000 * (Cp + Cu + Cag + Cf + 1) * (Cc * (X ^ 4 * P * B ^ 4)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_nonneg hCc0 hQ0)
    _ ≤ (54000 * (Cp + Cu + Cag + Cf + 1) * Cc + 1) * (X ^ 4 * P * B ^ 4) := by
        have h0 : (0 : ℝ) ≤ 54000 * (Cp + Cu + Cag + Cf + 1) * Cc := by
          have h1 : (0 : ℝ) ≤ Cp + Cu + Cag + Cf + 1 := by linarith
          positivity
        have hstep : 54000 * (Cp + Cu + Cag + Cf + 1) * (Cc * (X ^ 4 * P * B ^ 4))
            = (54000 * (Cp + Cu + Cag + Cf + 1) * Cc) * (X ^ 4 * P * B ^ 4) := by ring
        rw [hstep]
        exact mul_le_mul_of_nonneg_right (by linarith) hQ0
    _ = (54000 * (Cp + Cu + Cag + Cf + 1) * Cc + 1) * X ^ 4 * P * B ^ 4 := by ring

end Work.FTS.StrongPersist.H6Rows
