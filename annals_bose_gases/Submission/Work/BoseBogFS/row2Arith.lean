import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

theorem row2Arith {B η T L eps : ℝ} (hT0 : 0 < T) (heps0 : 0 < eps) (hη0 : 0 ≤ η) (hL1 : 1 ≤ L) (hTdef : T = 10 ^ 6 * (1 + L) / eps) (hηT : η * T ≤ 1) (hB : B = 8 * Real.pi + η * T) (hlog : Real.log T ≤ 56 + (1 / 1292) * L) : (B + 8 * Real.pi) ^ 2 * Real.log T / T ≤ eps := by
  -- `B + 8π = 16π + ηT`, with `ηT ≤ 1` hence `B + 8π ≤ 16·3.15 + 1 < 52`.
  have hL0 : (0:ℝ) < L := by linarith
  have h1L : (0:ℝ) < 1 + L := by linarith
  have hB8pos : 0 ≤ B + 8 * Real.pi := by
    have hh : B + 8 * Real.pi = 16 * Real.pi + η * T := by rw [hB]; ring
    rw [hh]
    have : 0 ≤ η * T := mul_nonneg hη0 hT0.le
    linarith [Real.pi_pos]
  have hB8 : B + 8 * Real.pi ≤ 52 := by
    have hh : B + 8 * Real.pi = 16 * Real.pi + η * T := by rw [hB]; ring
    rw [hh]
    linarith [Real.pi_lt_d2]
  have hsq : (B + 8 * Real.pi) ^ 2 ≤ 2704 := by nlinarith [hB8, hB8pos]
  -- `56 + L/1292 ≤ 56·(1+L)` and `2704·56 ≤ 10⁶`.
  have hX0 : 0 ≤ 56 + (1 / 1292) * L := by
    have : 0 ≤ (1 / 1292 : ℝ) * L := mul_nonneg (by norm_num) hL0.le
    linarith
  have hLX : 56 + (1 / 1292) * L ≤ 56 * (1 + L) := by
    have h1292 : (1:ℝ)/1292 ≤ 1 := by norm_num
    have hml : (1 / 1292 : ℝ) * L ≤ 1 * L := mul_le_mul_of_nonneg_right h1292 hL0.le
    linarith
  have hkey : 2704 * (56 + (1 / 1292) * L) ≤ 10 ^ 6 * (1 + L) := by
    have h2704 : (2704:ℝ) * 56 ≤ 10^6 := by norm_num
    calc 2704 * (56 + (1 / 1292) * L) ≤ 2704 * (56 * (1 + L)) := by
            apply mul_le_mul_of_nonneg_left hLX (by norm_num)
          _ ≤ 10^6 * (1 + L) := by nlinarith [h2704, h1L]
  -- Chain of inequalities, dividing by `T` and rewriting `1/T = eps/(10⁶(1+L))`.
  have hA : (B + 8 * Real.pi) ^ 2 * Real.log T
      ≤ (B + 8 * Real.pi) ^ 2 * (56 + (1 / 1292) * L) :=
    mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
  have hstep1 : (B + 8 * Real.pi) ^ 2 * Real.log T / T
      ≤ (B + 8 * Real.pi) ^ 2 * (56 + (1 / 1292) * L) / T :=
    div_le_div_of_nonneg_right hA hT0.le
  have hstep2 : (B + 8 * Real.pi) ^ 2 * (56 + (1 / 1292) * L) / T
      ≤ 2704 * (56 + (1 / 1292) * L) / T :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hX0) hT0.le
  have hTinv : 2704 * (56 + (1 / 1292) * L) / T
      = 2704 * (56 + (1 / 1292) * L) * eps / (10 ^ 6 * (1 + L)) := by
    rw [hTdef]
    field_simp
  have hfin : 2704 * (56 + (1 / 1292) * L) * eps / (10 ^ 6 * (1 + L)) ≤ eps := by
    have hb : (0:ℝ) < 10 ^ 6 * (1 + L) := by positivity
    rw [div_le_iff₀ hb]
    have hml := mul_le_mul_of_nonneg_right hkey heps0.le
    nlinarith [hml]
  exact hstep1.trans ((hstep2.trans_eq hTinv).trans hfin)

end Work.BoseBogFS
