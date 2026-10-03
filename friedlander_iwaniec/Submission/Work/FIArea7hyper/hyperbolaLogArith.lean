import Mathlib

namespace Work.FIArea7hyper

/-- Elementary real-variable bound: for `u ≥ 1`, `(⌊log₂ u⌋ + 1)·log(6u) ≤ 10·(log(u+2))²`. -/
lemma hyperbolaLogArith (u : ℕ) (hu : 1 ≤ u) :
    ((Nat.log 2 u : ℝ) + 1) * Real.log (6 * (u : ℝ))
      ≤ 10 * (Real.log ((u : ℝ) + 2)) ^ 2 := by
  have huR : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
  have huRpos : (0:ℝ) < (u:ℝ) := by linarith
  have hL2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `s` is the right-hand side's logarithm `log (u+2)`.
  set s : ℝ := Real.log ((u:ℝ) + 2) with hsdef
  have hsnonneg : 0 ≤ s := by rw [hsdef]; exact Real.log_nonneg (by linarith)
  -- `log (2u) ≤ 2 log (u+2)` since `2u ≤ (u+2)^2`.
  have hlog2u_le : Real.log (2 * (u:ℝ)) ≤ 2 * s := by
    have hquad : (2:ℝ) * (u:ℝ) ≤ ((u:ℝ)+2)^2 := by nlinarith [sq_nonneg ((u:ℝ))]
    have hp : (0:ℝ) < 2 * (u:ℝ) := by linarith
    have h := Real.log_le_log hp hquad
    rw [Real.log_pow] at h
    norm_num at h
    rw [hsdef]
    linarith
  -- `log (6u) ≤ 2 log (u+2)` since `6u ≤ (u+2)^2`.
  have hlog6u_le : Real.log (6 * (u:ℝ)) ≤ 2 * s := by
    have hquad : (6:ℝ) * (u:ℝ) ≤ ((u:ℝ)+2)^2 := by nlinarith [sq_nonneg ((u:ℝ)-1)]
    have hp : (0:ℝ) < 6 * (u:ℝ) := by linarith
    have h := Real.log_le_log hp hquad
    rw [Real.log_pow] at h
    norm_num at h
    rw [hsdef]
    linarith
  -- `Nat.log 2 u + 1 ≤ log (2u)/log 2 ≤ 5 log (u+2)`.
  have hA : (Nat.log 2 u : ℝ) + 1 ≤ 5 * s := by
    have hpow : 2 ^ Nat.log 2 u ≤ u := Nat.pow_log_le_self 2 (by omega)
    have hpowR : (2:ℝ) ^ Nat.log 2 u ≤ (u:ℝ) := by exact_mod_cast hpow
    have hpos : (0:ℝ) < (2:ℝ) ^ Nat.log 2 u := by positivity
    have hlogu := Real.log_le_log hpos hpowR
    rw [Real.log_pow] at hlogu
    have hn0 : (Nat.log 2 u : ℝ) ≤ Real.log (u:ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hL2pos]; linarith
    have hlogm : Real.log (2 * (u:ℝ)) = Real.log 2 + Real.log (u:ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt huRpos)
    have hA1 : Real.log (u:ℝ)/Real.log 2 + 1 = Real.log (2*(u:ℝ))/Real.log 2 := by
      rw [hlogm, add_div, div_self (ne_of_gt hL2pos)]; ring
    have hc : (2:ℝ)/Real.log 2 ≤ 5 := by
      rw [div_le_iff₀ hL2pos]; nlinarith [Real.log_two_gt_d9]
    calc
      (Nat.log 2 u : ℝ) + 1 ≤ Real.log (u:ℝ)/Real.log 2 + 1 := by linarith
      _ = Real.log (2*(u:ℝ))/Real.log 2 := hA1
      _ ≤ 2*s/Real.log 2 := div_le_div_of_nonneg_right hlog2u_le (le_of_lt hL2pos)
      _ = (2/Real.log 2) * s := by ring
      _ ≤ 5 * s := mul_le_mul_of_nonneg_right hc hsnonneg
  have hBnn : 0 ≤ Real.log (6 * (u:ℝ)) := Real.log_nonneg (by linarith)
  have key : ((Nat.log 2 u : ℝ) + 1) * Real.log (6 * (u:ℝ)) ≤ 10 * s^2 := calc
    ((Nat.log 2 u : ℝ) + 1) * Real.log (6 * (u:ℝ))
        ≤ (5*s) * (2*s) := mul_le_mul hA hlog6u_le hBnn (by linarith)
    _ = 10 * s^2 := by ring
  rw [hsdef] at key
  exact key

end Work.FIArea7hyper
