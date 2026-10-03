/-
# Arithmetic of the bump scale `ballScale`

For `N ≥ 1` the reciprocal width `ballScale P N = 2^{d·Log N}` of the `g`-side bump satisfies
`ballScale P N ≤ 2^d · N^d` and `N^d ≤ 2^d · ballScale P N`; this is what converts the pointwise
deviation bound `‖ballDev P N t ξ‖ ≤ C · min 1 (ballScale P N · |ξ|)` into the lacunary geometric
summand `(N^d |ξ|)^2 · 1_{N^d |ξ| < 2^d}` of `Work.KMTPlan.A6.lacunaryGeometricSumLeENNReal`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BallDevDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators

theorem ballScale_le_pow_mul (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) :
    ballScale P N ≤ (2:ℝ) ^ P.natDegree * (N:ℝ) ^ P.natDegree ∧
    (N:ℝ) ^ P.natDegree ≤ (2:ℝ) ^ P.natDegree * ballScale P N := by
  set L : ℕ := Nat.log 2 (max N 2) with hLdef
  have hlogN : Work.Analysis.EndVar.logN N = (L : ℤ) := by
    rw [hLdef, Work.Analysis.EndVar.logN]
  have hbs : ballScale P N = ((2:ℝ) ^ L) ^ P.natDegree := by
    rw [ballScale, hlogN]
    have hcast : (P.natDegree : ℝ) * ((L : ℤ) : ℝ) = ((L * P.natDegree : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast, Real.rpow_natCast, pow_mul]
  have hpowL : (2:ℝ) ^ L ≤ (max N 2 : ℝ) := by
    have h := Nat.pow_log_le_self 2 (by omega : max N 2 ≠ 0)
    rw [← hLdef] at h
    exact_mod_cast h
  have hmax2 : (max N 2 : ℝ) ≤ 2 * N := by
    have h1 : (max N 2 : ℕ) ≤ 2 * N := by
      rw [max_le_iff]
      exact ⟨by omega, by omega⟩
    exact_mod_cast h1
  have hNle : (N : ℝ) ≤ 2 * (2:ℝ) ^ L := by
    have hlt : max N 2 < 2 ^ (L + 1) := by
      rw [hLdef]
      simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
    have h1 : (max N 2 : ℝ) < 2 * (2:ℝ)^L := by
      have h2 : ((2^(L+1) : ℕ) : ℝ) = 2 * (2:ℝ)^L := by
        rw [pow_succ]; push_cast; ring
      have h3 : (max N 2 : ℝ) < ((2^(L+1) : ℕ) : ℝ) := by exact_mod_cast hlt
      linarith
    have h4 : (N:ℝ) ≤ (max N 2 : ℝ) := by exact_mod_cast le_max_left N 2
    linarith
  constructor
  · rw [hbs]
    calc ((2:ℝ)^L)^P.natDegree ≤ (2 * (N:ℝ))^P.natDegree :=
          pow_le_pow_left₀ (by positivity) (le_trans hpowL hmax2) _
      _ = (2:ℝ)^P.natDegree * (N:ℝ)^P.natDegree := by rw [mul_pow]
  · calc (N:ℝ)^P.natDegree ≤ (2 * (2:ℝ)^L)^P.natDegree :=
        pow_le_pow_left₀ (by positivity) hNle _
      _ = (2:ℝ)^P.natDegree * ((2:ℝ)^L)^P.natDegree := by rw [mul_pow]
      _ = (2:ℝ)^P.natDegree * ballScale P N := by rw [hbs]


end Work.KMTPlan.A6
