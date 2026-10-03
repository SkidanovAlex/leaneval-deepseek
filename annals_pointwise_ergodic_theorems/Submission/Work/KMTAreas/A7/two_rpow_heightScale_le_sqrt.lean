import Mathlib
import Submission.Work.KMTAreas.A7.heightScale_rpow_le

/-!
# `2^{ρ l_{(N)}} ≤ √(Log N + 2)`

With `l_{(N)} = heightScale C₀ N = C₀ · LogLog N` (`LogLog N = log₂(log₂ max(N,2) + 2)`) and
`ρ C₀ ≤ 1/2`, the height scale `l_{(N)}` grows at most like a square root of the logarithmic
parameter:

`2^{ρ l_{(N)}} ≤ √(log₂ max(N,2) + 2)`.

Indeed `ρ l_{(N)} ≤ (1/2) LogLog N = log₂ √(2^{LogLog N})`, and the auxiliary estimate
`Work.KMTAreas.A7.two_rpow_logLogN_le` gives `2^{LogLog N} ≤ log₂ N + 2`.  This is the elementary
estimate that keeps the exponential loss `2^{A ρ l_{(N)}}` of §5 of Krause--Mirek--Tao within a
power of `Log N`.
-/

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

lemma two_rpow_heightScale_le_sqrt {ρ : ℝ} {C₀ : ℕ} (hρ : 0 < ρ)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 2) (N : ℕ) :
    (2 : ℝ) ^ (ρ * ((Work.Analysis.EndVar.heightScale C₀ N : ℕ) : ℝ))
      ≤ Real.sqrt (((Nat.log 2 (max N 2) : ℕ) : ℝ) + 2) := by
  -- `ρ · l_{(N)} = ρC₀ · LogLog N ≤ (1/2) · LogLog N`
  have hLLnonneg : (0 : ℝ) ≤ (logLogN N : ℝ) := Nat.cast_nonneg _
  have hexp : ρ * ((heightScale C₀ N : ℕ) : ℝ) ≤ (1 / 2) * (logLogN N : ℝ) := by
    rw [heightScale, Nat.cast_mul]
    calc ρ * ((C₀ : ℝ) * (logLogN N : ℝ)) = (ρ * (C₀ : ℝ)) * (logLogN N : ℝ) := by ring
      _ ≤ (1 / 2) * (logLogN N : ℝ) := mul_le_mul_of_nonneg_right hρC₀ hLLnonneg
  have h1 : (2 : ℝ) ^ (ρ * ((heightScale C₀ N : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ ((1 / 2) * (logLogN N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  -- `2^{(1/2) LogLog N} = √(2^{LogLog N})`
  have h2 : (2 : ℝ) ^ ((1 / 2) * (logLogN N : ℝ))
      = Real.sqrt ((2 : ℝ) ^ (logLogN N : ℝ)) := by
    rw [show (1 / 2 : ℝ) * (logLogN N : ℝ) = (logLogN N : ℝ) * (1 / 2) by ring]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_eq_rpow]
  -- `2^{LogLog N} ≤ log₂ N + 2 ≤ log₂ max(N,2) + 2`
  have h3 : (2 : ℝ) ^ (logLogN N : ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) + 2 :=
    two_rpow_logLogN_le N
  have h4 : ((Nat.log 2 N : ℕ) : ℝ) + 2 ≤ ((Nat.log 2 (max N 2) : ℕ) : ℝ) + 2 := by
    have hb : Nat.log 2 N ≤ Nat.log 2 (max N 2) :=
      Nat.log_mono_right (b := 2) (le_max_left N 2)
    exact_mod_cast Nat.add_le_add_right hb 2
  have h5 : Real.sqrt ((2 : ℝ) ^ (logLogN N : ℝ))
      ≤ Real.sqrt (((Nat.log 2 (max N 2) : ℕ) : ℝ) + 2) :=
    Real.sqrt_le_sqrt (h3.trans h4)
  exact (h1.trans_eq h2).trans h5

end Work.KMTAreas.A7
