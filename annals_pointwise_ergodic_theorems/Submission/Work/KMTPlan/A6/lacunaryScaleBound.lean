import Mathlib
import Submission.Work.KMTPlan.A6.lacunaryLevel

set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6

open scoped NNReal

/-!
# The scale bound for a lacunary sequence

For a `Λ`-lacunary sequence `a : ℕ → ℝ≥0` with `Λ > 1` and `a n ≥ 1` we have
`a n ≳ Λ ^ n`, hence `a n` is eventually larger than any prescribed `K ∈ ℕ`: after
`⌈(K+1) / log₂ Λ⌉ + 1` indices, `a n > K`, i.e. `K < ⌊a n⌋`.

The proof is the elementary chain

`K + 1 ≤ 2 ^ (K + 1) ≤ 2 ^ (n · log₂ Λ) = Λ ^ n ≤ a n`,

the middle estimate being `n · log₂ Λ ≥ K + 1`, which is exactly what the hypothesis
`n ≥ ⌈(K+1) / log₂ Λ⌉ + 1` guarantees.  The growth `Λ ^ n ≤ a n` is
`lacunary_growth_pow` of `lacunaryLevel.lean` (applied at `p = 0`, using `a 0 ≥ 1`).
-/

theorem lacunaryScaleBound (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (K : ℕ) :
    ∀ n : ℕ, Nat.ceil (((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ)) + 1 ≤ n → K < Nat.floor (a n) := by
  intro n hn
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlogpos : 0 < Real.logb 2 (Λ : ℝ) := Real.logb_pos (by norm_num) hΛR
  have hlogne : Real.logb 2 (Λ : ℝ) ≠ 0 := ne_of_gt hlogpos
  -- Step 1: `n ≥ (K+1)/log₂ Λ + 1` as a real inequality.
  have hnR : ((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ) + 1 ≤ (n : ℝ) := by
    have h1 : ((Nat.ceil (((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ)) : ℕ) : ℝ) + 1
        ≤ (n : ℝ) := by
      exact_mod_cast hn
    have h2 : ((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ)
        ≤ ((Nat.ceil (((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ)) : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  -- Step 2: hence `n · log₂ Λ ≥ K + 1`.
  have hexp : (K : ℝ) + 1 ≤ (n : ℝ) * Real.logb 2 (Λ : ℝ) := by
    have hstep : (((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ) + 1) * Real.logb 2 (Λ : ℝ)
        ≤ (n : ℝ) * Real.logb 2 (Λ : ℝ) :=
      mul_le_mul_of_nonneg_right hnR hlogpos.le
    have hsimp : (((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ) + 1) * Real.logb 2 (Λ : ℝ)
        = ((K : ℝ) + 1) + Real.logb 2 (Λ : ℝ) := by
      rw [add_mul, div_mul_cancel₀ _ hlogne, one_mul]
    rw [hsimp] at hstep
    linarith
  have hexp' : (((K + 1 : ℕ)) : ℝ) ≤ (n : ℝ) * Real.logb 2 (Λ : ℝ) := by
    push_cast
    exact hexp
  -- Step 3: `K + 1 ≤ 2 ^ (n · log₂ Λ)`.
  have hKle : (((K + 1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ (((K + 1 : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self (n := K + 1)).le
  have hpow2 : (2 : ℝ) ^ (((K + 1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Λ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp'
  -- Step 4: `Λ ^ n ≤ a n`.
  have hgr := lacunary_growth_step Λ a ha ha1
  have hpow := lacunary_growth_pow Λ a hgr 0 n
  have hΛn : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    simp only [Nat.zero_add] at hpow
    have ha0 : (1 : ℝ) ≤ (a 0 : ℝ) := by
      have := ha1 0; exact_mod_cast this
    have hnn : (0 : ℝ) ≤ (Λ : ℝ) ^ n := pow_nonneg (by linarith) n
    calc (Λ : ℝ) ^ n = (Λ : ℝ) ^ n * 1 := (mul_one _).symm
      _ ≤ (Λ : ℝ) ^ n * (a 0 : ℝ) := mul_le_mul_of_nonneg_left ha0 hnn
      _ ≤ (a n : ℝ) := hpow
  -- Step 5: `2 ^ (n · log₂ Λ) = Λ ^ n`, since `2 ^ log₂ Λ = Λ`.
  have hlog : (2 : ℝ) ^ Real.logb 2 (Λ : ℝ) = (Λ : ℝ) :=
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith : (0 : ℝ) < (Λ : ℝ))
  have hpowexp : (Λ : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Λ : ℝ)) := by
    have h1 : (Λ : ℝ) ^ n = ((2 : ℝ) ^ Real.logb 2 (Λ : ℝ)) ^ n := by rw [hlog]
    rw [h1, ← Real.rpow_natCast ((2 : ℝ) ^ Real.logb 2 (Λ : ℝ)) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.logb 2 (Λ : ℝ)) (n : ℝ)]
    congr 1
    ring
  -- Assemble: `(K+1 : ℝ≥0) ≤ a n`, then take floors.
  have hK1 : ((K + 1 : ℕ) : NNReal) ≤ a n := by
    rw [← NNReal.coe_le_coe]
    push_cast
    calc (K : ℝ) + 1 = (((K + 1 : ℕ)) : ℝ) := by push_cast; ring
      _ ≤ (2 : ℝ) ^ (((K + 1 : ℕ)) : ℝ) := hKle
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Λ : ℝ)) := hpow2
      _ = (Λ : ℝ) ^ n := hpowexp.symm
      _ ≤ (a n : ℝ) := hΛn
  have := Nat.le_floor hK1
  omega

end Work.KMTPlan.A6
