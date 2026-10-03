/-
# The `goodScale`-to-band arithmetic of the adelic lift

`Work.KMTPlan.A6.goodScale Q L N` is the gate at which the A6/A7 model's windows are narrower than
the spacing `1/Q` of the arithmetic frequencies (`MdlAdelicDefs.lean`):

    `goodScale Q L N := 8 * Q * 2 ^ (L + 1) ≤ N`,

with `Q = arithQ ρ (max l₁ l₂)` and `L = lcL l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂)`.  The two
window widths of the frozen slice at that scale are

    `γ₁ = 2^{k₁ − Log N}`   (`mdlSliceF_band`),      `γ₂ = 2^{d (k₂ − Log N)}`   (`MdlSliceGband`),

and the product rule `BtwistBandOfInputs` makes the band of the slice the Minkowski sum of the two,
i.e. of width `γ₁ + γ₂`.  The adelic clauses (`AdelicFormPropRange`, `AdelicRealizeBounded`,
`AdelicLiftExists`) require this to be at most `1/(8Q)` (their `β`):

    `Work.KMTPlan.A6.goodScale_two_pow_bands_le`  (this file):

    `goodScale Q L N → k₁ ≤ L → k₂ ≤ L → 2 ≤ d → 1 ≤ Q → γ₁ + γ₂ ≤ 1/(8Q)`.

This is exactly the assertion made in the docstring of `MdlAdelicPackets.lean:167`
("`γ₁ = 2^{k₁ − Log ⌊a n⌋}`, which the `goodScale` gate turns into `γ₁ + γ₂ ≤ 1/(8Q)`"), and the
constant `8` in `goodScale` is *calibrated* for it: the statement is true but tight (the two
leading cases are `Q = 2^m` and `Q = 2^m - 1`, where the ratio `8Q (γ₁ + γ₂)` approaches `1`).

The proof (see the review of this statement) writes `t = ⌊log₂ (8Q)⌋`, `A = 2^{t+1}`, so that
`8Q < A`; `goodScale` gives `⌊log₂ N⌋ ≥ t + L + 1`, whence `γ₁ ≤ 1/A` and
`γ₂ ≤ 1/A^d ≤ 1/A²`; and `1/A + 1/A² ≤ 1/(A−1) ≤ 1/(8Q)`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal BigOperators

/-- **`Nat.log 2` of a product with a power of two**: `⌊log₂ (n · 2^m)⌋ = ⌊log₂ n⌋ + m` for
`n ≠ 0`. -/
private lemma natLog_two_mul_pow (n m : ℕ) (hn : n ≠ 0) :
    Nat.log 2 (n * 2 ^ m) = Nat.log 2 n + m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h1 : n * 2 ^ (k + 1) = n * 2 ^ k * 2 := by ring
      rw [h1, Nat.log_mul_base (by norm_num) (by positivity), ih]
      omega

/-- **The `goodScale` gate bounds the two window widths by `1/(8Q)`.**  With `L` dominating the two
scales `k₁`, `k₂` and `d ≥ 2` (the degree of the polynomial), the two widths `2^{k₁ − Log N}` and
`2^{d(k₂ − Log N)}` of the frozen slice at a good scale add up to at most `1/(8Q)`. -/
theorem goodScale_two_pow_bands_le (Q L N k₁ k₂ d : ℕ) (hd : 2 ≤ d) (hQ : 1 ≤ Q)
    (h : goodScale Q L N) (h₁ : k₁ ≤ L) (h₂ : k₂ ≤ L) :
    (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
        + (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
      ≤ 1 / (8 * (Q : ℝ)) := by
  unfold goodScale at h
  -- the comparison modulus `A = 2^{⌊log₂ (8Q)⌋+1} > 8Q`
  set t : ℕ := Nat.log 2 (8 * Q) with ht
  set A : ℕ := 2 ^ (t + 1) with hA
  have h8Qne : 8 * Q ≠ 0 := by positivity
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have h8Q_lt_A : 8 * Q < A := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (8 * Q)
    simpa [ht, hA, Nat.succ_eq_add_one] using this
  have hA2 : 2 ≤ A := by
    have : 2 ^ 1 ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hA] using this
  -- `⌊log₂ (8Q · 2^{L+1})⌋ = t + L + 1`, hence `⌊log₂ N⌋ ≥ t + L + 1`
  have hlog_prod : Nat.log 2 (8 * Q * 2 ^ (L + 1)) = t + L + 1 := by
    rw [ht, natLog_two_mul_pow (8 * Q) (L + 1) h8Qne]
    omega
  have hlogN_ge : t + L + 1 ≤ Nat.log 2 (max N 2) := by
    rw [← hlog_prod]
    exact Nat.log_mono_right (le_trans h (le_max_left _ _))
  have hs : ((t + L + 1 : ℕ) : ℝ) ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
    rw [show ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) = ((Nat.log 2 (max N 2) : ℕ) : ℝ) from by
      simp [Work.Analysis.EndVar.logN]]
    exact_mod_cast hlogN_ge
  have hsum_nat : ((t + L + 1 : ℕ) : ℝ) = (t : ℝ) + (L : ℝ) + 1 := by push_cast; ring
  have hsucc_nat : (((t + 1 : ℕ)) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
  -- the two widths
  have hterm1 : (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
      ≤ 1 / (A : ℝ) := by
    have hk1 : (k₁ : ℝ) ≤ (L : ℝ) := by exact_mod_cast h₁
    have hstep : (k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
        ≤ -(((t + 1 : ℕ)) : ℝ) := by
      rw [hsum_nat] at hs
      linarith
    calc (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
        ≤ (2 : ℝ) ^ (-(((t + 1 : ℕ)) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hstep
      _ = 1 / (A : ℝ) := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, hA]
          push_cast
          rw [one_div]
  have hterm2 : (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
      ≤ 1 / (A : ℝ) ^ 2 := by
    have hk2 : (k₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast h₂
    have hstep : (k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
        ≤ -(((t + 1 : ℕ)) : ℝ) := by
      rw [hsum_nat] at hs
      linarith
    have h1 : (2 : ℝ) ^ ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
        ≤ 1 / (A : ℝ) := by
      calc (2 : ℝ) ^ ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
          ≤ (2 : ℝ) ^ (-(((t + 1 : ℕ)) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hstep
        _ = 1 / (A : ℝ) := by
            rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, hA]
            push_cast
            rw [one_div]
    have hbase_nonneg : (0 : ℝ) ≤ 2 ^ ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (le_trans (by norm_num) hA2)
    have hinv1 : 1 / (A : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hA1
    have hinv_nonneg : (0 : ℝ) ≤ 1 / (A : ℝ) := by positivity
    calc (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
        = ((2 : ℝ) ^ ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))) ^ d := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          ring_nf
      _ ≤ (1 / (A : ℝ)) ^ d := pow_le_pow_left₀ hbase_nonneg h1 d
      _ ≤ (1 / (A : ℝ)) ^ 2 := pow_le_pow_of_le_one hinv_nonneg hinv1 (by omega : 2 ≤ d)
      _ = 1 / (A : ℝ) ^ 2 := by rw [div_pow, one_pow]
  -- assemble
  have hApos : (0 : ℝ) < (A : ℝ) := by positivity
  have hA2R : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2
  have hkey : 1 / (A : ℝ) + 1 / (A : ℝ) ^ 2 ≤ 1 / (8 * (Q : ℝ)) := by
    have hAm1 : (0 : ℝ) < (A : ℝ) - 1 := by linarith
    have h8Q : (0 : ℝ) < 8 * (Q : ℝ) := by positivity
    have hle : 8 * (Q : ℝ) ≤ (A : ℝ) - 1 := by
      have hcast : ((8 * Q : ℕ) : ℝ) + 1 ≤ (A : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt h8Q_lt_A
      push_cast at hcast
      linarith
    have h1 : 1 / ((A : ℝ) - 1) ≤ 1 / (8 * (Q : ℝ)) :=
      one_div_le_one_div_of_le h8Q hle
    have h2 : 1 / (A : ℝ) + 1 / (A : ℝ) ^ 2 ≤ 1 / ((A : ℝ) - 1) := by
      rw [← sub_nonneg]
      have heq : 1 / ((A : ℝ) - 1) - (1 / (A : ℝ) + 1 / (A : ℝ) ^ 2)
          = 1 / ((A : ℝ) ^ 2 * ((A : ℝ) - 1)) := by
        field_simp
        ring
      rw [heq]
      positivity
    linarith
  linarith [hterm1, hterm2, hkey]

end Work.KMTPlan.A6
