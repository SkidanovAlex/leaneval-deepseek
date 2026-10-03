/-
# The number of low-lying scales of a lacunary sequence

For a `Λ`-lacunary scale sequence `a` with `a n ≥ 1` (`Λ > 1`) the number of indices `n` whose
dyadic level `logN ⌊a n⌋` stays below a given level `M` is `O_Λ(M)`: since `a n ≥ Λ^n`, the
condition `logN ⌊a n⌋ < M` forces `Λ^n < 2^M`, i.e. `n < M log 2 / log Λ`.

This is what makes the (evidently finite) initial segment of *non-narrow* scales in
`Work.KMTAreas.A7.LoLinVar` cost only a factor `O(k)` on top of the single-scale bound.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7LoLin

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar

noncomputable section

/-- A `Λ`-lacunary sequence with `a n ≥ 1` dominates `Λ^n`. -/
theorem rpow_le_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    ∀ n : ℕ, (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
  intro n
  induction n with
  | zero => simpa using (ha1 0)
  | succ j ih =>
      have hpos : (0 : NNReal) < a j := lt_of_lt_of_le zero_lt_one (ha1 j)
      have hdiv : Λ < a (j + 1) / a j := ha j
      have hltNN : Λ * a j < a (j + 1) := by rwa [lt_div_iff₀ hpos] at hdiv
      have hlt : (Λ : ℝ) * (a j : ℝ) < (a (j + 1) : ℝ) := by exact_mod_cast hltNN
      calc (Λ : ℝ) ^ (j + 1) = (Λ : ℝ) ^ j * Λ := by rw [pow_succ]
        _ ≤ (a j : ℝ) * Λ := by
            have hΛnn : (0 : ℝ) ≤ (Λ : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_right ih hΛnn
        _ = (Λ : ℝ) * (a j : ℝ) := by ring
        _ ≤ (a (j + 1) : ℝ) := le_of_lt hlt

/-- **The low-lying scales of a lacunary sequence are bounded** (explicit form). -/
theorem badScale_bound_explicit {Λ : NNReal} (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (M : ℕ) :
    ∀ n : ℕ, logN (Nat.floor (a n)) < (M : ℤ) →
      n < ⌈(M : ℝ) * (Real.log 2 / Real.log (Λ : ℝ))⌉₊ + 1 := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlog : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛR
  intro n hn
  have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := rpow_le_of_lacunary hΛ ha ha1 n
  -- the level condition bounds `a n` by `2^M`
  have hMlt : Nat.log 2 (max (Nat.floor (a n)) 2) < M := by
    have h1 : logN (Nat.floor (a n)) < (M : ℤ) := hn
    have h2 : (logN (Nat.floor (a n))).toNat < M := by
      have h3 : (0 : ℤ) ≤ logN (Nat.floor (a n)) := by simp only [logN]; positivity
      omega
    simpa [logN] using h2
  have h2M : (a n : ℝ) < (2 : ℝ) ^ M := by
    have hfloor_lt : (a n : ℝ) < (Nat.floor (a n) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hNlt : Nat.floor (a n) < 2 ^ M := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max (Nat.floor (a n)) 2)
      calc Nat.floor (a n) ≤ max (Nat.floor (a n)) 2 := le_max_left _ _
        _ < 2 ^ (Nat.log 2 (max (Nat.floor (a n)) 2) + 1) := h
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcast : (Nat.floor (a n) : ℝ) + 1 ≤ ((2 ^ M : ℕ) : ℝ) := by
      have : Nat.floor (a n) + 1 ≤ 2 ^ M := hNlt
      exact_mod_cast this
    have : ((2 ^ M : ℕ) : ℝ) = (2 : ℝ) ^ M := by push_cast; ring
    linarith [hfloor_lt, hcast, this.le, this.ge]
  -- hence `n log Λ < M log 2`
  have hloglt : (n : ℝ) * Real.log (Λ : ℝ) < (M : ℝ) * Real.log 2 := by
    have h1 : Real.log ((Λ : ℝ) ^ n) < Real.log ((2 : ℝ) ^ M) :=
      Real.log_lt_log (by positivity) (by linarith)
    rw [Real.log_pow, Real.log_pow] at h1
    linarith [h1]
  have hbound : (n : ℝ) < (M : ℝ) * (Real.log 2 / Real.log (Λ : ℝ)) := by
    have h2 := mul_lt_mul_of_pos_right hloglt (inv_pos.mpr hlog)
    rw [mul_assoc] at h2
    have h3 : Real.log (Λ : ℝ) * (Real.log (Λ : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ hlog.ne'
    rw [h3, mul_one] at h2
    calc (n : ℝ) < (M : ℝ) * Real.log 2 * (Real.log (Λ : ℝ))⁻¹ := h2
      _ = (M : ℝ) * (Real.log 2 / Real.log (Λ : ℝ)) := by rw [div_eq_mul_inv]; ring
  have hJ : (n : ℝ) < ((⌈(M : ℝ) * (Real.log 2 / Real.log (Λ : ℝ))⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil ((M : ℝ) * (Real.log 2 / Real.log (Λ : ℝ)))]
  exact_mod_cast hJ

/-- **The low-lying scales of a lacunary sequence are bounded.** -/
theorem exists_badScale_bound {Λ : NNReal} (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (M : ℕ) :
    ∃ J : ℕ, ∀ n : ℕ, logN (Nat.floor (a n)) < (M : ℤ) → n < J :=
  ⟨_, badScale_bound_explicit hΛ a ha ha1 M⟩

end

end Work.KMTAreas.A7LoLin
