import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

noncomputable section

namespace Commons.Analysis.ExpLog

/-- The least natural number `p` with `H^(1/M) ≤ p`, i.e. `⌈H^(1/M)⌉₊`. -/
def lowerThreshold (M H : ℕ) : ℕ :=
  Nat.ceil ((H : ℝ) ^ ((1 : ℝ) / (M : ℝ)))

lemma lowerThreshold_le_of_rpow_le (M H p : ℕ)
    (hle : (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ (p : ℝ)) : lowerThreshold M H ≤ p :=
  (Nat.ceil_le).2 hle

lemma rpow_le_lowerThreshold (M H : ℕ) :
    (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ (lowerThreshold M H : ℝ) :=
  Nat.le_ceil ((H : ℝ) ^ ((1 : ℝ) / (M : ℝ)))

lemma le_pow_lowerThreshold (M H : ℕ) (hM : 1 ≤ M) : H ≤ (lowerThreshold M H) ^ M := by
  have hMne : M ≠ 0 := by omega
  have hx0 : 0 ≤ (H : ℝ) := by exact_mod_cast Nat.zero_le H
  have hce : (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ (lowerThreshold M H : ℝ) :=
    rpow_le_lowerThreshold M H
  have hce' : (H : ℝ) ^ ((M : ℝ)⁻¹) ≤ (lowerThreshold M H : ℝ) := by
    simpa [div_eq_mul_inv] using hce
  have hpow : ((H : ℝ) ^ ((M : ℝ)⁻¹)) ^ M ≤ (lowerThreshold M H : ℝ) ^ M :=
    pow_le_pow_left₀ (Real.rpow_nonneg hx0 _) hce' M
  have hrid : ((H : ℝ) ^ ((M : ℝ)⁻¹)) ^ M = (H : ℝ) :=
    Real.rpow_inv_natCast_pow hx0 hMne
  have hfin : (H : ℝ) ≤ ((lowerThreshold M H) ^ M : ℝ) := by
    simpa [hrid, Nat.cast_pow] using hpow
  exact_mod_cast hfin

lemma lt_lowerThreshold_of_ge (M H : ℕ) (hM : 1 ≤ M) (hH : (M + 1) ^ M ≤ H) :
    M < lowerThreshold M H := by
  have hMposR : 0 < (M : ℝ) := by
    have : 0 < M := lt_of_lt_of_le zero_lt_one hM
    exact_mod_cast this
  have hx0 : 0 ≤ (M + 1 : ℝ) := by positivity
  have hH0 : 0 ≤ (H : ℝ) := by exact_mod_cast Nat.zero_le H
  have hbase : ((M + 1 : ℕ) ^ M : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hpow_ineq : (M + 1 : ℝ) ^ (M : ℝ) ≤ (H : ℝ) := by
    simpa [Nat.cast_pow] using hbase
  have hroot : (M + 1 : ℝ) ≤ (H : ℝ) ^ ((M : ℝ)⁻¹) :=
    (Real.le_rpow_inv_iff_of_pos hx0 hH0 hMposR).2 hpow_ineq
  have hce : (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ (lowerThreshold M H : ℝ) :=
    rpow_le_lowerThreshold M H
  have hce' : (H : ℝ) ^ ((M : ℝ)⁻¹) ≤ (lowerThreshold M H : ℝ) := by
    simpa [div_eq_mul_inv] using hce
  have hltR : (M : ℝ) < (lowerThreshold M H : ℝ) := by
    nlinarith [le_trans hroot hce']
  exact_mod_cast hltR

theorem exists_ceil_rpow_lower_threshold (M : ℕ) (hM : 1 ≤ M) :
    ∃ B : ℕ → ℕ,
      (∀ᶠ H : ℕ in atTop, H ≤ (B H) ^ M) ∧
      (∀ᶠ H : ℕ in atTop, M < B H) ∧
      (∀ H p : ℕ, 1 ≤ p → (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ (p : ℝ) → B H ≤ p) := by
  refine ⟨lowerThreshold M, ?_, ?_, ?_⟩
  · exact Eventually.of_forall fun H => le_pow_lowerThreshold M H hM
  · rw [eventually_atTop]
    exact ⟨(M + 1) ^ M, fun H hH => lt_lowerThreshold_of_ge M H hM hH⟩
  · intro H p _hp hle
    exact lowerThreshold_le_of_rpow_le M H p hle

end Commons.Analysis.ExpLog