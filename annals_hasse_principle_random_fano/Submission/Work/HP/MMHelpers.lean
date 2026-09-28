import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MM2.Defs

set_option autoImplicit false
noncomputable section
open Filter

namespace Work.HP

open Filter

/-- `mainTerm` is nonnegative (for `0 ≤ A`). -/
lemma mainTerm_nonneg (d n : ℕ) {A : ℝ} (B : ℝ) (hA : 0 ≤ A) : 0 ≤ mainTerm d n A B := by
  have h1 : 0 ≤ iotaDN d n := by
    rw [iotaDN]
    refine div_nonneg (ENNReal.toReal_nonneg) ?_
    have : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (NN d n - 2) :=
      tsum_nonneg fun k => by positivity
    linarith
  have h3 : 0 ≤ EE d n B := by
    rw [EE, finsum_mem_def]
    refine finsum_nonneg fun p => ?_
    by_cases hp : p ∈ Omega d n B
    · rw [Set.indicator_of_mem hp]; exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
    · rw [Set.indicator_of_notMem hp]
  rw [mainTerm]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) (pow_nonneg hA _)) h3

/-- `Σ₂^{mix}` is a sum of nonnegative terms times a nonnegative weight. -/
lemma Sigma2mix_nonneg (d n : ℕ) [DecidableEq (Mon d n)] {A B : ℝ} (hB : 1 ≤ B) :
    0 ≤ MM2.Sigma2mix d n A B := by
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hW : 0 ≤ (bigW (wOf B) : ℝ) := Nat.cast_nonneg _
  have h : ∀ p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ),
      0 ≤ Set.indicator (MM2.OmegaBad d n A B)
        (fun q : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) =>
          Sstar d n 1 (GamMix d n q.1 q.2 (bigW (wOf B))) (TmixSet d n q.2 A (Real.log B)) /
            eNorm (veronese d n q.2)) p := by
    intro p
    by_cases hp : p ∈ MM2.OmegaBad d n A B
    · rw [Set.indicator_of_mem hp]
      refine div_nonneg ?_ (eNorm_nonneg _)
      rw [Sstar, finsum_mem_def]
      exact finsum_nonneg fun a => by
        by_cases ha : a ∈ {a : Mon d n → ℤ | a ∈ GamMix d n p.1 p.2 (bigW (wOf B)) ∧
            IsPrim a ∧ a ∈ TmixSet d n p.2 A (Real.log B)}
        · simp only [Set.indicator_of_mem ha]
          exact div_nonneg zero_le_one (pow_nonneg (eNorm_nonneg _) 1)
        · simp only [Set.indicator_of_notMem ha, le_refl]
    · rw [Set.indicator_of_notMem hp]
  have hfin := finsum_nonneg h
  rw [MM2.Sigma2mix, finsum_mem_def]
  exact mul_nonneg (div_nonneg (mul_nonneg hlog hW) (by norm_num)) hfin

/-- `sqrt (log A) ≤ A^(1/20)` for `A ≥ 20^20`. -/
lemma sqrt_log_le_rpow (A : ℝ) (hA : (20:ℝ) ^ 20 ≤ A) :
    Real.sqrt (Real.log A) ≤ A ^ ((1 : ℝ) / 20) := by
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le (by positivity) hA
  have h1 : (0:ℝ) < A ^ ((1:ℝ)/20) := Real.rpow_pos_of_pos hA0 _
  have h20 : (20:ℝ) ≤ A ^ ((1:ℝ)/20) := by
    have hc : ((20:ℝ) ^ 20) ^ ((1:ℝ)/20) ≤ A ^ ((1:ℝ)/20) :=
      Real.rpow_le_rpow (by positivity) hA (by norm_num)
    have he : ((20:ℝ) ^ 20) ^ ((1:ℝ)/20) = 20 := by
      rw [← Real.rpow_natCast ((20:ℝ)) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 20),
        show ((20:ℕ):ℝ) * ((1:ℝ)/20) = 1 by norm_num, Real.rpow_one]
    rwa [he] at hc
  have hsq : Real.log A ≤ (A ^ ((1:ℝ)/20)) ^ 2 := by
    have hb : Real.log A ≤ A ^ ((1:ℝ)/20) / ((1:ℝ)/20) := Real.log_le_rpow_div hA0.le (by norm_num)
    have h20' : A ^ ((1:ℝ)/20) / ((1:ℝ)/20) = 20 * A ^ ((1:ℝ)/20) := by
      rw [div_eq_mul_inv, show ((1:ℝ)/20)⁻¹ = 20 by norm_num, mul_comm]
    rw [h20'] at hb
    nlinarith [h1, h20, hb]
  calc Real.sqrt (Real.log A) ≤ Real.sqrt ((A ^ ((1:ℝ)/20)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = A ^ ((1:ℝ)/20) := Real.sqrt_sq h1.le


end Work.HP
