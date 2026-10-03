import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallSet_le_log

/-!
# Counting the lacunary indices whose floor is below a threshold

For a `Λ`-lacunary sequence `a : ℕ → ℝ≥0` with `a n ≥ 1` (so `a n ≥ Λ ^ n`) and `Λ > 1`, the set of
indices `n < M` with `⌊a n⌋ ≤ X` is contained in an initial segment of length `≲ log₂ X`:
there is a constant `K` depending only on `Λ` with

  `#{n < M | ⌊a n⌋ ≤ X} ≤ K * (Nat.log 2 (X + 2) + 1)`.

This is the elementary counting estimate used to control the number of lacunary scales below a
given level.  The proof is the obvious one: `⌊a n⌋ ≤ X` forces `Λ ^ n ≤ a n < X + 1`, and since
`X + 2 < 2 ^ (Nat.log 2 (X + 2) + 1)`, the inequality `Λ ^ n < X + 1` bounds `n` by a fixed
multiple of `Nat.log 2 (X + 2) + 1`.

The arithmetic core is isolated as `rpow_lt_natLog_le_aux` (a real-variable statement, also
available as `Work.KMTPlan.A6.rpow_lt_natLog_le`).
-/

namespace Work.KMTPlan.A6

open scoped NNReal BigOperators

/-- If `1 ≤ K₀ * logb 2 λ` and `λ > 1` then `2 ≤ λ ^ K₀`: indeed taking `logb 2` of the
conclusion, it is enough to show `1 ≤ logb 2 (λ ^ K₀) = K₀ * logb 2 λ`, which is the hypothesis. -/
theorem two_le_pow_of_one_le_mul_logb {lam : ℝ} (hlam : 1 < lam) {K₀ : ℕ}
    (hK₀ : 1 ≤ (K₀ : ℝ) * Real.logb 2 lam) : (2 : ℝ) ≤ lam ^ K₀ := by
  have hpos : (0 : ℝ) < lam ^ K₀ := pow_pos (by linarith) K₀
  have h1 : (1 : ℝ) ≤ Real.logb 2 (lam ^ K₀) := by
    rw [Real.logb_pow]
    exact hK₀
  have h2 : (2 : ℝ) ^ (1 : ℝ) ≤ lam ^ K₀ :=
    (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).mp h1
  simpa using h2

/-- **Arithmetic core.**  If `Λ > 1` and `1 ≤ K₀ * logb 2 Λ`, then `Λ ^ n < X + 1` forces
`n ≤ K₀ * (Nat.log 2 (X + 2) + 1)`.

Indeed `X + 2 < 2 ^ (Nat.log 2 (X + 2) + 1) ≤ (Λ ^ K₀) ^ (Nat.log 2 (X + 2) + 1) = Λ ^ (K₀ * …)`,
so any `n ≥ K₀ * (Nat.log 2 (X + 2) + 1)` satisfies `Λ ^ n ≥ Λ ^ (K₀ * (Nat.log 2 (X + 2) + 1)) >
X + 1`, contradicting the hypothesis. -/
theorem rpow_lt_natLog_le_aux {lam : ℝ} (hlam : 1 < lam) {K₀ : ℕ}
    (hK₀ : 1 ≤ (K₀ : ℝ) * Real.logb 2 lam) (n X : ℕ) (h : lam ^ n < (X : ℝ) + 1) :
    n ≤ K₀ * (Nat.log 2 (X + 2) + 1) := by
  have h2 : (2 : ℝ) ≤ lam ^ K₀ := two_le_pow_of_one_le_mul_logb hlam hK₀
  have hX : (X : ℝ) + 2 < (2 : ℝ) ^ (Nat.log 2 (X + 2) + 1) := by
    have hnat := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) (X + 2)
    simp only [Nat.succ_eq_add_one] at hnat
    have h' : ((X + 2 : ℕ) : ℝ) < ((2 ^ (Nat.log 2 (X + 2) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at h'
    exact h'
  by_contra hcon
  have hcon' : K₀ * (Nat.log 2 (X + 2) + 1) ≤ n := by omega
  have hbig : (X : ℝ) + 1 < lam ^ n := by
    calc (X : ℝ) + 1 < (X : ℝ) + 2 := by linarith
      _ < (2 : ℝ) ^ (Nat.log 2 (X + 2) + 1) := hX
      _ ≤ lam ^ (K₀ * (Nat.log 2 (X + 2) + 1)) := by
            calc (2 : ℝ) ^ (Nat.log 2 (X + 2) + 1)
                ≤ (lam ^ K₀) ^ (Nat.log 2 (X + 2) + 1) :=
                  pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 _
              _ = lam ^ (K₀ * (Nat.log 2 (X + 2) + 1)) :=
                  (pow_mul lam K₀ (Nat.log 2 (X + 2) + 1)).symm
      _ ≤ lam ^ n := pow_le_pow_right₀ (le_of_lt hlam) hcon'
  linarith

theorem lacunaryFloorCount (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ K : ℕ, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
      (M X : ℕ), ((Finset.range M).filter (fun n => Nat.floor (a n) ≤ X)).card
        ≤ K * (Nat.log 2 (X + 2) + 1) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hc : 0 < Real.logb 2 (Λ : ℝ) := Real.logb_pos (by norm_num) hΛR
  obtain ⟨K₀, hK₀gr⟩ := exists_nat_gt ((Real.logb 2 (Λ : ℝ))⁻¹)
  have hK₀ : 1 ≤ (K₀ : ℝ) * Real.logb 2 (Λ : ℝ) := by
    have h1 : 1 < (K₀ : ℝ) * Real.logb 2 (Λ : ℝ) := by
      have h2 := mul_lt_mul_of_pos_right hK₀gr hc
      rwa [inv_mul_cancel₀ (ne_of_gt hc)] at h2
    linarith
  refine ⟨K₀ + 1, ?_⟩
  intro a ha ha1 M X
  have hpow : ∀ n : ℕ, (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    intro n
    have h' : ((Λ ^ n : ℝ≥0) : ℝ) ≤ ((a n : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.mpr (lowSmallSet_lacunary_pow_le ha ha1 n)
    rwa [NNReal.coe_pow] at h'
  have hsub : (Finset.range M).filter (fun n => Nat.floor (a n) ≤ X)
      ⊆ Finset.range (K₀ * (Nat.log 2 (X + 2) + 1) + 1) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨-, hnX⟩ := hn
    have haX : (a n : ℝ) < (X : ℝ) + 1 := by
      have h1 : (a n : ℝ) < ((Nat.floor (a n) : ℝ≥0) : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one (a n)
      have h2 : ((Nat.floor (a n) : ℝ≥0) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
      linarith
    have hlt : (Λ : ℝ) ^ n < (X : ℝ) + 1 := lt_of_le_of_lt (hpow n) haX
    have hb := rpow_lt_natLog_le_aux hΛR hK₀ n X hlt
    simp only [Finset.mem_range]
    omega
  calc ((Finset.range M).filter (fun n => Nat.floor (a n) ≤ X)).card
      ≤ (Finset.range (K₀ * (Nat.log 2 (X + 2) + 1) + 1)).card := Finset.card_le_card hsub
    _ = K₀ * (Nat.log 2 (X + 2) + 1) + 1 := Finset.card_range _
    _ ≤ (K₀ + 1) * (Nat.log 2 (X + 2) + 1) := by
        rw [add_mul, one_mul]
        exact Nat.add_le_add_left (by omega : 1 ≤ Nat.log 2 (X + 2) + 1) _

end Work.KMTPlan.A6
