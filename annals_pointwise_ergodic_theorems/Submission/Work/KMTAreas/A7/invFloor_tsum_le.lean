import Mathlib
import Submission.Work.Analysis.EndVar.Sums

/-!
# Summability of the reciprocals of the floors along a lacunary sequence

Let `a : ℕ → ℝ≥0` be `Λ`-lacunary (`a (n+1) / a n > Λ`, `Λ > 1`) with `a n ≥ 1`.  Then
`a n ≥ Λ ^ n`, so `⌊a n⌋ ≥ Λ ^ n - 1` grows exponentially; consequently

  `∑' n, (⌊a n⌋ : ℝ)⁻¹ < ∞`,

with a total mass bounded uniformly over all such sequences `a`, depending only on `Λ`.

This is the elementary summability estimate used by the §5 bookkeeping of area `A7` (the error
terms of the lacunary-scale decomposition are indexed by the scales `⌊a n⌋`).
-/

namespace Work.KMTAreas.A7

open Filter

theorem invFloor_tsum_le (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ∧
      (∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ≤ C := by
  set r : ℝ := (Λ : ℝ) with hr
  have hr1 : 1 < r := by rw [hr]; exact_mod_cast hΛ
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hrinv_nonneg : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hrinv_lt_one : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr1
  -- a threshold beyond which `r ^ n ≥ 2`
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, (2 : ℝ) ≤ r ^ N := by
    have h : ∀ᶠ n in atTop, (2 : ℝ) ≤ r ^ n :=
      (tendsto_pow_atTop_atTop_of_one_lt hr1).eventually (eventually_ge_atTop 2)
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    exact ⟨N, hN N le_rfl⟩
  refine ⟨2 * r ^ N₀ * (1 - r⁻¹)⁻¹, ?_, ?_⟩
  · have h1 : 0 < 1 - r⁻¹ := by linarith
    have h2 : 0 ≤ 2 * r ^ N₀ := by have := pow_pos hr0 N₀; linarith
    exact mul_nonneg h2 (inv_nonneg.mpr h1.le)
  · intro a ha ha1
    -- `a n` dominates `r ^ n`
    have hpow : ∀ n, r ^ n ≤ (a n : ℝ) := by
      intro n
      have h := Work.Analysis.EndVar.pow_le_of_lacunary hΛ ha ha1 n
      rw [hr]
      exact_mod_cast h
    -- `⌊a n⌋ > r ^ n - 1`
    have hfloor_gt : ∀ n, r ^ n - 1 < ((Nat.floor (a n) : ℕ) : ℝ) := by
      intro n
      have h : (a n : ℝ) < ((Nat.floor (a n) : ℕ) : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (a n)
        exact_mod_cast this
      linarith [hpow n]
    -- `⌊a n⌋ ≥ 1`
    have hfloor_ge_one : ∀ n, (1 : ℝ) ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by
      intro n
      have h1n : ((1 : ℕ) : NNReal) ≤ a n := by simpa using ha1 n
      have := Nat.le_floor (α := NNReal) (a := a n) (n := 1) h1n
      exact_mod_cast this
    -- the pointwise bound against the geometric majorant
    have hterm_le : ∀ n, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ ≤ 2 * r ^ N₀ * (r⁻¹) ^ n := by
      intro n
      have hpos : 0 < ((Nat.floor (a n) : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one (hfloor_ge_one n)
      rcases le_or_gt n N₀ with hn | hn
      · -- small `n`: the term is at most `1`, and `r ^ N₀ * (r⁻¹) ^ n = r ^ (N₀ - n) ≥ 1`
        have h1 : (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr (hfloor_ge_one n)
        have h3 : r ^ N₀ * (r⁻¹) ^ n = r ^ (N₀ - n) := by
          rw [inv_pow, ← pow_sub₀ r hrne hn]
        calc (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ ≤ 1 := h1
          _ ≤ 2 * r ^ (N₀ - n) := by
              have := one_le_pow₀ hr1.le (n := N₀ - n); linarith
          _ = 2 * (r ^ N₀ * (r⁻¹) ^ n) := by rw [← h3]
          _ = 2 * r ^ N₀ * (r⁻¹) ^ n := by ring
      · -- large `n`: the term is at most `2 (r⁻¹) ^ n`, and `r ^ N₀ ≥ 1`
        have hrn : (2 : ℝ) ≤ r ^ n := le_trans hN₀ (pow_le_pow_right₀ hr1.le hn.le)
        have hfloor_ge : r ^ n / 2 ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by linarith [hfloor_gt n]
        have hpos2 : 0 < r ^ n / 2 := by positivity
        have h2 : (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ ≤ 2 * (r⁻¹) ^ n := by
          calc (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ ≤ (r ^ n / 2)⁻¹ := inv_anti₀ hpos2 hfloor_ge
            _ = 2 * (r ^ n)⁻¹ := by field_simp
            _ = 2 * (r⁻¹) ^ n := by rw [inv_pow]
        have hge : (1 : ℝ) ≤ r ^ N₀ := one_le_pow₀ hr1.le
        have ht : 0 ≤ (r⁻¹) ^ n := pow_nonneg hrinv_nonneg n
        have := mul_le_mul_of_nonneg_right hge ht
        calc (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ ≤ 2 * (r⁻¹) ^ n := h2
          _ ≤ 2 * r ^ N₀ * (r⁻¹) ^ n := by linarith
    have hM_summable : Summable (fun n : ℕ => 2 * r ^ N₀ * (r⁻¹) ^ n) := by
      have hg : Summable (fun n : ℕ => (r⁻¹) ^ n) :=
        summable_geometric_of_norm_lt_one (by
          rw [Real.norm_eq_abs, abs_of_nonneg hrinv_nonneg]; exact hrinv_lt_one)
      exact hg.mul_left (2 * r ^ N₀)
    have hterm_summable : Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) :=
      Summable.of_nonneg_of_le
        (fun n => inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le zero_lt_one (hfloor_ge_one n))))
        hterm_le hM_summable
    refine ⟨hterm_summable, ?_⟩
    have hle := Summable.tsum_le_tsum hterm_le hterm_summable hM_summable
    have hMtsum : (∑' n : ℕ, 2 * r ^ N₀ * (r⁻¹) ^ n) = 2 * r ^ N₀ * (1 - r⁻¹)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (ξ := r⁻¹) (by
        rw [Real.norm_eq_abs, abs_of_nonneg hrinv_nonneg]; exact hrinv_lt_one)]
    rw [hMtsum] at hle
    exact hle

end Work.KMTAreas.A7
