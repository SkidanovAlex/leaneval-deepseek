import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Commons.Analysis.Sum

/-- For `y ≥ 1`, `Real.log y ≤ 2 * √y`. -/
lemma log_le_two_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos_of_pos hypos
  have hlog : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 := Real.log_le_sub_one_of_pos hspos
  have key : Real.log y = 2 * Real.log (Real.sqrt y) := by
    have h : Real.log ((Real.sqrt y) ^ 2) = (2 : ℝ) * Real.log (Real.sqrt y) := Real.log_pow _ 2
    rwa [Real.sq_sqrt hypos.le] at h
  rw [key]; linarith

/-- For `y ≥ 1`, `Real.log y / Real.log 2 + 1 ≤ (2 / Real.log 2 + 1) * √y`. -/
lemma log_div_log_two_add_one_le {y : ℝ} (hy : 1 ≤ y) :
    Real.log y / Real.log 2 + 1 ≤ (2 / Real.log 2 + 1) * Real.sqrt y := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log y ≤ 2 * Real.sqrt y := log_le_two_sqrt hy
  have h2 : Real.log y / Real.log 2 ≤ 2 * Real.sqrt y / Real.log 2 := by
    gcongr
  have h3 : (1 : ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  have hdecomp : (2 / Real.log 2 + 1) * Real.sqrt y = 2 * Real.sqrt y / Real.log 2 + Real.sqrt y := by
    ring
  rw [hdecomp]
  linarith

/-- `√(a ^ n) = (√a) ^ n` for `a ≥ 0`. -/
lemma sqrt_pow_of_nonneg (a : ℝ) (n : ℕ) (ha : 0 ≤ a) :
    Real.sqrt (a ^ n) = (Real.sqrt a) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg ha k) a, ih, pow_succ]

/-- For a `Λ`-lacunary sequence `x` of positive naturals (`Λ > 1`, `x (n+1) ≥ Λ * x n`), the
    series `∑ (log₂ (x n) + 1) / x n` converges.  This bounds the `O(∑_{N ∈ D} (log₂ N + 1) / N)`
    error term in the dyadic telescoping reduction of the long variational ergodic theorem. -/
theorem summable_log2_div_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {x : ℕ → ℕ} (hx0 : 1 ≤ x 0)
    (hx : ∀ n, Λ * x n ≤ x (n + 1)) :
    Summable (fun n => ((Nat.log2 (x n) : ℝ) + 1) / (x n : ℝ)) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := lt_trans one_pos hΛR
  -- real form of the lacunarity hypothesis
  have hxR : ∀ n, (Λ : ℝ) * (x n : ℝ) ≤ (x (n + 1) : ℝ) := by
    intro n
    exact_mod_cast hx n
  -- geometric lower bound
  have hgeo : ∀ n, (Λ : ℝ) ^ n * (x 0 : ℝ) ≤ (x n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hstep : (Λ : ℝ) * ((Λ : ℝ) ^ k * (x 0 : ℝ)) ≤ (Λ : ℝ) * (x k : ℝ) :=
          mul_le_mul_of_nonneg_left ih (le_of_lt hΛpos)
        calc (Λ : ℝ) ^ (k + 1) * (x 0 : ℝ)
            = (Λ : ℝ) * ((Λ : ℝ) ^ k * (x 0 : ℝ)) := by ring
          _ ≤ (Λ : ℝ) * (x k : ℝ) := hstep
          _ ≤ (x (k + 1) : ℝ) := hxR k
  have hx0R : (1 : ℝ) ≤ (x 0 : ℝ) := by exact_mod_cast hx0
  have hx1 : ∀ n, (1 : ℝ) ≤ (x n : ℝ) := by
    intro n
    have hpow : (1 : ℝ) ≤ (Λ : ℝ) ^ n := one_le_pow₀ (le_of_lt hΛR)
    have hmul : (1 : ℝ) ≤ (Λ : ℝ) ^ n * (x 0 : ℝ) := by
      have h := mul_le_mul hpow hx0R (by norm_num : (0 : ℝ) ≤ 1)
        (pow_nonneg (le_of_lt hΛpos) n)
      simpa using h
    exact le_trans hmul (hgeo n)
  have hxpos : ∀ n, (0 : ℝ) < (x n : ℝ) := fun n => lt_of_lt_of_le one_pos (hx1 n)
  -- pointwise bound
  have hbound : ∀ n, ((Nat.log2 (x n) : ℝ) + 1) / (x n : ℝ)
      ≤ (2 / Real.log 2 + 1) * ((Real.sqrt (Λ : ℝ))⁻¹) ^ n := by
    intro n
    set y : ℝ := (x n : ℝ) with hy
    have hy1 : 1 ≤ y := by rw [hy]; exact hx1 n
    have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
    have hlog2b : (Nat.log2 (x n) : ℝ) ≤ Real.log y / Real.log 2 := by
      have h := Real.log2_le_logb (x n)
      simpa [Real.logb, hy] using h
    have hstep : (Nat.log2 (x n) : ℝ) + 1 ≤ (2 / Real.log 2 + 1) * Real.sqrt y := by
      have h := log_div_log_two_add_one_le hy1
      linarith [hlog2b, h]
    have hsqrtpos : 0 < Real.sqrt y := Real.sqrt_pos_of_pos hypos
    -- growth gives √((Λ)^n) ≤ √y
    have hpowle : (Λ : ℝ) ^ n ≤ y := by
      rw [hy]
      have h1 : (Λ : ℝ) ^ n ≤ (Λ : ℝ) ^ n * (x 0 : ℝ) :=
        le_mul_of_one_le_right (pow_nonneg (le_of_lt hΛpos) n) hx0R
      exact le_trans h1 (hgeo n)
    have hsqrtle : (Real.sqrt (Λ : ℝ)) ^ n ≤ Real.sqrt y := by
      have := Real.sqrt_le_sqrt hpowle
      rwa [sqrt_pow_of_nonneg (Λ : ℝ) n (le_of_lt hΛpos)] at this
    have hnum_nonneg : 0 ≤ (2 / Real.log 2 + 1 : ℝ) := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    have hspos : 0 < (Real.sqrt (Λ : ℝ)) ^ n := pow_pos (Real.sqrt_pos_of_pos hΛpos) n
    calc ((Nat.log2 (x n) : ℝ) + 1) / (x n : ℝ)
        = ((Nat.log2 (x n) : ℝ) + 1) / y := by rw [hy]
      _ ≤ ((2 / Real.log 2 + 1) * Real.sqrt y) / y :=
            div_le_div_of_nonneg_right hstep (le_of_lt hypos)
      _ = (2 / Real.log 2 + 1) / Real.sqrt y := by
            rw [div_eq_div_iff hypos.ne' hsqrtpos.ne']
            have hsq : Real.sqrt y * Real.sqrt y = y := by
              rw [← pow_two]; exact Real.sq_sqrt hypos.le
            nlinarith [hsq]
      _ ≤ (2 / Real.log 2 + 1) / (Real.sqrt (Λ : ℝ)) ^ n :=
            div_le_div_of_nonneg_left hnum_nonneg hspos hsqrtle
      _ = (2 / Real.log 2 + 1) * ((Real.sqrt (Λ : ℝ))⁻¹) ^ n := by rw [div_eq_mul_inv, inv_pow]
  -- summability of the dominating geometric series
  have hsqrt_lt : (1 : ℝ) < Real.sqrt (Λ : ℝ) := by
    rw [← Real.sqrt_one]
    exact (Real.sqrt_lt_sqrt_iff (show (0 : ℝ) ≤ 1 by norm_num)).mpr hΛR
  have hr_nonneg : 0 ≤ (Real.sqrt (Λ : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr_lt_one : (Real.sqrt (Λ : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrt_lt
  have hsummable_geom : Summable (fun n => ((Real.sqrt (Λ : ℝ))⁻¹) ^ n) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have hsummable : Summable (fun n => (2 / Real.log 2 + 1) * ((Real.sqrt (Λ : ℝ))⁻¹) ^ n) :=
    hsummable_geom.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) hbound hsummable
  apply div_nonneg
  · positivity
  · exact le_of_lt (hxpos n)

end Commons.Analysis.Sum