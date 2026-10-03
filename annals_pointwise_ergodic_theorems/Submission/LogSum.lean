import ChallengeDeps
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Submission.Commons.Analysis.Sum.exists_bound_log2_floor_div_of_lacunary
import Submission.Commons.Analysis.Sum.summable_log2_div_of_lacunary

open scoped ENNReal NNReal

open Commons.Analysis

namespace Submission
namespace PointwiseErgodicTheorems

namespace LogSum



/-- For a `Λ`-lacunary sequence `x : ℕ → ℝ≥0` (`Λ > 1`, `x 0 ≥ 1`, `x (n+1) ≥ Λ * x n`) the
real series `∑ (log₂ ⌊x n⌋ + 1) / ⌊x n⌋` is summable.  The dominating sequence is geometric
with ratio `(√Λ)⁻¹ < 1`, obtained from the bound `⌊x n⌋ ≥ Λⁿ / 2` and `log₂ y + 1 ≤ K √y`. -/
private lemma summable_log2_floor_div_of_lacunary_aux (Λ : NNReal) (hΛ : 1 < Λ)
    (x : ℕ → NNReal) (hx0 : 1 ≤ x 0) (hx : ∀ n, Λ * x n ≤ x (n + 1)) :
    Summable (fun n => (((Nat.log2 (Nat.floor (x n)) : ℕ) : ℝ) + 1) / (Nat.floor (x n) : ℝ)) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := lt_trans one_pos hΛR
  have hmono : Monotone x := Commons.Analysis.Real.monotone_of_lacunary hΛ hx
  have hx1 : ∀ n, (1 : NNReal) ≤ x n := fun n => le_trans hx0 (hmono (Nat.zero_le n))
  have hx0R : (1 : ℝ) ≤ (x 0 : ℝ) := by exact_mod_cast hx0
  have hgeo : ∀ n, (Λ : ℝ) ^ n * (x 0 : ℝ) ≤ (x n : ℝ) := by
    intro n
    have h := Commons.Analysis.Real.le_pow_mul_of_lacunary hx n
    have h' : ((Λ ^ n * x 0 : NNReal) : ℝ) ≤ ((x n : NNReal) : ℝ) := by exact_mod_cast h
    rwa [NNReal.coe_mul, NNReal.coe_pow] at h'
  have hpow_le : ∀ n, (Λ : ℝ) ^ n ≤ (x n : ℝ) := by
    intro n
    have h1 : (Λ : ℝ) ^ n ≤ (Λ : ℝ) ^ n * (x 0 : ℝ) :=
      le_mul_of_one_le_right (pow_nonneg hΛpos.le n) hx0R
    exact le_trans h1 (hgeo n)
  have hfloor_le1 : ∀ n, 1 ≤ Nat.floor (x n) := fun n => by
    apply Nat.le_floor; simpa using hx1 n
  have hfloor_pos : ∀ n, (0 : ℝ) < (Nat.floor (x n) : ℝ) := by
    intro n
    have h1 : 0 < Nat.floor (x n) := by have := hfloor_le1 n; omega
    exact_mod_cast h1
  -- Growth: `Λⁿ / 2 ≤ ⌊x n⌋`.
  have hfloor_ge : ∀ n, (Λ : ℝ) ^ n / 2 ≤ (Nat.floor (x n) : ℝ) := by
    intro n
    have hlt : (x n : ℝ) < (Nat.floor (x n) : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (x n)
      exact_mod_cast this
    by_cases h2 : (Λ : ℝ) ^ n ≤ 2
    · have h1 : (1 : ℝ) ≤ (Nat.floor (x n) : ℝ) := by
        have : 1 ≤ Nat.floor (x n) := hfloor_le1 n
        exact_mod_cast this
      linarith
    · have h2' : 2 < (Λ : ℝ) ^ n := not_le.mp h2
      have hfn : (Λ : ℝ) ^ n - 1 ≤ (Nat.floor (x n) : ℝ) := by linarith [hpow_le n]
      linarith
  -- Pointwise geometric bound.
  have hbound : ∀ n, ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) / (Nat.floor (x n) : ℝ)
      ≤ (2 / Real.log 2 + 1) * Real.sqrt 2 * ((Real.sqrt (Λ : ℝ))⁻¹) ^ n := by
    intro n
    set y : ℝ := (Nat.floor (x n) : ℝ) with hy
    have hy1 : 1 ≤ y := by rw [hy]; exact_mod_cast hfloor_le1 n
    have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
    have hlog2b : (Nat.log2 (Nat.floor (x n)) : ℝ) ≤ Real.log y / Real.log 2 := by
      have h := Real.log2_le_logb (Nat.floor (x n))
      simpa [Real.logb, hy] using h
    have hstep : (Nat.log2 (Nat.floor (x n)) : ℝ) + 1 ≤ (2 / Real.log 2 + 1) * Real.sqrt y := by
      have h := Commons.Analysis.Sum.log_div_log_two_add_one_le hy1
      linarith [hlog2b, h]
    have hsqrtpos : 0 < Real.sqrt y := Real.sqrt_pos_of_pos hypos
    have hsqrtle : (Real.sqrt (Λ : ℝ)) ^ n / Real.sqrt 2 ≤ Real.sqrt y := by
      have h1 : (Λ : ℝ) ^ n / 2 ≤ y := by rw [hy]; exact hfloor_ge n
      have h2 : (Λ : ℝ) ^ n ≤ 2 * y := by linarith
      have h3 : Real.sqrt ((Λ : ℝ) ^ n) ≤ Real.sqrt (2 * y) := Real.sqrt_le_sqrt h2
      rw [Commons.Analysis.Sum.sqrt_pow_of_nonneg (Λ : ℝ) n hΛpos.le,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h3
      rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
      linarith
    have hnum : 0 ≤ (2 / Real.log 2 + 1 : ℝ) := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
    have hspos : 0 < (Real.sqrt (Λ : ℝ)) ^ n / Real.sqrt 2 := by positivity
    calc ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) / (Nat.floor (x n) : ℝ)
        = ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) / y := by rw [hy]
      _ ≤ ((2 / Real.log 2 + 1) * Real.sqrt y) / y :=
            div_le_div_of_nonneg_right hstep (le_of_lt hypos)
      _ = (2 / Real.log 2 + 1) / Real.sqrt y := by
            rw [div_eq_div_iff hypos.ne' hsqrtpos.ne']
            have hsq : Real.sqrt y * Real.sqrt y = y := by
              rw [← pow_two]; exact Real.sq_sqrt hypos.le
            nlinarith [hsq]
      _ ≤ (2 / Real.log 2 + 1) / ((Real.sqrt (Λ : ℝ)) ^ n / Real.sqrt 2) :=
            div_le_div_of_nonneg_left hnum hspos hsqrtle
      _ = (2 / Real.log 2 + 1) * Real.sqrt 2 * ((Real.sqrt (Λ : ℝ))⁻¹) ^ n := by
            rw [div_div_eq_mul_div, div_eq_mul_inv, inv_pow]
  have hsqrt_lt : (1 : ℝ) < Real.sqrt (Λ : ℝ) := by
    rw [← Real.sqrt_one]
    exact (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr hΛR
  have hr_nonneg : 0 ≤ (Real.sqrt (Λ : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr_lt_one : (Real.sqrt (Λ : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrt_lt
  have hgeom : Summable (fun n => ((Real.sqrt (Λ : ℝ))⁻¹) ^ n) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have hsumm : Summable
      (fun n => (2 / Real.log 2 + 1) * Real.sqrt 2 * ((Real.sqrt (Λ : ℝ))⁻¹) ^ n) :=
    hgeom.mul_left _
  exact Summable.of_nonneg_of_le
    (fun n => div_nonneg (by positivity) (le_of_lt (hfloor_pos n))) hbound hsumm

theorem tsum_ennreal_log2_floor_div_le_of_lacunary (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, ∀ (x : ℕ → NNReal), 1 ≤ x 0 → (∀ n, Λ * x n ≤ x (n + 1)) →
      ∑' n, ((((Nat.log2 (Nat.floor (x n)) + 1 : ℕ)) : ENNReal) * ((Nat.floor (x n) : ENNReal))⁻¹)
        ≤ (C : ENNReal) := by
  obtain ⟨C, hC⟩ := Commons.Analysis.Sum.exists_bound_log2_floor_div_of_lacunary Λ hΛ
  refine ⟨C, fun x hx0 hx => ?_⟩
  have hmono : Monotone x := Commons.Analysis.Real.monotone_of_lacunary hΛ hx
  have hx1 : ∀ n, (1 : NNReal) ≤ x n := fun n => le_trans hx0 (hmono (Nat.zero_le n))
  have ha : ∀ n, 1 ≤ Nat.floor (x n) := fun n => by
    apply Nat.le_floor; simpa using hx1 n
  have h_ofReal : ∀ n,
      ENNReal.ofReal ((((Nat.log2 (Nat.floor (x n)) : ℕ) : ℝ) + 1) / (Nat.floor (x n) : ℝ))
        = ((Nat.log2 (Nat.floor (x n)) + 1 : ℕ) : ENNReal)
            * ((Nat.floor (x n) : ENNReal))⁻¹ := by
    intro n
    have hpos : (0 : ℝ) < (Nat.floor (x n) : ℝ) := by
      have h1 : 0 < Nat.floor (x n) := by have := ha n; omega
      exact_mod_cast h1
    rw [show (((Nat.log2 (Nat.floor (x n)) : ℕ) : ℝ) + 1)
          = ((Nat.log2 (Nat.floor (x n)) + 1 : ℕ) : ℝ) by push_cast; ring]
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [div_eq_mul_inv]
  have hnonneg : ∀ n, 0 ≤ (((Nat.log2 (Nat.floor (x n)) : ℕ) : ℝ) + 1)
      / (Nat.floor (x n) : ℝ) :=
    fun n => div_nonneg (by positivity) (by positivity)
  have hsumm := summable_log2_floor_div_of_lacunary_aux Λ hΛ x hx0 hx
  calc ∑' n, ((((Nat.log2 (Nat.floor (x n)) + 1 : ℕ)) : ENNReal)
          * ((Nat.floor (x n) : ENNReal))⁻¹)
      = ∑' n, ENNReal.ofReal
          ((((Nat.log2 (Nat.floor (x n)) : ℕ) : ℝ) + 1) / (Nat.floor (x n) : ℝ)) :=
        tsum_congr (fun n => (h_ofReal n).symm)
    _ = ENNReal.ofReal
          (∑' n, (((Nat.log2 (Nat.floor (x n)) : ℕ) : ℝ) + 1) / (Nat.floor (x n) : ℝ)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hsumm).symm
    _ ≤ ENNReal.ofReal ((C : ℝ)) := ENNReal.ofReal_le_ofReal (hC x hx0 hx)
    _ = (C : ENNReal) := ENNReal.ofReal_coe_nnreal



end LogSum
end PointwiseErgodicTheorems
end Submission
