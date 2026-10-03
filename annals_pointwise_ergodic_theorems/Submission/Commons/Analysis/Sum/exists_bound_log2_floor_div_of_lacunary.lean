import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Submission.Commons.Analysis.Sum.summable_succ_mul_inv_pow
import Submission.Commons.Analysis.Real.le_pow_mul_of_lacunary
import Submission.Commons.Analysis.Real.monotone_of_lacunary

open scoped NNReal
open Commons.Analysis.Real

namespace Commons.Analysis.Sum

/-- For `y ≥ 1` we have `Nat.log2 y + 1 ≤ y`. -/
private lemma nat_log2_add_one_le (y : ℕ) (hy : 1 ≤ y) : Nat.log2 y + 1 ≤ y := by
  have hy0 : y ≠ 0 := by omega
  have h1 : Nat.log2 y < y := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hy0).mpr Nat.lt_two_pow_self
  omega

/-- For reals `2 ≤ A ≤ y`, the function `t ↦ (log₂ t + 1) / t` is nonincreasing. -/
private lemma log_div_log_two_add_one_div_le {A y : ℝ} (hA : 2 ≤ A) (hy : A ≤ y) :
    (Real.log y / Real.log 2 + 1) / y ≤ (Real.log A / Real.log 2 + 1) / A := by
  have hApos : 0 < A := by linarith
  have hypos : 0 < y := lt_of_lt_of_le hApos hy
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_div_iff₀ hypos hApos]
  have key : A * (Real.log y + Real.log 2) ≤ y * (Real.log A + Real.log 2) := by
    set t : ℝ := y / A with ht
    have ht1 : 1 ≤ t := by rw [ht]; rw [le_div_iff₀ hApos]; simpa using hy
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hyt : y = t * A := by rw [ht]; field_simp
    have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h1 : Real.exp 1 < Real.exp (Real.log 4) := by
        rw [Real.exp_log (by norm_num : (0:ℝ) < 4)]
        linarith [Real.exp_one_lt_three]
      exact le_of_lt ((Real.exp_lt_exp).mp h1)
    have hlog2A_ge1 : 1 ≤ Real.log (2*A) := by
      have h4 : (4:ℝ) ≤ 2*A := by linarith
      exact le_trans hlog4 (Real.log_le_log (by norm_num) h4)
    have hlogt' : Real.log t ≤ (t-1) * Real.log (2*A) := by
      have h0 : 0 ≤ t - 1 := by linarith
      calc Real.log t ≤ t - 1 := hlogt
        _ = (t-1)*1 := by ring
        _ ≤ (t-1)*Real.log (2*A) := by gcongr
    have hmain : Real.log t + Real.log A + Real.log 2 ≤ t*(Real.log A + Real.log 2) := by
      have hlog2A : Real.log A + Real.log 2 = Real.log (2*A) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hApos)]; ring
      rw [hlog2A]
      nlinarith [hlogt']
    rw [hyt, Real.log_mul (ne_of_gt htpos) (ne_of_gt hApos)]
    calc A * (Real.log t + Real.log A + Real.log 2)
        ≤ A * (t * (Real.log A + Real.log 2)) := mul_le_mul_of_nonneg_left hmain (le_of_lt hApos)
      _ = t * A * (Real.log A + Real.log 2) := by ring
  have h1 : (Real.log y / Real.log 2 + 1) * A = A * (Real.log y + Real.log 2) / Real.log 2 := by
    field_simp
  have h2 : (Real.log A / Real.log 2 + 1) * y = y * (Real.log A + Real.log 2) / Real.log 2 := by
    field_simp
  rw [h1, h2]
  exact div_le_div_of_nonneg_right key (le_of_lt hlog2pos)

/-- Quantitative form of the `log₂` decay estimate: for `2 ≤ y`, `4 ≤ Λ^n` and `Λ^n / 2 ≤ y`,
the term `(log₂ y + 1) / y` is bounded by `2 · (log₂ Λ) · n · Λ⁻ⁿ`. -/
private lemma term_le {Λ : ℝ} (hΛ1 : 1 < Λ) {y : ℕ} {n : ℕ}
    (hy : Λ^n / 2 ≤ (y : ℝ)) (h4 : 4 ≤ Λ^n) :
    ((Nat.log2 y : ℝ) + 1) / (y : ℝ) ≤ 2 * (Real.log Λ / Real.log 2) * (n : ℝ) * (Λ⁻¹)^n := by
  have hΛpos : 0 < Λ := lt_trans one_pos hΛ1
  have hA2 : 2 ≤ Λ^n / 2 := by linarith
  have hypos : 0 < (y:ℝ) := by linarith
  have hylog : (Nat.log2 y : ℝ) + 1 ≤ Real.log (y:ℝ) / Real.log 2 + 1 := by
    have h := Real.log2_le_logb y
    simp only [Real.logb] at h
    linarith
  calc ((Nat.log2 y : ℝ) + 1) / (y:ℝ)
      ≤ (Real.log (y:ℝ) / Real.log 2 + 1) / (y:ℝ) :=
        div_le_div_of_nonneg_right hylog (le_of_lt hypos)
    _ ≤ (Real.log (Λ^n/2) / Real.log 2 + 1) / (Λ^n/2) := log_div_log_two_add_one_div_le hA2 hy
    _ = 2 * (Real.log Λ / Real.log 2) * (n:ℝ) * (Λ⁻¹)^n := by
        rw [Real.log_div (pow_ne_zero n (ne_of_gt hΛpos)) (by norm_num : (2:ℝ) ≠ 0),
          Real.log_pow, inv_pow]
        field_simp
        ring

theorem exists_bound_log2_floor_div_of_lacunary (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, ∀ (x : ℕ → NNReal), 1 ≤ x 0 → (∀ n, Λ * x n ≤ x (n + 1)) →
      ∑' n, (((Nat.log2 (Nat.floor (x n)) : ℕ) : ℝ) + 1) / (Nat.floor (x n) : ℝ)
        ≤ (C : ℝ) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛRpos : (0 : ℝ) < (Λ : ℝ) := lt_trans one_pos hΛR
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl_nonneg : (0:ℝ) ≤ Real.log (Λ:ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hΛR.le) hlog2pos.le
  have hr_nonneg : (0:ℝ) ≤ (Λ:ℝ)⁻¹ := inv_nonneg.mpr hΛRpos.le
  -- a threshold from which the lacunary growth is at least `4`
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (4:ℝ) hΛR
  have hK4 : (4:ℝ) ≤ (Λ:ℝ)^K := le_of_lt hK
  -- the dominating sequence `hfun n = 2 log₂Λ (n+1) Λ⁻ⁿ`
  let hfun : ℕ → ℝ := fun n => 2 * (Real.log (Λ:ℝ) / Real.log 2) * ((n:ℝ)+1) * ((Λ:ℝ)⁻¹)^n
  have hfun_nonneg : ∀ n, 0 ≤ hfun n := by
    intro n
    simp only [hfun]
    have h2 : 0 ≤ ((Λ:ℝ)⁻¹)^n := pow_nonneg hr_nonneg n
    have h3 : (0:ℝ) ≤ (n:ℝ)+1 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hl_nonneg) h3) h2
  have hsum : Summable hfun := by
    have h0 := summable_succ_mul_inv_pow hΛ
    have h1 : Summable
        (fun n : ℕ => (2 * (Real.log (Λ:ℝ) / Real.log 2)) * (((n:ℝ)+1) * ((Λ:ℝ)⁻¹)^n)) :=
      (h0.mul_left (2 * (Real.log (Λ:ℝ) / Real.log 2))).congr (fun n => by rw [inv_pow])
    exact h1.congr (fun n => by simp only [hfun]; ring)
  -- the actual dominating sequence: `1` for the finitely many small indices, `hfun` afterwards
  let gfun : ℕ → ℝ := fun n => (if n < K then (1:ℝ) else 0) + hfun n
  have hgsum : Summable gfun := by
    have hF : Summable (fun n : ℕ => (if n < K then (1:ℝ) else 0)) :=
      summable_of_ne_finset_zero (s := Finset.range K) (fun b hb => by
        simp only [Finset.mem_range, not_lt] at hb
        simp [hb])
    refine (hF.add hsum).congr (fun n => ?_)
    simp only [gfun]
  have hg_nonneg : 0 ≤ ∑' n, gfun n := tsum_nonneg (fun n => by
    simp only [gfun]
    have h1 : (0:ℝ) ≤ (if n < K then (1:ℝ) else 0) := by split <;> norm_num
    linarith [hfun_nonneg n])
  refine ⟨(∑' n, gfun n).toNNReal, ?_⟩
  intro x hx0 hx
  rw [Real.coe_toNNReal _ hg_nonneg]
  have hx0R : (1:ℝ) ≤ (x 0 : ℝ) := by exact_mod_cast hx0
  have hmono : Monotone x := monotone_of_lacunary hΛ hx
  have hx1 : ∀ n, (1:NNReal) ≤ x n := fun n => le_trans hx0 (hmono (Nat.zero_le n))
  have hgeom : ∀ n, (Λ:ℝ)^n * (x 0 : ℝ) ≤ (x n : ℝ) := by
    intro n
    have h := le_pow_mul_of_lacunary hx n
    have h' : ((Λ ^ n * x 0 : NNReal) : ℝ) ≤ ((x n : NNReal) : ℝ) := by exact_mod_cast h
    rwa [NNReal.coe_mul, NNReal.coe_pow] at h'
  have hpow_le : ∀ n, (Λ:ℝ)^n ≤ (x n : ℝ) := by
    intro n
    have h1 : (Λ:ℝ)^n ≤ (Λ:ℝ)^n * (x 0 : ℝ) :=
      le_mul_of_one_le_right (pow_nonneg hΛRpos.le n) hx0R
    exact le_trans h1 (hgeom n)
  have hfloor_pos : ∀ n, (0:ℝ) < (Nat.floor (x n) : ℝ) := by
    intro n
    have h1 : 1 ≤ Nat.floor (x n) := by apply Nat.le_floor; simpa using hx1 n
    exact_mod_cast (by omega : 0 < Nat.floor (x n))
  -- pointwise comparison with the dominating sequence
  have hterm_le : ∀ n,
      ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) / (Nat.floor (x n) : ℝ) ≤ gfun n := by
    intro n
    by_cases hn : n < K
    · have h1 : 1 ≤ Nat.floor (x n) := by apply Nat.le_floor; simpa using hx1 n
      have hle : Nat.log2 (Nat.floor (x n)) + 1 ≤ Nat.floor (x n) := nat_log2_add_one_le _ h1
      have hleR : ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) ≤ (Nat.floor (x n) : ℝ) := by
        exact_mod_cast hle
      have hT1 : ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) / (Nat.floor (x n) : ℝ) ≤ 1 := by
        rw [div_le_one (hfloor_pos n)]; exact hleR
      have hg1 : (1:ℝ) ≤ gfun n := by
        simp only [gfun, if_pos hn]
        linarith [hfun_nonneg n]
      linarith
    · have hKn : K ≤ n := by omega
      have h4n : (4:ℝ) ≤ (Λ:ℝ)^n := le_trans hK4 (pow_le_pow_right₀ hΛR.le hKn)
      have hAy : (Λ:ℝ)^n / 2 ≤ (Nat.floor (x n) : ℝ) := by
        have hlt : (x n : ℝ) < (Nat.floor (x n) : ℝ) + 1 := by
          have := Nat.lt_floor_add_one (x n)
          exact_mod_cast this
        have h2 : (2:ℝ) ≤ (Λ:ℝ)^n := le_trans (by norm_num) h4n
        linarith [hpow_le n]
      have hmain := term_le hΛR hAy h4n
      have hle_h : 2 * (Real.log (Λ:ℝ) / Real.log 2) * (n:ℝ) * ((Λ:ℝ)⁻¹)^n ≤ hfun n := by
        simp only [hfun]
        have hrpow : 0 ≤ ((Λ:ℝ)⁻¹)^n := pow_nonneg hr_nonneg n
        have hnle : (n:ℝ) ≤ (n:ℝ)+1 := by linarith
        have hcoef : 0 ≤ 2 * (Real.log (Λ:ℝ) / Real.log 2) := by linarith [hl_nonneg]
        calc 2 * (Real.log (Λ:ℝ) / Real.log 2) * (n:ℝ) * ((Λ:ℝ)⁻¹)^n
            = (2 * (Real.log (Λ:ℝ) / Real.log 2)) * ((n:ℝ) * ((Λ:ℝ)⁻¹)^n) := by ring
          _ ≤ (2 * (Real.log (Λ:ℝ) / Real.log 2)) * (((n:ℝ)+1) * ((Λ:ℝ)⁻¹)^n) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnle hrpow) hcoef
          _ = 2 * (Real.log (Λ:ℝ) / Real.log 2) * ((n:ℝ)+1) * ((Λ:ℝ)⁻¹)^n := by ring
      simp only [gfun, if_neg hn, zero_add]
      exact le_trans hmain hle_h
  have hT_nonneg : ∀ n, 0 ≤ ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) / (Nat.floor (x n) : ℝ) := by
    intro n
    exact div_nonneg (by positivity) (le_of_lt (hfloor_pos n))
  have Tsum : Summable
      (fun n => ((Nat.log2 (Nat.floor (x n)) : ℝ) + 1) / (Nat.floor (x n) : ℝ)) :=
    Summable.of_nonneg_of_le hT_nonneg hterm_le hgsum
  exact Summable.tsum_le_tsum hterm_le Tsum hgsum

end Commons.Analysis.Sum