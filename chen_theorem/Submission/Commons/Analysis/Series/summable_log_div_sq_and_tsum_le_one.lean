import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SumIntegralComparisons

open Set MeasureTheory intervalIntegral Filter
open scoped Topology

namespace Commons.Analysis.Series

/-- The summand `log x / x ^ 2`. -/
noncomputable abbrev logDivSq (x : ℝ) : ℝ := Real.log x / x ^ 2

/-- `log x / x ^ 2` is antitone on `[3, ∞)`. -/
private lemma logDivSq_antitone : AntitoneOn logDivSq (Ici (3:ℝ)) := by
  have hanti : AntitoneOn (fun x : ℝ => Real.log x / x ^ (2:ℝ)) (Ici (Real.exp (2⁻¹))) :=
    Real.log_div_self_rpow_antitoneOn (a := 2) (by norm_num)
  have heq : (fun x : ℝ => Real.log x / x ^ (2:ℝ)) = (fun x : ℝ => Real.log x / x ^ 2) := by
    funext x
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [heq] at hanti
  have hexp : Real.exp (2⁻¹) ≤ 3 := by
    have h2 : Real.exp (2⁻¹) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpos : 0 < Real.exp (2⁻¹) := Real.exp_pos _
    nlinarith [Real.exp_one_lt_three, h2, hpos]
  have hsub : Ici (3:ℝ) ⊆ Ici (Real.exp (2⁻¹)) := fun x hx => by
    simp only [mem_Ici] at hx ⊢; linarith
  exact hanti.mono hsub

/-- The antiderivative of `log x / x ^ 2` is `-((log x + 1) / x)`. -/
private lemma hasDerivAt_neg_log_add_one_div (x : ℝ) (hx : x ∈ Ici (3:ℝ)) :
    HasDerivAt (fun y : ℝ => -((Real.log y + 1) / y)) (logDivSq x) x := by
  have hx3 : (3:ℝ) ≤ x := hx
  have hx0 : x ≠ 0 := by
    have : (0:ℝ) < x := by linarith
    positivity
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have h1 : HasDerivAt (fun y : ℝ => Real.log y + 1) x⁻¹ x := by
    simpa using hlog.add_const 1
  have h2 : HasDerivAt (fun y : ℝ => (Real.log y + 1) / y)
      ((x⁻¹ * x - (Real.log x + 1) * 1) / x ^ 2) x :=
    h1.div (hasDerivAt_id x) (by simpa using hx0)
  have h3 := h2.neg
  have hder : -((x⁻¹ * x - (Real.log x + 1) * 1) / x ^ 2) = logDivSq x := by
    rw [logDivSq]
    field_simp
    ring
  rwa [hder] at h3

/-- `log x / x ^ 2` is nonnegative on `(3, ∞)`. -/
private lemma logDivSq_nonneg : ∀ x ∈ Ioi (3:ℝ), 0 ≤ logDivSq x := by
  intro x hx
  have hx3 : (3:ℝ) < x := hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : (0:ℝ) < x := by linarith
  exact div_nonneg hlog (by positivity)

/-- The antiderivative tends to `0` at `+∞`. -/
private lemma tendsto_neg_log_add_one_div :
    Tendsto (fun y : ℝ => -((Real.log y + 1) / y)) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsum : Tendsto (fun y : ℝ => Real.log y / y + y⁻¹) atTop (𝓝 0) := by
    simpa using hlogdiv.add hinv
  have h2 : Tendsto (fun y : ℝ => (Real.log y + 1) / y) atTop (𝓝 0) := by
    simpa [add_div] using hsum
  simpa using h2.neg

/-- The improper integral of `log x / x ^ 2` over `(3, ∞)` equals `(log 3 + 1) / 3`. -/
private lemma integral_logDivSq :
    ∫ x in Ioi (3:ℝ), logDivSq x = (Real.log 3 + 1) / 3 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun y : ℝ => -((Real.log y + 1) / y)) (g' := logDivSq)
    hasDerivAt_neg_log_add_one_div logDivSq_nonneg tendsto_neg_log_add_one_div
  simpa using h

/-- `log x / x ^ 2` is integrable on `(3, ∞)`. -/
private lemma integrableOn_logDivSq : IntegrableOn logDivSq (Ioi (3:ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (g := fun y : ℝ => -((Real.log y + 1) / y)) (g' := logDivSq)
    hasDerivAt_neg_log_add_one_div logDivSq_nonneg tendsto_neg_log_add_one_div

theorem summable_log_div_sq_and_tsum_le_one :
    Summable (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) ∧
      (∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2) ≤ 1 := by
  have hsummable : Summable (fun n : ℕ => logDivSq n) :=
    AntitoneOn.summable_of_integrableOn_Ioi (N := 3)
      logDivSq_antitone integrableOn_logDivSq logDivSq_nonneg
  have hanti' : AntitoneOn logDivSq (Ici (((4:ℕ):ℝ) - 1)) := by
    rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num]; exact logDivSq_antitone
  have hint' : IntegrableOn logDivSq (Ioi (((4:ℕ):ℝ) - 1)) := by
    rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num]; exact integrableOn_logDivSq
  have hnonneg' : ∀ t ∈ Ioi (((4:ℕ):ℝ) - 1), 0 ≤ logDivSq t := by
    intro t ht
    rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num] at ht
    exact logDivSq_nonneg t ht
  have hb := AntitoneOn.abs_tsum_sub_sum_range_le_integral (f := logDivSq) (N := 4)
    (by norm_num) hanti' hint' hnonneg'
  rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num, integral_logDivSq] at hb
  have h1 : (∑' n : ℕ, logDivSq n) - ∑ n ∈ Finset.range 4, logDivSq n ≤
      (Real.log 3 + 1) / 3 :=
    le_trans (le_abs_self _) hb
  have hT : ∑ n ∈ Finset.range 4, logDivSq n = Real.log 2 / 4 + Real.log 3 / 9 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, logDivSq, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, Real.log_zero, Real.log_one, zero_div]
    norm_num
  rw [hT] at h1
  refine ⟨?_, ?_⟩
  · simpa [logDivSq] using hsummable
  · have h2 := Real.log_two_lt_d9
    have h3 := Real.log_three_lt_d9
    have hfin : (∑' n : ℕ, logDivSq n) ≤ 1 := by linarith
    simpa [logDivSq] using hfin

end Commons.Analysis.Series