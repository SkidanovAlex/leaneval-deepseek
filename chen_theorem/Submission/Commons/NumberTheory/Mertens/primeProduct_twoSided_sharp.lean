import Mathlib
import Submission.Commons.NumberTheory.Mertens.prod_one_sub_inv_prime_asymptotic
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto

namespace Commons.NumberTheory.Mertens

open scoped BigOperators
open Filter Finset

noncomputable section

/-- The Mertens product equals `exp (-logRatioSum x)`, where
`logRatioSum x = ∑_{p ≤ x} log (p/(p-1))`. -/
private lemma prod_eq_exp_neg_logRatioSum (x : ℝ) :
    (∏ p ∈ (⌊x⌋₊).primesLE, (1 - 1 / (p : ℝ))) = Real.exp (-logRatioSum x) := by
  have hfac : ∀ p ∈ (⌊x⌋₊).primesLE,
      (1 - 1 / (p : ℝ)) = ((p : ℝ) / ((p : ℝ) - 1))⁻¹ := by
    intro p hp
    have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [inv_div]
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_inv_distrib]
  have hexp : (∏ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) / ((p : ℝ) - 1)))
      = Real.exp (logRatioSum x) := by
    rw [logRatioSum, Real.exp_sum]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact (Real.exp_log (by positivity)).symm
  rw [hexp, Real.exp_neg]

/-- The product `∏_{p ≤ x} (1 - 1/p)` times `log x` tends to `exp (-γ)`. -/
private lemma prod_mul_log_tendsto :
    Tendsto (fun x : ℝ => (∏ p ∈ (⌊x⌋₊).primesLE, (1 - 1 / (p : ℝ))) * Real.log x)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hγ : Tendsto (fun x : ℝ => logRatioSum x - Real.log (Real.log x)) atTop
      (nhds Real.eulerMascheroniConstant) := sum_log_prime_ratio_real_tendsto
  have h1 : Tendsto (fun x : ℝ => -(logRatioSum x - Real.log (Real.log x))) atTop
      (nhds (-Real.eulerMascheroniConstant)) := hγ.neg
  have h2 : Tendsto (fun x : ℝ => Real.exp (-(logRatioSum x - Real.log (Real.log x))))
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
    (Real.continuous_exp.tendsto (-Real.eulerMascheroniConstant)).comp h1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [prod_eq_exp_neg_logRatioSum,
    show -(logRatioSum x - Real.log (Real.log x)) = -logRatioSum x + Real.log (Real.log x)
      by ring,
    Real.exp_add, Real.exp_log (Real.log_pos hx)]

/-- If the product times `log` converges to `C₀` at rate `D / log`, then the limit is
`C₀` (a squeeze argument). -/
private lemma prod_mul_log_tendsto_of_bound {C₀ D : ℝ}
    (hD : ∀ y : ℝ, 2 ≤ y →
      |(∏ p ∈ (⌊y⌋₊).primesLE, (1 - 1 / (p : ℝ))) * Real.log y - C₀|
        ≤ D / Real.log y) :
    Tendsto (fun x : ℝ => (∏ p ∈ (⌊x⌋₊).primesLE, (1 - 1 / (p : ℝ))) * Real.log x)
      atTop (nhds C₀) := by
  have hDinv : Tendsto (fun x : ℝ => D / Real.log x) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  have hnorm : Tendsto
      (fun x : ℝ => ‖(∏ p ∈ (⌊x⌋₊).primesLE, (1 - 1 / (p : ℝ))) * Real.log x - C₀‖)
      atTop (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _)) ?_ hDinv
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [Real.norm_eq_abs]
    exact hD x hx
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

open scoped BigOperators in
theorem primeProduct_twoSided_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 100 ≤ y →
      |(∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)) * Real.log (y : ℝ) - Real.exp (-Real.eulerMascheroniConstant)|
        ≤ C / Real.log (y : ℝ) := by
  obtain ⟨C₀, hC₀pos, hAsym⟩ := prod_one_sub_inv_prime_asymptotic
  obtain ⟨D, hDpos, hD⟩ := hAsym 1 (by norm_num)
  have hD' : ∀ y : ℝ, 2 ≤ y →
      |(∏ p ∈ (⌊y⌋₊).primesLE, (1 - 1 / (p : ℝ))) * Real.log y - C₀|
        ≤ D / Real.log y := by
    intro y hy
    simpa [Real.rpow_one] using hD y hy
  -- `C₀ = exp (-γ)` by uniqueness of the limit
  have hlimC : Tendsto
      (fun x : ℝ => (∏ p ∈ (⌊x⌋₊).primesLE, (1 - 1 / (p : ℝ))) * Real.log x)
      atTop (nhds C₀) := prod_mul_log_tendsto_of_bound hD'
  have hC₀eq : C₀ = Real.exp (-Real.eulerMascheroniConstant) :=
    tendsto_nhds_unique hlimC prod_mul_log_tendsto
  refine ⟨max D 1, lt_max_of_lt_left hDpos, ?_⟩
  intro y hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 2 ≤ y)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have h := hD' (y : ℝ) hy2
  rw [Nat.floor_natCast] at h
  have h' : |(∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)) * Real.log (y : ℝ)
      - Real.exp (-Real.eulerMascheroniConstant)| ≤ D / Real.log (y : ℝ) := by
    rw [← hC₀eq]
    simpa [one_div] using h
  exact le_trans h' (div_le_div_of_nonneg_right (le_max_left D 1) (le_of_lt hlogy))

end

end Commons.NumberTheory.Mertens
