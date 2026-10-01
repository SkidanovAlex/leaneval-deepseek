import Mathlib

namespace Work.LinnikAreas.Density4

open MeasureTheory intervalIntegral Finset

/-- Derivative of `t ↦ log (t / y)` at a nonzero point. -/
private lemma deriv_log_div_eq (y t : ℝ) (hy : y ≠ 0) (ht : t ≠ 0) :
    deriv (fun s : ℝ => Real.log (s / y)) t = 1 / t := by
  have h1 : HasDerivAt (fun s : ℝ => s / y) (1 / y) t := (hasDerivAt_id t).div_const y
  have h2 : HasDerivAt (fun s : ℝ => Real.log (s / y)) ((1 / y) / (t / y)) t :=
    h1.log (div_ne_zero ht hy)
  rw [h2.deriv]
  field_simp

/-- `θ` expressed as a sum over `Icc 0 ⌊t⌋₊` with an `if`-predicate. -/
private lemma theta_eq_sum_ite (t : ℝ) :
    (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then (Real.log k : ℝ) else 0))
      = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]

/-- The prime-indexed set of the theorem, rewritten as `Ioc ⌊y⌋₊ ⌊x⌋₊` filtered by primality. -/
private lemma filter_eq_Ioc {y x : ℝ} (hy : 0 ≤ y) :
    (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ))
      = (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp, hpy⟩
    exact ⟨⟨(Nat.floor_lt hy).mpr hpy, h2⟩, hp⟩
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨hp.one_le, h2⟩, hp, (Nat.floor_lt hy).mp h1⟩

theorem prime_log_sum_repr {y x : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
        Real.log (p : ℝ) * Real.log ((p : ℝ) / y))
      = Chebyshev.theta (⌊x⌋₊) * Real.log (x / y)
        - ∫ t in y..x, Chebyshev.theta t / t := by
  have hy0 : 0 ≤ y := by linarith
  have hyne : y ≠ 0 := by linarith
  -- differentiability of `t ↦ log (t / y)` on `[y,x]`
  have hdiff : ∀ t ∈ Set.Icc y x,
      DifferentiableAt ℝ (fun s : ℝ => Real.log (s / y)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun s : ℝ => s / y) (1 / y) t := (hasDerivAt_id t).div_const y
    exact (h1.log (div_ne_zero ht0 hyne)).differentiableAt
  -- integrability of the derivative
  have hint : IntegrableOn (deriv (fun s : ℝ => Real.log (s / y))) (Set.Icc y x) volume := by
    have h1 : IntegrableOn (fun t : ℝ => 1 / t) (Set.Icc y x) volume := by
      refine ContinuousOn.integrableOn_Icc ?_
      refine ContinuousOn.div continuousOn_const continuousOn_id ?_
      intro t ht
      have : (1 : ℝ) ≤ t := le_trans hy ht.1
      linarith
    refine h1.congr_fun ?_ measurableSet_Icc
    intro t ht
    rw [deriv_log_div_eq y t hyne (by linarith [ht.1] : t ≠ 0)]
  -- Abel summation
  have habel := sum_mul_eq_sub_sub_integral_mul
      (fun k : ℕ => if k.Prime then (Real.log k : ℝ) else 0)
      (f := fun t : ℝ => Real.log (t / y)) hy0 hyx hdiff hint
  beta_reduce at habel
  -- rewrite the target sum into the form the Abel identity works with
  have hkey : (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
        Real.log (p : ℝ) * Real.log ((p : ℝ) / y))
      = ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊,
          Real.log ((k : ℝ) / y) * (if k.Prime then (Real.log k : ℝ) else 0) := by
    rw [filter_eq_Ioc hy0, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.Prime <;> simp [h, mul_comm]
  -- the value of the `θ`-sums appearing in the Abel identity
  have hsumx : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (if k.Prime then (Real.log k : ℝ) else 0))
      = Chebyshev.theta ⌊x⌋₊ := by
    rw [theta_eq_sum_ite x]
    exact Chebyshev.theta_eq_theta_coe_floor x
  -- identify the integral in the Abel identity
  have hint_eq : (∫ t in Set.Ioc y x, deriv (fun s : ℝ => Real.log (s / y)) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then (Real.log k : ℝ) else 0))
      = ∫ t in y..x, Chebyshev.theta t / t := by
    rw [intervalIntegral.integral_of_le hyx]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [Set.mem_Ioc] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    rw [deriv_log_div_eq y t hyne ht0, theta_eq_sum_ite t]
    rw [one_div, div_eq_mul_inv, mul_comm]
  rw [hkey, habel, hsumx, theta_eq_sum_ite y, div_self hyne, Real.log_one, zero_mul, sub_zero,
    hint_eq]
  ring

end Work.LinnikAreas.Density4
