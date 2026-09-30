import Mathlib
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter Asymptotics
open scoped Topology

namespace Commons.NumberTheory.PrimeNumberTheorem

/-- For `A > 0` and any positive constant `C`, eventually `C · (log x)^A ≤ x^(1/2)`.

This is the standard domination of any fixed power of the logarithm by any positive
power of `x`, here `x^(1/2)`, a consequence of `log = o(x^s)` for `s > 0`. -/
private lemma eventually_const_mul_log_rpow_le_sqrt (C : ℝ) (hC : 0 < C) (A : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, C * (Real.log x) ^ A ≤ x ^ (1 / 2 : ℝ) := by
  have hlit : (fun x : ℝ => Real.log x ^ A) =o[Filter.atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop A (by norm_num)
  have hbound := hlit.bound (show 0 < 1 / C by positivity)
  filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlpow : 0 ≤ Real.log x ^ A := Real.rpow_nonneg hlognn A
  have hxhalf : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_of_nonneg hlpow, Real.norm_of_nonneg hxhalf] at hx
  calc C * Real.log x ^ A ≤ C * ((1 / C) * x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx (le_of_lt hC)
    _ = x ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, mul_one_div, div_self hC.ne', one_mul]

/-- `θ(x) = x + O_A(x / (log x)^A)` for every real `A > 0`: eventually the
Chebyshev `θ`-function differs from `x` by at most `x / (log x)^A`.

This is the classical Prime Number Theorem with a power-of-log error term
(de la Vallée Poussin).  We deduce it from the corresponding statement for the
second Chebyshev function `ψ` (`Commons.NumberTheory.Zeta.psi_sub_id_powLog_real`)
together with the elementary bound `ψ x - θ x = O(√x)`, since `√x` is eventually
absorbed by `x / (log x)^A`. -/
theorem theta_sub_id_powLog (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.theta x - x| ≤ x / (Real.log x) ^ A := by
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  obtain ⟨x₁, hx₁⟩ := Commons.NumberTheory.Zeta.psi_sub_id_powLog_real (A + 1) hA1
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set D : ℝ := max C₀ 0 + 1 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]; have := le_max_right C₀ 0; linarith
  have hC₀D : C₀ ≤ D := by
    rw [hDdef]; have := le_max_left C₀ 0; linarith
  have hdom : ∀ᶠ x : ℝ in Filter.atTop, (2 * D) * Real.log x ^ A ≤ x ^ (1 / 2 : ℝ) :=
    eventually_const_mul_log_rpow_le_sqrt (2 * D) (by linarith) A
  have hlogge : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 2)
  have hge1 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  apply Filter.eventually_atTop.mp
  filter_upwards [Filter.eventually_ge_atTop x₁, hdom, hlogge, hge1] with x hxle hdomx hlog2 hx1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlog2
  have hLpow : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlogpos A
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- The `ψ - θ` term and its domination by half the budget.
  have hpt : Chebyshev.psi x - Chebyshev.theta x ≤ D * Real.sqrt x := by
    refine (hC₀ x).trans ?_
    exact mul_le_mul_of_nonneg_right hC₀D hs
  have hsqrdom : D * Real.sqrt x ≤ (1 / 2) * (x / Real.log x ^ A) := by
    have hdom' : (2 * D) * Real.log x ^ A ≤ Real.sqrt x := by
      simpa only [Real.sqrt_eq_rpow] using hdomx
    have hstep : (2 * D) * Real.log x ^ A * Real.sqrt x ≤ x := by
      have := mul_le_mul_of_nonneg_right hdom' hs
      rwa [Real.mul_self_sqrt hx0.le] at this
    rw [show (1 / 2) * (x / Real.log x ^ A) = x / (2 * Real.log x ^ A) by ring]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hstep]
  -- The `ψ`-error term and its domination by half the budget.
  have hpsiabs : x / Real.log x ^ (A + 1) ≤ (1 / 2) * (x / Real.log x ^ A) := by
    have hsplit : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
      rw [Real.rpow_add hlogpos, Real.rpow_one]
    have hB : 0 ≤ x / Real.log x ^ A := by positivity
    have hLinv : 1 / Real.log x ≤ 1 / 2 := by
      rw [div_le_iff₀ hlogpos]; nlinarith [hlog2]
    have hxeq : x / (Real.log x ^ A * Real.log x) = (x / Real.log x ^ A) * (1 / Real.log x) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hsplit, hxeq, show (1 / 2) * (x / Real.log x ^ A) = (x / Real.log x ^ A) * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left hLinv hB
  -- Assemble.
  have htri : |Chebyshev.theta x - x| ≤
      (Chebyshev.psi x - Chebyshev.theta x) + |Chebyshev.psi x - x| := by
    have hle : Chebyshev.theta x - Chebyshev.psi x ≤ 0 := by
      linarith [Chebyshev.theta_le_psi x]
    have h := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
    rw [abs_of_nonpos hle] at h
    linarith
  have hpsi := hx₁ x hxle
  calc |Chebyshev.theta x - x|
      ≤ (Chebyshev.psi x - Chebyshev.theta x) + |Chebyshev.psi x - x| := htri
    _ ≤ D * Real.sqrt x + x / Real.log x ^ (A + 1) := by
        linarith [hpt, hpsi]
    _ ≤ (1 / 2) * (x / Real.log x ^ A) + (1 / 2) * (x / Real.log x ^ A) := by
        linarith [hsqrdom, hpsiabs]
    _ = x / Real.log x ^ A := by ring

end Commons.NumberTheory.PrimeNumberTheorem
