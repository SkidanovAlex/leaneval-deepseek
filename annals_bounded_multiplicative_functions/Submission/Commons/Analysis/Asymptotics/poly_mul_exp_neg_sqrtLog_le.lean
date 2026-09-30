import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter
open scoped Topology

namespace Commons.Analysis.Asymptotics

theorem poly_mul_exp_neg_sqrtLog_le (a : ℝ) (ha : 0 < a) (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop,
      C * (Real.log x) ^ k * Real.exp (-a * Real.sqrt (Real.log x)) ≤
        Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
  have ha2 : (0 : ℝ) < a / 2 := by linarith
  -- The auxiliary function `u ↦ u ^ (2k) * exp (-(a/2) * u)` tends to `0` at `+∞`.
  have hg : Filter.Tendsto
      (fun u : ℝ => u ^ (((2 * k : ℕ) : ℝ)) * Real.exp (-(a / 2) * u))
      Filter.atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (((2 * k : ℕ) : ℝ)) (a / 2) ha2
  -- Multiplying by the constant `C` keeps the limit `0`.
  have hgC : Filter.Tendsto
      (fun u : ℝ => C * (u ^ (((2 * k : ℕ) : ℝ)) * Real.exp (-(a / 2) * u)))
      Filter.atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hg
  -- Compose with `x ↦ sqrt (log x)`, which tends to `+∞`.
  have hcomp : Filter.Tendsto
      (fun x : ℝ => C * ((Real.sqrt (Real.log x)) ^ (((2 * k : ℕ) : ℝ)) *
        Real.exp (-(a / 2) * Real.sqrt (Real.log x))))
      Filter.atTop (𝓝 0) :=
    hgC.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  -- Hence eventually the quantity is `≤ 1`.
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      C * ((Real.sqrt (Real.log x)) ^ (((2 * k : ℕ) : ℝ)) *
        Real.exp (-(a / 2) * Real.sqrt (Real.log x))) ≤ 1 :=
    hcomp.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  have hlog : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 0
  filter_upwards [hev, hlog] with x hx1 hx2
  -- Rewrite the `sqrt` power as a `log` power using `log x ≥ 0`.
  have hpow : (Real.sqrt (Real.log x)) ^ (((2 * k : ℕ) : ℝ)) = (Real.log x) ^ k := by
    rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt hx2]
  have hT : C * (Real.log x) ^ k * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) ≤ 1 := by
    rw [hpow] at hx1
    simpa only [mul_assoc] using hx1
  have he : 0 < Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := Real.exp_pos _
  have hexp : Real.exp (-a * Real.sqrt (Real.log x)) =
      Real.exp (-(a / 2) * Real.sqrt (Real.log x)) *
        Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  have h := mul_le_mul_of_nonneg_right hT he.le
  nlinarith [h]

end Commons.Analysis.Asymptotics