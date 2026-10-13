import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EComparison.intervalIntegral_eq_setIntegral_indicator
import Submission.Work.FTS.StrongEps.EComparison.intervalIntegral_secondDeriv_mul_sub
import Submission.Work.FTS.StrongEps.EComparison.integrable_fubiniWeightZ_integrand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- **Fubini/weight identity for the weighted primitive of `W`.**

For `0 < a < b`, `W` locally integrable on `(0,∞)` and a test function `ρ` compactly supported
inside `(a,b)`,
```
∫_a^b ρ''(t) * ∫_t^b (z - t) W z dz dt = ∫_a^b W z * ρ z dz .
```
The double integral runs over the triangle `a ≤ t ≤ z ≤ b`, so Fubini rewrites it as an integral
in `z` whose inner `t`-integral is `∫_a^z ρ''(t)(z-t)dt = ρ z` (second-order Taylor formula,
using that `ρ` vanishes near `a`).

Mechanism: replace `∫_t^b (z-t)W z dz` by the integral over the fixed box `Icc a b` of the
truncated function `(z-t)W z·1_{t ≤ z}` (`intervalIntegral_eq_setIntegral_indicator`), pull out
the constant `ρ'' t`, apply Fubini on the box
(`MeasureTheory.integral_integral_swap`, whose integrability side condition is
`integrable_fubiniWeightZ_integrand`), and evaluate the inner integral in `t` at fixed `z`
(`intervalIntegral_secondDeriv_mul_sub`), together with the identification of the interval
integrals `a..b` with the box integrals. -/
theorem FubiniWeightZ {a b : ℝ} {W ρ : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) (ha : 0 < a) (hab : a < b)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ)
    (hsupp : tsupport ρ ⊆ Set.Ioo a b) :
    (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ z in a..b, W z * ρ z := by
  have hab' : a ≤ b := hab.le
  -- `ρ` vanishes on a neighbourhood of `a`
  have hρa_ev : ρ =ᶠ[nhds a] 0 := by
    rw [← notMem_tsupport_iff_eventuallyEq]
    refine fun hmem => absurd (hsupp hmem) ?_
    rw [Set.mem_Ioo]
    exact fun h => absurd h.1 (lt_irrefl a)
  -- the joint integrand on the box is product-integrable
  have hfun : (Function.uncurry (fun t z : ℝ =>
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0)))
      = fun p : ℝ × ℝ => deriv (deriv ρ) p.1 *
        (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0) := by
    funext p
    rfl
  have hInt : MeasureTheory.Integrable
      (Function.uncurry (fun t z : ℝ =>
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))) := by
    rw [hfun]
    exact integrable_fubiniWeightZ_integrand hW ha hab hρ
  -- the reduction to the box
  have hL : (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ t in Set.Icc a b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z) :=
    (intervalIntegral.integral_of_le hab').trans (integral_Icc_eq_integral_Ioc).symm
  -- rewrite the `z`-integral as an integral over the box
  have key1 : (∫ t in Set.Icc a b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ t in Set.Icc a b, ∫ z in Set.Icc a b,
          deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have h1 : (∫ z in Set.Icc a b, deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
        = deriv (deriv ρ) t * ∫ z in Set.Icc a b, (if t ≤ z then (z - t) * W z else 0) :=
      integral_const_mul (deriv (deriv ρ) t) _
    rw [h1, ← intervalIntegral_eq_setIntegral_indicator ht.1 ht.2 (fun z => (z - t) * W z)]
  -- Fubini
  have key2 : (∫ t in Set.Icc a b, ∫ z in Set.Icc a b,
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
      = ∫ z in Set.Icc a b, ∫ t in Set.Icc a b,
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0) :=
    integral_integral_swap (μ := volume.restrict (Set.Icc a b))
      (ν := volume.restrict (Set.Icc a b))
      (f := fun t z : ℝ => deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0)) hInt
  -- the inner `t`-integral at fixed `z`
  have key3 : (∫ z in Set.Icc a b, ∫ t in Set.Icc a b,
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
      = ∫ z in Set.Icc a b, W z * ρ z := by
    refine setIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
    have e0 : (∫ t in Set.Icc a b, deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
        = ∫ t in Set.Icc a b, W z * (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0) :=
      setIntegral_congr_fun measurableSet_Icc (fun t _ => by
        by_cases h : t ≤ z
        · rw [ite_eq_left h, ite_eq_left h]; ring
        · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero])
    have e1 : (∫ t in Set.Icc a b, W z * (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
        = W z * ∫ t in Set.Icc a b,
            (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0) :=
      integral_const_mul (W z) _
    have e2 : (∫ t in Set.Icc a b, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
        = ρ z := by
      have h3a : (∫ t in Set.Icc a b, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
          = ∫ t in Set.Icc a z, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0) :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
          (Set.Icc_subset_Icc_right hz.2) (fun t ht => by
            have hle : ¬ (t ≤ z) := fun h => ht.2 ⟨ht.1.1, h⟩
            rw [ite_eq_right hle])
      have h3b : (∫ t in Set.Icc a z, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
          = ∫ t in Set.Icc a z, deriv (deriv ρ) t * (z - t) :=
        setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [ite_eq_left ht.2])
      have h3c : (∫ t in Set.Icc a z, deriv (deriv ρ) t * (z - t))
          = ∫ t in a..z, deriv (deriv ρ) t * (z - t) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz.1]
      rw [h3a, h3b, h3c, intervalIntegral_secondDeriv_mul_sub hz.1 (by simpa using hρ 3) hρa_ev]
    rw [e0, e1, e2]
  have hR : (∫ z in Set.Icc a b, W z * ρ z) = ∫ z in a..b, W z * ρ z :=
    (integral_Icc_eq_integral_Ioc).trans (intervalIntegral.integral_of_le hab').symm
  exact hL.trans (key1.trans (key2.trans (key3.trans hR)))

end Work.FTS.StrongEps.EComparison
