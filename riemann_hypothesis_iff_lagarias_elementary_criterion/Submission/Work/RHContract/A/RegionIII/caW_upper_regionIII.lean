import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.R3.caW_core

namespace Work.RHContract.A.RegionIII

/-- **`Margin.caW ε ≤ (12/100)·u(ξ)` in the region `ξ = caXi ε ≥ 10^8`**,
`u ξ = 1/(√ξ log ξ)` (no `RiemannHypothesis` needed: the envelope hypothesis `hA2` suffices).

`Margin.caW ε = log log ξ + v/L − log log ψ ξ` with `L = log ξ`, `v = (ψ ξ − ξ)/ξ`.  By `hA2`
at `t = ξ`, `|ψ ξ − ξ| ≤ 0.45ξ^{3/4} + 2`, so `ψ ξ = ξ(1 + v)` with `|v| ≤ v₀` where
`v₀ := (0.45ξ^{3/4} + 2)/ξ ≤ 4.501·10⁻³` for `ξ ≥ 10^8`; also `ψ ξ ≥ ξ(1 − v₀) > 1`, so
`log ψ ξ > 0`.

Writing `x := log(1+v)/L` one has `log log ψ ξ = log(L + log(1+v)) = log L + log(1 + x)`, hence

`caW ε = v/L − log(1 + x)`,  `|x| ≤ v₀/(L(1−v₀))`.

Since `log(1+x) ≥ x − x²` for `|x| ≤ 1/2` and `v − log(1+v) ≤ v²/(2(1−v₀))` for `|v| ≤ v₀ ≤ 1/2`,

`caW ε ≤ v²/(2(1−v₀)L) + v²/(L²(1−v₀)²) ≤ v₀²(1 + 2/L)/(2L(1−v₀)²)`,

and with `v₀²·√ξ ≤ 0.202502`, `L ≥ 18.42`, `1 − v₀ ≥ 0.995499`:

`v₀²(1 + 2/L)·√ξ·L/(2L(1−v₀)²) ≤ 0.202502·(1 + 2/18.42)/(2·0.995499²) = 0.113538 < 0.12`. -/
theorem caW_upper_regionIII (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hA2 : ∀ t : ℝ, Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ t →
      |Chebyshev.psi t - t| ≤ 0.45 * t ^ (3 / 4 : ℝ) + 2) :
    Work.RHContract.Margin.caW ε ≤ (12 / 100) * (1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
        * Real.log (Work.RHPlan.caXi ε : ℝ))) := by
  rw [Work.RHContract.Margin.caW]
  have hξ1 : (1 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hsqrt_le : Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have he : |Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) - (Work.RHPlan.caXi ε : ℝ)|
      ≤ 0.45 * (Work.RHPlan.caXi ε : ℝ) ^ (3 / 4 : ℝ) + 2 := hA2 _ hsqrt_le
  have hrpow_le : (Work.RHPlan.caXi ε : ℝ) ^ (3 / 4 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hξ1 (show (3 / 4 : ℝ) ≤ 1 by norm_num)
    simpa using this
  have hp_ge : (Work.RHPlan.caXi ε : ℝ) - (0.45 * (Work.RHPlan.caXi ε : ℝ) + 2)
      ≤ Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) := by
    have h := (abs_le.mp he).1
    linarith
  have hp1 : 1 < Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) := by
    nlinarith [hp_ge, hξ]
  have hcore := Work.RHContract.A.R3.caW_core (Work.RHPlan.caXi ε : ℝ)
    (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)) hξ hp1 he
  refine le_trans hcore ?_
  have hpos : (0 : ℝ) ≤ 1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
      * Real.log (Work.RHPlan.caXi ε : ℝ)) :=
    div_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hξ1))
  have hc : ((115 : ℝ) / 1000) ≤ 12 / 100 := by norm_num
  exact mul_le_mul_of_nonneg_right hc hpos

end Work.RHContract.A.RegionIII
