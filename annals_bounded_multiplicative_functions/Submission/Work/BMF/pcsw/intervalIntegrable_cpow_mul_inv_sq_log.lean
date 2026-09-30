import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

open MeasureTheory

/-- The function `v ↦ (v^{1+it}/(1+it)) · (v (log v)²)⁻¹` is interval integrable on `[N,M]`
for `1 < N ≤ M`.

Route. `(1+it) ≠ 0` (its real part is `1`), so the first factor `v ↦ v^{1+it}/(1+it)` is
continuous on `[N,M]`: at every `x ∈ [N,M]` we have `x ≥ N > 1 > 0`, hence `x ≠ 0`, and
`hasDerivAt_ofReal_cpow_const` gives differentiability (and so continuity) of `v ↦ v^{1+it}`
there. The second factor `v ↦ (v (log v)²)⁻¹` is continuous on `[N,M]` because `v * (log v)²`
is continuous (product of `id` and `(Real.log ·)²`, the latter continuous since `v ≥ N > 1 > 0`)
and strictly positive there, hence nonzero. The product is continuous on the compact interval,
hence `IntervalIntegrable` by `ContinuousOn.intervalIntegrable_of_Icc`. -/
theorem intervalIntegrable_cpow_mul_inv_sq_log (t N M : ℝ) (hN : 1 < N) (hNM : N ≤ M) :
    IntervalIntegrable
      (fun v : ℝ => ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) *
        (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹) MeasureTheory.volume N M := by
  refine ContinuousOn.intervalIntegrable_of_Icc hNM ?_
  have hr : (1 + Complex.I * (t : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hpow : ContinuousOn (fun v : ℝ => (v : ℂ) ^ (1 + Complex.I * (t : ℂ)))
      (Set.Icc N M) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have h1 : (1 : ℝ) < x := lt_of_lt_of_le hN hx.1
      linarith
    exact ((hasDerivAt_ofReal_cpow_const hx0 hr).continuousAt).continuousWithinAt
  have hcont1 : ContinuousOn
      (fun v : ℝ => (v : ℂ) ^ (1 + Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)))
      (Set.Icc N M) := hpow.div_const _
  have hlogcont : ContinuousOn Real.log (Set.Icc N M) :=
    Real.continuousOn_log.mono fun v hv => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have h1 : (1 : ℝ) < v := lt_of_lt_of_le hN hv.1
      exact ne_of_gt (lt_trans one_pos h1)
  have hne : ∀ v ∈ Set.Icc N M, (((v * (Real.log v) ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    intro v hv
    have h1 : (1 : ℝ) < v := lt_of_lt_of_le hN hv.1
    have hv0 : v ≠ 0 := ne_of_gt (lt_trans one_pos h1)
    have hlogne : Real.log v ≠ 0 := ne_of_gt (Real.log_pos h1)
    have hreal : (v * (Real.log v) ^ 2 : ℝ) ≠ 0 :=
      mul_ne_zero hv0 (pow_ne_zero 2 hlogne)
    exact_mod_cast hreal
  have hcont2 : ContinuousOn (fun v : ℝ => (((v * (Real.log v) ^ 2 : ℝ)) : ℂ))
      (Set.Icc N M) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.mul (hlogcont.pow 2))
  exact hcont1.mul (hcont2.inv₀ hne)

end Work.BMF.pcsw
