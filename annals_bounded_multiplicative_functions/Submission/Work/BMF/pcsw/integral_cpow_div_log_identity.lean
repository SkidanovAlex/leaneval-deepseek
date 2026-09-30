import Mathlib
import Submission.Work.BMF.pcsw.intervalIntegrable_cpow_div_log
import Submission.Work.BMF.pcsw.intervalIntegrable_cpow_mul_inv_sq_log

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

open MeasureTheory

/-- **Derivative of `v ↦ (v^{1+it}/(1+it))/log v`.** For `x > 1`, with `G(v) = v^{1+it}/(1+it)`
satisfying `G' = v^{it}` (`hasDerivAt_ofReal_cpow_const'`) and `(log v)' = 1/v`:

`H' x = v^{it}/log v − (v^{1+it}/(1+it)) · (v (log v)²)⁻¹`.

This is the exact `H` and `H'` appearing in `integral_cpow_div_log_identity`. -/
lemma hasDerivAt_cpow_div_log (t x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun v : ℝ => (v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t) / ((Real.log v : ℝ) : ℂ))
      ((x : ℂ) ^ (Complex.I * t) / ((Real.log x : ℝ) : ℂ)
        - ((x : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) * (((x * (Real.log x) ^ 2 : ℝ)) : ℂ)⁻¹) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hI : Complex.I * (t:ℂ) ≠ -1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hG : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t))
      ((x : ℂ) ^ (Complex.I * t)) x := by
    have h := hasDerivAt_ofReal_cpow_const' hx0 (r := Complex.I * (t:ℂ)) hI
    simpa only [add_comm (Complex.I * (t:ℂ)) 1] using h
  have hL : HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) (((x⁻¹ : ℝ)) : ℂ) x :=
    (Real.hasDerivAt_log hx0).ofReal_comp
  have hLne : ((Real.log x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlogpos
  have hH := hG.div hL hLne
  refine hH.congr_deriv ?_
  push_cast
  field_simp

/-- **The `[N,M]` integral of `v^{it}/log v` against its antiderivative** (integration by parts
with `G(v) = v^{1+it}/(1+it)`, `G' = v^{it}`):
```
∫_N^M v^{it}/log v dv = G(M)/log M − G(N)/log N + ∫_N^M G(v)/(v (log v)^2) dv
```
for `1 < N ≤ M`, where `v^{c}` is `Complex.cpow`.

Route. Let `H v = ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log v : ℝ) : ℂ)`
on `(1, ∞)`. Then `H` is differentiable with
`H' v = v^{it}/log v − (v^{1+it}/(1+it)) * ((v * (log v)^2)⁻¹)`:
differentiate using `hasDerivAt_ofReal_cpow_const'` (with `r = I*t ≠ -1`) for
`v ↦ v^{1+it}/(1+it)`, `Real.hasDerivAt_log`, `HasDerivAt.div`, and simplify using
`(v : ℂ)^{I*t} = (v : ℂ)^{1+I*t} / v` (`Complex.cpow_add`, `Complex.cpow_one` for `v ≠ 0`).
Both summands of `H'` are continuous on the compact interval `[N,M]` (`N > 1`), hence
interval integrable. Newton–Leibniz
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) applied to `H` gives
`∫_N^M H' = H M − H N`; then `intervalIntegral.integral_add` (or `integral_sub`) splits
`∫_N^M H'` into the two integrals of the statement, and the result is rearranged. -/
theorem integral_cpow_div_log_identity (t N M : ℝ) (hN : 1 < N) (hNM : N ≤ M) :
    ∫ v in N..M, (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)
      = ((Real.log M : ℝ) : ℂ)⁻¹ * ((M : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t))
        - ((Real.log N : ℝ) : ℂ)⁻¹ * ((N : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t))
        + ∫ v in N..M, ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) *
            (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹ := by
  have hint1 : IntervalIntegrable
      (fun v : ℝ => (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)) volume N M :=
    intervalIntegrable_cpow_div_log t N M hN hNM
  have hint2 : IntervalIntegrable
      (fun v : ℝ => ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) *
        (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹) volume N M :=
    intervalIntegrable_cpow_mul_inv_sq_log t N M hN hNM
  -- Newton–Leibniz for `H v = (v^{1+it}/(1+it))/log v`
  have hNL : ∫ v in N..M, ((v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)
        - ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) * (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹)
      = ((M : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log M : ℝ) : ℂ)
        - ((N : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log N : ℝ) : ℂ) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v : ℝ =>
        ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log v : ℝ) : ℂ)) ?_ ?_
    · intro x hx
      rw [Set.uIcc_of_le hNM] at hx
      exact hasDerivAt_cpow_div_log t x (lt_of_lt_of_le hN hx.1)
    · exact hint1.sub hint2
  -- split the integral of `H'` as a difference
  have hsplit : ∫ v in N..M, ((v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ)
        - ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) * (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹)
      = (∫ v in N..M, (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ))
        - (∫ v in N..M, ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) *
            (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹) :=
    intervalIntegral.integral_sub hint1 hint2
  have key : (∫ v in N..M, (v : ℂ) ^ (Complex.I * t) / ((Real.log v : ℝ) : ℂ))
      = (((M : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log M : ℝ) : ℂ)
        - ((N : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log N : ℝ) : ℂ))
        + (∫ v in N..M, ((v : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) *
            (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹) := by
    rw [hsplit] at hNL
    exact sub_eq_iff_eq_add.mp hNL
  rw [key]
  have hM : (((M : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log M : ℝ) : ℂ))
      = ((Real.log M : ℝ) : ℂ)⁻¹ * ((M : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) :=
    div_eq_inv_mul _ _
  have hN' : (((N : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) / ((Real.log N : ℝ) : ℂ))
      = ((Real.log N : ℝ) : ℂ)⁻¹ * ((N : ℂ) ^ (1 + Complex.I * t) / (1 + Complex.I * t)) :=
    div_eq_inv_mul _ _
  rw [hM, hN']

end Work.BMF.pcsw

