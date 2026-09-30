import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

open MeasureTheory

/-- The complexified function `v ↦ (log v)⁻¹` is differentiable at `t > 1` with derivative
`-((t (log t)²)⁻¹)`. -/
lemma hasDerivAt_inv_log_cplx (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹)
      (-(((t * (Real.log t) ^ 2 : ℝ)) : ℂ)⁻¹) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hL : HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) ((t⁻¹ : ℝ) : ℂ) t :=
    (Real.hasDerivAt_log ht0).ofReal_comp
  have hLne : ((Real.log t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hlogpos
  have h := hL.inv hLne
  have hval : (-((t⁻¹ : ℝ) : ℂ)) / (((Real.log t : ℝ) : ℂ)) ^ 2
      = -(((t * (Real.log t) ^ 2 : ℝ)) : ℂ)⁻¹ := by
    push_cast
    rw [div_eq_mul_inv, neg_mul, mul_inv]
  convert h using 1
  exact hval.symm

/-- **Abel's summation formula with the weight `v ↦ 1/log v`.** For any sequence `c : ℕ → ℂ`
and reals `2 ≤ N ≤ M`, with `C(t) = Σ_{k ≤ ⌊t⌋₊} c k` the prefix-sum step function,
```
Σ_{N < k ≤ M} c k / log k = C(M)/log M − C(N)/log N + ∫_N^M C(v) / (v (log v)^2) dv ,
```
where the left sum runs over the naturals `k ∈ (⌊N⌋₊, ⌊M⌋₊]` and the integral is the
interval integral over `[N,M]`.

Route (mirror of `Submission/Work/BMF/liouville/abel_step_twist.lean`, which does the same for
the weight `1/(t log t)`): apply Mathlib's `sum_mul_eq_sub_sub_integral_mul`
(`Mathlib/NumberTheory/AbelSummation.lean`) with `𝕜 = ℂ`, `f v = ((Real.log v : ℝ) : ℂ)⁻¹`
and the sequence `c` itself (its prefix sums are already `∑ k ∈ Icc 0 ⌊v⌋₊, c k`), lower limit
`N` and upper limit `M`. `f` is differentiable on `[N,M]` since `N ≥ 2 > 1` (so `log v ≠ 0`),
with `deriv f v = -((v * (log v)^2)⁻¹ : ℝ)` as an element of `ℂ` (from `Real.hasDerivAt_log`,
`HasDerivAt.inv`, `HasDerivAt.ofReal_comp`), and `deriv f` is integrable there because it is
continuous on the compact interval. Since the formula's sum is already over
`Finset.Ioc ⌊N⌋₊ ⌊M⌋₊`, no boundary-term absorption is needed. -/
theorem abel_inv_log_identity (c : ℕ → ℂ) (N M : ℝ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Finset.Ioc ⌊N⌋₊ ⌊M⌋₊, ((Real.log k : ℝ) : ℂ)⁻¹ * c k
      = ((Real.log M : ℝ) : ℂ)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊M⌋₊, c k)
        - ((Real.log N : ℝ) : ℂ)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊N⌋₊, c k)
        + ∫ v in N..M, (∑ k ∈ Finset.Icc 0 ⌊v⌋₊, c k) * (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹ := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hderiv : ∀ t ∈ Set.Icc N M,
      HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹)
        (-(((t * (Real.log t) ^ 2 : ℝ)) : ℂ)⁻¹) t :=
    fun t ht => hasDerivAt_inv_log_cplx t (by linarith [ht.1])
  have hdiff : ∀ t ∈ Set.Icc N M,
      DifferentiableAt ℝ (fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹) t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hEq : Set.EqOn (fun t : ℝ => -(((t * (Real.log t) ^ 2 : ℝ)) : ℂ)⁻¹)
      (deriv (fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹)) (Set.Icc N M) :=
    fun t ht => ((hderiv t ht).deriv).symm
  have hlogcont : ContinuousOn Real.log (Set.Icc N M) :=
    Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : (2 : ℝ) ≤ t := le_trans hN ht.1
      linarith)
  have hne : ∀ t ∈ Set.Icc N M, (t * (Real.log t) ^ 2 : ℝ) ≠ 0 := by
    intro t ht
    have h2 : (2 : ℝ) ≤ t := le_trans hN ht.1
    exact mul_ne_zero (by linarith) (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith))))
  have hcplx : ContinuousOn (fun t : ℝ => (((t * (Real.log t) ^ 2 : ℝ)) : ℂ)) (Set.Icc N M) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.mul (hlogcont.pow 2))
  have hneC : ∀ t ∈ Set.Icc N M, (((t * (Real.log t) ^ 2 : ℝ)) : ℂ) ≠ 0 :=
    fun t ht => by exact_mod_cast hne t ht
  have hcont : ContinuousOn
      (fun t : ℝ => -(((t * (Real.log t) ^ 2 : ℝ)) : ℂ)⁻¹) (Set.Icc N M) :=
    (hcplx.inv₀ hneC).neg
  have hint : IntegrableOn (deriv (fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹)) (Set.Icc N M) :=
    (hcont.integrableOn_compact isCompact_Icc).congr_fun hEq measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c (f := fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹)
    hN0 hNM hdiff hint
  have hint_eq : (∫ t in Set.Ioc N M,
        deriv (fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      = -∫ v in N..M,
        (∑ k ∈ Finset.Icc 0 ⌊v⌋₊, c k) * (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹ := by
    have h1 : (∫ t in Set.Ioc N M,
          deriv (fun v : ℝ => ((Real.log v : ℝ) : ℂ)⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        = ∫ t in Set.Ioc N M,
          -((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) * (((t * (Real.log t) ^ 2 : ℝ)) : ℂ)⁻¹) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp only []
      rw [(hderiv t ⟨le_of_lt ht.1, ht.2⟩).deriv]
      ring
    rw [h1, MeasureTheory.integral_neg]
    congr 1
    exact (intervalIntegral.integral_of_le hNM).symm
  rw [habel, hint_eq]
  ring

end Work.BMF.pcsw
