import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

open MeasureTheory

/-- The product of the prefix-sum step function `v ↦ (Σ_{k ≤ ⌊v⌋₊} c k)` with the continuous
factor `(v (log v)^2)⁻¹` is interval-integrable on `[N,M]` for `2 ≤ N ≤ M`.

Route. On `[N,M]` one has `v ≥ 2 > 1`, so `(v * (log v)^2)⁻¹` is continuous and bounded.
For the step factor, write `S(v) = ∑ k ∈ Finset.Icc 0 ⌊v⌋₊, c k`; it is bounded on `[N,M]` since
`⌊v⌋₊ ≤ ⌊M⌋₊` there. Measurability: `S = g ∘ (fun v => ⌊v⌋₊)` with
`g n = ∑ k ∈ Finset.Icc 0 n, c k : ℂ`, and `⌊·⌋₊` is measurable
(`Measurable.comp` / `Nat.measurable_floor`), or alternatively use the pointwise representation
`S v = ∑ k ∈ Finset.Icc 0 ⌊M⌋₊, if (k : ℝ) ≤ v then c k else 0` on `[N,M]` (a finite sum of
products of a constant with the indicator of `Set.Ici (k:ℝ)`, using `Nat.le_floor`), which is
manifestly strongly measurable. Then `AEStronglyMeasurable` + bounded + finite measure gives
`IntegrableOn` (`MeasureTheory.IntegrableOn.of_bound` or
`Integrable.of_bound`/`IntegrableOn.mono_set` with the constant majorant), hence
`IntervalIntegrable` (`intervalIntegrable_iff_integrableOn_Icc_of_le`). -/
theorem intervalIntegrable_step_sum_mul (c : ℕ → ℂ) (N M : ℝ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    IntervalIntegrable
      (fun v : ℝ => (∑ k ∈ Finset.Icc 0 ⌊v⌋₊, c k) * (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹)
      MeasureTheory.volume N M := by
  set A : ℝ := ∑ k ∈ Finset.Icc 0 ⌊M⌋₊, ‖c k‖ with hAdef
  set C : ℝ := A * (2 * (Real.log 2) ^ 2)⁻¹ with hCdef
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]; exact Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hd_pos : 0 < 2 * (Real.log 2) ^ 2 := by positivity
  have hmeas : Measurable
      (fun v : ℝ => (∑ k ∈ Finset.Icc 0 ⌊v⌋₊, c k) * (((v * (Real.log v) ^ 2 : ℝ)) : ℂ)⁻¹) := by
    apply Measurable.mul
    · exact (measurable_of_countable (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, c k)).comp
        (Measurable.nat_floor measurable_id)
    · exact (Complex.measurable_ofReal.comp
        (measurable_id.mul (Real.measurable_log.pow_const 2))).inv
  refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => C) intervalIntegrable_const
    hmeas.aestronglyMeasurable ?_
  rw [Set.uIoc_of_le hNM]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
  have hx2 : (2:ℝ) ≤ x := le_trans hN hx.1.le
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : ‖∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k‖ ≤ A := by
    rw [hAdef]
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.floor_mono hx.2)) (fun i _ _ => norm_nonneg _)
  have hr_pos : 0 < x * (Real.log x) ^ 2 := mul_pos hxpos (pow_pos hlogx 2)
  have hlogge : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : (Real.log 2)^2 ≤ (Real.log x)^2 := pow_le_pow_left₀ hlog2nn hlogge 2
  have hr_ge : 2 * (Real.log 2)^2 ≤ x * (Real.log x)^2 :=
    mul_le_mul hx2 hsq (sq_nonneg _) hxpos.le
  have h2 : ‖(((x * (Real.log x) ^ 2 : ℝ)) : ℂ)⁻¹‖ ≤ (2 * (Real.log 2) ^ 2)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self_eq_abs, abs_inv, abs_of_pos hr_pos]
    exact (inv_le_inv₀ hr_pos hd_pos).mpr hr_ge
  rw [hCdef, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) hA_nonneg

end Work.BMF.pcsw
