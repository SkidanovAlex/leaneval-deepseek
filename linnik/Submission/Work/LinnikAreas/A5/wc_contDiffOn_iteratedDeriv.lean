import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.f1_data
import Submission.Work.LinnikAreas.A5.Basic

open scoped Topology

namespace Work.LinnikAreas.A5

/-- On `(0,K)` the cut-off weight `wc K lam` coincides with the smooth branch
`(sinh (Kλ))⁻¹ · sinh((K−t)λ)`. -/
lemma wc_eq_smooth_of_mem {K lam t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) K) :
    wc K lam t = (Real.sinh (K * lam))⁻¹ * Real.sinh ((K - t) * lam) := by
  rw [wc_of_nonneg (le_of_lt ht.1), f1_of_le ht.2.le]

/-- `wc K lam` is `C²` on `(0,K)`, where it agrees with the smooth branch. -/
lemma wc_contDiffOn (K lam : ℝ) :
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.wc K lam) (Set.Ioo 0 K) := by
  have hψ : ContDiff ℝ 2
      (fun t : ℝ => (Real.sinh (K * lam))⁻¹ * Real.sinh ((K - t) * lam)) := by
    fun_prop
  exact hψ.contDiffOn.congr (fun t ht => wc_eq_smooth_of_mem ht)

/-- The second derivative of `wc K lam` on `(0,K)`. -/
lemma wc_iteratedDeriv_two (K lam : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) K) :
    iteratedDeriv 2 (Work.LinnikAreas.A5.wc K lam) t
      = lam ^ 2 * Real.sinh ((K - t) * lam) / Real.sinh (K * lam) := by
  have hev : wc K lam =ᶠ[𝓝 t] (fun s => (Real.sinh (K * lam))⁻¹ * f1 K lam s) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht.1] with s hs
    exact wc_of_nonneg (le_of_lt hs)
  rw [hev.iteratedDeriv_eq 2]
  rw [iteratedDeriv_const_mul_field, f1_iteratedDeriv_two K lam ht]
  ring

theorem wc_contDiffOn_iteratedDeriv (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.wc K lam) (Set.Ioo 0 K) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) K, ‖iteratedDeriv 2 (Work.LinnikAreas.A5.wc K lam) t‖ ≤ lam ^ 2) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) K, iteratedDeriv 2 (Work.LinnikAreas.A5.wc K lam) t
       = lam ^ 2 * Real.sinh ((K - t) * lam) / Real.sinh (K * lam)) := by
  have hsinh_pos : 0 < Real.sinh (K * lam) := Real.sinh_pos_iff.mpr (mul_pos hK hlam)
  refine ⟨wc_contDiffOn K lam, ?_, fun t ht => wc_iteratedDeriv_two K lam ht⟩
  intro t ht
  rw [wc_iteratedDeriv_two K lam ht]
  have h1 : (0:ℝ) ≤ (K - t) * lam := mul_nonneg (by linarith [ht.2]) hlam.le
  have h2 : (0:ℝ) ≤ lam ^ 2 * Real.sinh ((K - t) * lam) :=
    mul_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr h1)
  have h3 : Real.sinh ((K - t) * lam) ≤ Real.sinh (K * lam) :=
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by linarith [ht.1]) hlam.le)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg h2, abs_of_nonneg hsinh_pos.le]
  rw [div_le_iff₀ hsinh_pos]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end Work.LinnikAreas.A5
