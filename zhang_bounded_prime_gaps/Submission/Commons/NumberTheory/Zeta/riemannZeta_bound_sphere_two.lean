import Mathlib.NumberTheory.LSeries.RiemannZeta
import Submission.Commons.NumberTheory.Zeta.removedFactors_ratio_error

namespace Commons.NumberTheory.Zeta

theorem riemannZeta_bound_sphere_two :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖riemannZeta z‖ ≤ K := by
  have hne : (1 : ℂ) ∉ Metric.sphere (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_sphere, dist_eq_norm]
    norm_num
  have hcont : ContinuousOn riemannZeta (Metric.sphere (2 : ℂ) (3 / 2)) :=
    (differentiableOn_riemannZeta.mono fun z hz => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => hne (h ▸ hz)).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_sphere (2 : ℂ) (3 / 2)).exists_bound_of_continuousOn hcont
  exact ⟨|C| + 1, by positivity, fun z hz => (hC z hz).trans (by
    have : C ≤ |C| := le_abs_self C
    linarith)⟩

end Commons.NumberTheory.Zeta