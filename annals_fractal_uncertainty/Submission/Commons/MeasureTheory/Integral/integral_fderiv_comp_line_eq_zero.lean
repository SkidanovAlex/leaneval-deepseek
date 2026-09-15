import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.UniformSpace.Uniformizable

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory

/-- A C^1 function on the real line with compact support has derivative of integral zero. -/
theorem integral_deriv_eq_zero_of_contDiff_one_of_hasCompactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) : ∫ t : ℝ, deriv f t = 0 := by
  refine integral_eq_zero_of_hasDerivAt_of_integrable
    (fun t => (hf.differentiable one_ne_zero t).hasDerivAt) ?_ ?_
  · exact (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  · exact hf.continuous.integrable_of_hasCompactSupport hc

theorem integral_fderiv_comp_line_eq_zero {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (x y : EuclideanSpace ℝ (Fin d)) :
    ∫ t : ℝ, (fderiv ℝ φ (x + t • y)) y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp
  · set g : ℝ → ℝ := fun t => φ (x + t • y) with hg_def
    have hline_contDiff : ContDiff ℝ 1 fun t : ℝ => x + t • y :=
      contDiff_const.add (contDiff_id.smul_const y)
    have hline_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • y) y t := fun t => by
      simpa using ((hasDerivAt_id t).smul_const y).const_add x
    have hderiv : ∀ t : ℝ, HasDerivAt g ((fderiv ℝ φ (x + t • y)) y) t := by
      intro t
      have hl : HasFDerivAt φ (fderiv ℝ φ (x + t • y)) (x + t • y) :=
        (hφ.differentiable one_ne_zero (x + t • y)).hasFDerivAt
      exact hl.comp_hasDerivAt t (hline_deriv t)
    have hg_compact : HasCompactSupport g := by
      obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall x
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R / ‖y‖)) ?_
      intro t ht
      have hnot : x + t • y ∉ tsupport φ := by
        intro hmem
        have hb : ‖t‖ * ‖y‖ ≤ R := by
          have hmem' := hR hmem
          rw [Metric.mem_closedBall, dist_eq_norm] at hmem'
          simpa [norm_smul] using hmem'
        have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
        have hle : ‖t‖ ≤ R / ‖y‖ := (le_div_iff₀ hypos).mpr hb
        have : t ∈ Metric.closedBall (0 : ℝ) (R / ‖y‖) := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          simpa using hle
        exact ht this
      change φ (x + t • y) = 0
      exact image_eq_zero_of_notMem_tsupport hnot
    have hg_contDiff : ContDiff ℝ 1 g := hφ.comp hline_contDiff
    have hg_int : Integrable g :=
      hg_contDiff.continuous.integrable_of_hasCompactSupport hg_compact
    have hderiv_int : Integrable (deriv g) :=
      (hg_contDiff.continuous_deriv le_rfl).integrable_of_hasCompactSupport hg_compact.deriv
    have hf'_int : Integrable (fun t : ℝ => (fderiv ℝ φ (x + t • y)) y) := by
      have heq : (fun t : ℝ => (fderiv ℝ φ (x + t • y)) y) = deriv g := by
        funext t
        exact ((hderiv t).deriv).symm
      rw [heq]
      exact hderiv_int
    exact integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf'_int hg_int

end Commons.MeasureTheory.Integral