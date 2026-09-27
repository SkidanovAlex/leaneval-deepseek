import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.Complex

theorem exists_annulus_lt_of_lt_on_sphere {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0:ℂ) R)) (hg : ContinuousOn g (Metric.closedBall (0:ℂ) R))
    (h : ∀ z ∈ Metric.sphere (0:ℂ) R, ‖g z‖ < ‖f z‖) :
    ∃ ρ, 0 < ρ ∧ ρ < R ∧ ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ R → ‖g z‖ < ‖f z‖ := by
  have hball : IsCompact (Metric.closedBall (0:ℂ) R) := isCompact_closedBall 0 R
  have hsphere : IsCompact (Metric.sphere (0:ℂ) R) := isCompact_sphere 0 R
  have hψcont : ContinuousOn (fun z : ℂ => ‖f z‖ - ‖g z‖) (Metric.closedBall (0:ℂ) R) :=
    hf.norm.sub hg.norm
  have hψcont_sphere : ContinuousOn (fun z : ℂ => ‖f z‖ - ‖g z‖) (Metric.sphere (0:ℂ) R) :=
    hψcont.mono Metric.sphere_subset_closedBall
  have hpos : ∀ z ∈ Metric.sphere (0:ℂ) R, (0:ℝ) < ‖f z‖ - ‖g z‖ := by
    intro z hz
    have := h z hz
    linarith
  obtain ⟨m, hm0, hm⟩ := hsphere.exists_forall_le' hψcont_sphere hpos
  have huc : UniformContinuousOn (fun z : ℂ => ‖f z‖ - ‖g z‖) (Metric.closedBall (0:ℂ) R) :=
    hball.uniformContinuousOn_of_continuous hψcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc (m / 2) (by linarith)
  set c : ℝ := min δ (R / 2) with hcdef
  have hc0 : 0 < c := lt_min hδ0 (by linarith)
  have hcR : c ≤ R / 2 := min_le_right _ _
  have hcδ : c ≤ δ := min_le_left _ _
  refine ⟨R - c / 2, by linarith, by linarith, ?_⟩
  intro z hzρ hzR
  have hzpos : 0 < ‖z‖ := by linarith [hzρ, hcR, hR]
  set w : ℂ := (R / ‖z‖) • z with hw
  have hwnorm : ‖w‖ = R := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hzpos)]
    exact div_mul_cancel₀ R (ne_of_gt hzpos)
  have hwsphere : w ∈ Metric.sphere (0:ℂ) R := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact hwnorm
  have hzw : dist z w < δ := by
    have hzw_eq : dist z w = R - ‖z‖ := by
      rw [dist_eq_norm, hw]
      rw [show z - (R / ‖z‖) • z = (1 - R / ‖z‖) • z by rw [sub_smul, one_smul]]
      rw [norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonpos (by
        have h1 : (1 : ℝ) ≤ R / ‖z‖ := (le_div_iff₀ hzpos).mpr (by linarith)
        linarith)]
      field_simp
      ring
    rw [hzw_eq]
    have h2 : R - ‖z‖ ≤ c / 2 := by linarith [hzρ]
    linarith [hcδ, hδ0]
  have hzmem : z ∈ Metric.closedBall (0:ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hzR
  have hwmem : w ∈ Metric.closedBall (0:ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_eq hwnorm
  have hclose := hδ z hzmem w hwmem hzw
  rw [Real.dist_eq] at hclose
  have hwm : m ≤ ‖f w‖ - ‖g w‖ := hm w hwsphere
  have hfin : 0 < ‖f z‖ - ‖g z‖ := by
    have h1 : -(m / 2) < (‖f z‖ - ‖g z‖) - (‖f w‖ - ‖g w‖) := (abs_lt.mp hclose).1
    linarith
  linarith

end Commons.Analysis.Complex