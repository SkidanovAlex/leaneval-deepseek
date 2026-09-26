import Submission.Work.Collar3D.Model.Plane
import Submission.Work.Collar3D.Model.planeChartHomeo
import Submission.Work.Collar3D.Model.isCircleCurve_planeCircle
import Submission.Work.Collar3D.Model.Basic

/-!
# The model collar of the plane along its unit circle

The explicit collar

`Work.Collar3D.hasCollar_planeCircle : HasCollar plane planeCircle`

realising `Work.Collar3D.plane` as the middle sheet `S¹ × ℝ × {0}` of the chart
`p ↦ (unit (p 0 + p 1 · i), log ‖p 0 + p 1 · i‖, p 2)` of the complement of the `z`-axis, with the
unit circle as the core.  This is the non-vacuity certificate of `Work.Collar3D.HasCollar`.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

theorem planeChartFun_circle (θ : ℝ) :
    planeChartFun ⟨planeCircle θ, planeCircle_mem_planeTube θ⟩ = (circlePoint θ, 0, 0) := by
  have hv : planeCircle θ 0 + planeCircle θ 1 * Complex.I = Complex.exp (θ * Complex.I) := by
    rw [planeCircle_zero, planeCircle_one, Complex.exp_ofReal_mul_I]
  have hn : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    rw [planeChartFun_fst, hv, hn]
    simp
  · rw [planeChartFun_snd, hv, hn, Real.log_one]
  · rw [planeChartFun_thd, planeCircle_two]

/-- **The model collar of the plane along its unit circle**: the complement of the `z`-axis, with
the polar-coordinate chart. -/
theorem hasCollar_planeCircle : HasCollar plane planeCircle := by
  obtain ⟨Φ, hΦ⟩ := Work.Collar3D.Model.planeChartHomeo
  have hγ : ∀ θ : ℝ, Φ ⟨planeCircle θ, planeCircle_mem_planeTube θ⟩ = (circlePoint θ, 0, 0) :=
    fun θ => by rw [hΦ, planeChartFun_circle]
  have hF : ∀ u : ↥planeTube, ((u : R3) ∈ plane ↔ (Φ u).2.2 = 0) := fun u => by
    rw [hΦ]
    exact Iff.rfl
  exact ⟨planeTube, planeTube_isOpen, planeCircle_mem_planeTube, Φ, hγ, hF⟩

end

end Work.Collar3D
