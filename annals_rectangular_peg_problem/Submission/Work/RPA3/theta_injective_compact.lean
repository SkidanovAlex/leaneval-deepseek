import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.InjectiveDefs
import Submission.Work.RPA3.theta_per
import Submission.Work.RPA3.theta_std
import Submission.Work.RPA3.contDiff_thetaP
import Submission.Work.RPA3.theta_per_int
import Submission.Work.RPA3.ell_per_int
import Submission.Work.RPA3.int_tendsto_eventually_const

open Filter Set
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- **Local injectivity of `thetaP` from `IsLocDiffeoAt`.**  At a point where the derivative of
`thetaP L` is invertible, `thetaP L` is injective on a ball around that point.  This is the
`C¹`-inverse-function-theorem statement `ContDiffAt.toOpenPartialHomeomorph`: an open partial
homeomorphism is injective on its (open) source, which contains a ball around the point. -/
theorem local_inj_of_isLocDiffeoAt (L : LagFamilyAll) (w : ℝ × PS) (h : IsLocDiffeoAt L w) :
    ∃ δ > 0, ∀ y z : ℝ × PS, dist y w < δ → dist z w < δ → thetaP L y = thetaP L z → y = z := by
  obtain ⟨F', hF'⟩ := h
  have hcd : ContDiffAt ℝ 7 (thetaP L) w := (contDiff_thetaP L).contDiffAt
  have h7 : (7 : WithTop ENat) ≠ 0 := by norm_num
  set e := ContDiffAt.toOpenPartialHomeomorph (thetaP L) hcd hF' h7 with he
  have hcoe : (e : ℝ × PS → ℝ × PS) = thetaP L := by
    rw [he]; exact ContDiffAt.toOpenPartialHomeomorph_coe hcd hF' h7
  have hsrc : w ∈ e.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hcd hF' h7
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp e.open_source w hsrc
  refine ⟨δ, hδ, fun y z hy hz heq => ?_⟩
  have hy' : y ∈ e.source := hball (by rw [Metric.mem_ball]; exact hy)
  have hz' : z ∈ e.source := hball (by rw [Metric.mem_ball]; exact hz)
  exact e.injOn hy' hz' (by rw [hcoe]; exact heq)

end Work.RPA3
