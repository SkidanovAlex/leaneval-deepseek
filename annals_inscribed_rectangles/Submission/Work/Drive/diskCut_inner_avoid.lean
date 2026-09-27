import Mathlib
import Submission.Work.Drive.cutTransport

open scoped Topology

namespace Work.Drive

/-- **The cut of a disk presentation avoids a neighbourhood of the origin, provided the base point
does.**  If `Q 0` is not a point of the sweep `W` (over the parameter cube), then for all sufficiently
small `x` the plane point `Q (cplxOf x)` is still outside the *compact* set `W '' unitBox 2`, and
hence `x` is not a point of the cut `diskCut Q W` (which requires `Q (cplxOf x) ∈ W '' unitBox 2`).

The content is exactly: `W '' unitBox 2` is compact hence closed in the Hausdorff space
`CappingSpace` (`Work.Drive.t2Space_cappingSpace`), so its complement is a neighbourhood of `Q 0`,
which pulls back to a neighbourhood of `0` along the continuous map `x ↦ Q (cplxOf x)`
(`cplxOf` is the linear isometry equivalence `ℝ² ≅ ℂ`, so `‖cplxOf x‖ = ‖x‖`). -/
theorem diskCut_inner_avoid (Q : ℂ → CappingSpace) (W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hQ : Continuous Q) (hW : Continuous W) (h0 : Q 0 ∉ W '' Submission.Drive.unitBox 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δ → x ∉ diskCut Q W := by
  haveI : T2Space CappingSpace := Work.Drive.t2Space_cappingSpace
  have hK : IsCompact (W '' Submission.Drive.unitBox 2) := (isCompact_unitBox 2).image hW
  have hcplx : Continuous fun x : EuclideanSpace ℝ (Fin 2) => cplxOf x := by
    have h : (fun x : EuclideanSpace ℝ (Fin 2) => cplxOf x) = ⇑Work.Drive.LinChart.cplxOfLIE :=
      funext fun x => (Work.Drive.LinChart.cplxOfLIE_apply x).symm
    rw [h]; exact Work.Drive.LinChart.cplxOfLIE.continuous
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 2) => Q (cplxOf x) := hQ.comp hcplx
  have hmem : (fun x : EuclideanSpace ℝ (Fin 2) => Q (cplxOf x)) ⁻¹'
        (W '' Submission.Drive.unitBox 2)ᶜ ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) :=
    hcont.continuousAt.eventually (hK.isClosed.isOpen_compl.mem_nhds (by simpa using h0))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  exact ⟨ε / 2, by linarith, fun x hx hxcut => hsub (by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, ← norm_cplxOf x]; linarith) hxcut.2⟩

end Work.Drive
