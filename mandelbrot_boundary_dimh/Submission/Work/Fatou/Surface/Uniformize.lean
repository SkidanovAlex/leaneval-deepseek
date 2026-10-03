import Submission.Work.Fatou.Surface.Deck

/-!
# Uniformizing `XF`

Combining the uniformization hypothesis `UniformizationHyp` (applied to the Riemann surface
`XF D`) with the exclusion of the upper half-plane case, we obtain a biholomorphism
`XF D ≃ ℂ`.  Note that `XF D` is simply connected (it is `ℂ` topologically), so the periods
condition of `UniformizationHyp` holds automatically.
-/

namespace Work.Fatou

open MandelDim Filter Set Metric
open scoped Topology Manifold ContDiff
open LeanEval.Geometry

noncomputable section

open FatouData

/-- `XF D` has no non-trivial additive periods (it is simply connected). -/
instance subsingleton_periods (D : FatouData) (x : D.XF) :
    Subsingleton (Additive (FundamentalGroup D.XF x) →+ ℝ) where
  allEq f g := AddMonoidHom.ext fun a => by
    have ha : a = 0 := Subsingleton.elim a 0
    rw [ha, map_zero, map_zero]

/-- **Uniformization of `XF`.**  Assuming the uniformization theorem and the impossibility of the
upper half-plane case, `XF D` is biholomorphic to `ℂ`. -/
theorem exists_diffeomorph_plane (hU : UniformizationHyp)
    (hnp : ∀ D : FatouData,
      ¬ Nonempty (D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane))
    (D : FatouData) :
    Nonempty (D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) := by
  have hnc : ¬ CompactSpace D.XF := by
    intro hc
    haveI := hc
    haveI : NoncompactSpace D.XF := instNoncompactSpaceXF D
    exact (inferInstance : NoncompactSpace D.XF).noncompact_univ isCompact_univ
  rcases hU D.XF hnc (D.ofℂ 0) inferInstance with h | h
  · exact h
  · exact absurd h (hnp D)

end

end Work.Fatou
