import Mathlib
import Submission.Work.Smooth.SphereJordan.Pullback

namespace Work.Smooth.SphereJordan

/-- The pull-backs to the model disc of the pairwise disjoint intersection curves of a slice disc are
again pairwise disjoint: the pull-back is injective (it is the inverse of the embedding `D.e` on its
image), and any common point of two pulled-back curves would be a common point of the two curves of
`F`, which are disjoint by `SliceDisc.curves_disjoint`. -/
theorem pullbackSphereCurve_pairwiseDisjoint {P : Work.CoreTopology.ParamTorus}
    (D : Work.Topology.SphereSlicing.SliceDisc P) :
    Pairwise fun i j : D.ι => Disjoint
      (Set.range (Work.Smooth.SphereJordan.pullbackSphereCurve D i))
      (Set.range (Work.Smooth.SphereJordan.pullbackSphereCurve D j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨t, ht⟩ ⟨s, hs⟩
  -- a common point of the two pull-backs gives an equality of the two model-disc parameters
  have h : pullbackSphereCurve D i t = pullbackSphereCurve D j s := ht.trans hs.symm
  have hc : ((SliceDiscPullback D i t : Disc) : ℂ) = ((SliceDiscPullback D j s : Disc) : ℂ) :=
    OnePoint.coe_injective h
  have hDisc : SliceDiscPullback D i t = SliceDiscPullback D j s := Subtype.ext hc
  -- hence the two original curves of `F` meet, contradicting their disjointness
  have hval : (D.curves i).γ t = (D.curves j).γ s := by
    have h1 := SliceDiscPullback_spec D i t
    have h2 := SliceDiscPullback_spec D j s
    rw [hDisc] at h1
    exact h1.symm.trans h2
  exact (Set.disjoint_left.mp (D.curves_disjoint hij) ⟨t, rfl⟩) ⟨s, hval.symm⟩

end Work.Smooth.SphereJordan
