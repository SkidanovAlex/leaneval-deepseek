import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.preconnected_finite_closed_cover
import Submission.Work.Topology.SphereSlicing.range_closedCurve_isCompact

namespace Work.Topology.SphereSlicing

open Set
open Work.CoreTopology

/-- **A loop of `F` lying in a transverse sphere lies on a single component of `S ∩ F`.**

If `S` is transverse to `F` (so that `S ∩ F` is a finite disjoint union of simple closed curves
of `F`), then every closed curve `γ` of `F` whose image is contained in `S` is contained in one of
those components: the image of `γ` is connected, `S ∩ F` is the disjoint union of the (compact,
hence closed) images of the components, and a connected set which is a finite disjoint union of
closed pieces is one of the pieces.

The curve `c` of the conclusion is that component; it is simple, it lies in `S`, and it covers
`γ`. -/
theorem transverseSphere_covers {P : Work.CoreTopology.ParamTorus}
    {S : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Topology.SphereSlicing.TransverseSphere P S)
    (γ : Work.CoreTopology.ClosedCurve P) (hγ : ∀ t : ℝ, γ.γ t ∈ S) :
    ∃ c : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsSimple P c ∧
      (∀ t : ℝ, c.γ t ∈ S) ∧ Set.range γ.γ ⊆ Set.range c.γ := by
  obtain ⟨ι, hfin, c, hsimple, hdisj, hmem, hcovers⟩ := h
  -- the image of `γ` is preconnected
  have hpre : IsPreconnected (Set.range γ.γ) := isPreconnected_range γ.cont
  -- each component of `S ∩ F` has closed image
  have hclosed : ∀ i : ι, IsClosed (Set.range (c i).γ) :=
    fun i => (range_closedCurve_isCompact (c i)).isClosed
  -- the components are pairwise disjoint
  have hdisj' : ∀ i j : ι, i ≠ j →
      Disjoint (Set.range (c i).γ) (Set.range (c j).γ) :=
    fun i j hij => hdisj hij
  -- the image of `γ` is nonempty
  have hne : (Set.range γ.γ).Nonempty := ⟨γ.γ 0, 0, rfl⟩
  -- the components cover the image of `γ`
  have hsub : Set.range γ.γ ⊆ ⋃ i, Set.range (c i).γ := by
    rintro y ⟨t, rfl⟩
    exact Set.mem_iUnion.mpr (hcovers (γ.γ t) (hγ t) (γ.mem t))
  obtain ⟨i, hi⟩ :=
    @preconnected_finite_closed_cover (Set.range γ.γ) hpre ι hfin (fun i => Set.range (c i).γ)
      hclosed hdisj' hne hsub
  exact ⟨c i, hsimple i, hmem i, hi⟩

end Work.Topology.SphereSlicing
