import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_covered

/-!
# The components of a slice cover every loop contained in the sphere

Let `P` be a parametrised torus with surface `F = P.carrier`, and let `S` be an embedded sphere
equipped with a slicing datum `Work.Topology.SphereSlicing.SliceData P S`: `S ∩ F` is a finite
union of pairwise disjoint simple closed curves `c i` of `F` (the field `disjoint`), and every
point of `S ∩ F` lies on one of them (the field `covers_pt`).

Then a closed curve `γ` of `F` whose image lies entirely in `S` has its image contained in the
image of a *single* component `c i`.

The argument is purely topological: `Set.range γ.γ`, being the image of the connected space `ℝ`
under the continuous map `γ.γ`, is preconnected; each `Set.range (c i).γ` is compact (the image
of the fundamental period `[0, 2π]`, by `2π`-periodicity), hence closed; the ranges of distinct
indices are disjoint by `SliceData.disjoint`; and `SliceData.covers_pt` (together with `γ.mem`)
shows that `Set.range γ.γ` is covered by the union of the ranges.  A preconnected set covered by
finitely many pairwise disjoint closed sets lies in one of them — this is exactly
`Work.InnermostDisk.exists_subset_of_preconnected_iUnion`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Topology.SphereSlicing

theorem sliceData_covers {P : Work.CoreTopology.ParamTorus}
    {S : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Topology.SphereSlicing.SliceData P S) (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ.γ t ∈ S) : ∃ i : h.ι, Set.range γ.γ ⊆ Set.range (h.c i).γ := by
  refine Work.InnermostDisk.exists_subset_of_preconnected_iUnion
    (isPreconnected_range γ.cont) ⟨γ.γ 0, ⟨0, rfl⟩⟩ (fun i => Set.range (h.c i).γ)
    (fun i => Work.InnermostDisk.isClosed_range_closedCurve (h.c i)) h.disjoint ?_
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨i, hi⟩ := h.covers_pt (γ.γ t) (hγ t) (γ.mem t)
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

end Work.Topology.SphereSlicing
