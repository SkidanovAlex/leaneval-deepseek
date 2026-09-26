import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_isSimple

/-!
# Loops inside a finite union of disjoint inessential simple loops

Let `F = P.carrier` be a parametrised torus and let `c : ι → ClosedCurve P` be a finite family of
*simple*, *inessential*, pairwise disjoint closed curves of `F`.  This file proves

`Work.InnermostDisk.not_isEssential_of_range_subset_covered`:

a closed curve `γ` of `F` whose image is contained in the union of the images of the `c i` is
inessential in `F`.

The point is that `Set.range γ.γ`, the image of the connected space `ℝ` under the continuous map
`γ.γ`, is preconnected; each `Set.range (c i).γ` is compact (the image of the fundamental period
`[0, 2π]`), hence closed; and the ranges of distinct indices are disjoint.  A preconnected set
covered by a finite family of pairwise disjoint closed sets lies in one of them, so `γ` ranges in
the image of a single `c i`, and `Work.InnermostDisk.not_isEssential_of_range_subset_isSimple`
concludes.

This is the step from Pardon's literal conclusion ("every *component* of `S ∩ F` is inessential
in `F`") to the formal one used by `mustbeinessential` ("every closed curve of `F` whose image
lies in `S` is inessential").
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.InnermostDisk

noncomputable section

/-- The image of a closed curve of the torus is compact (it is the image of the compact
fundamental period `[0, 2π]`, by `2π`-periodicity), hence a closed subset of `ℝ³`. -/
theorem isClosed_range_closedCurve {P : Work.CoreTopology.ParamTorus}
    (c : Work.CoreTopology.ClosedCurve P) : IsClosed (Set.range c.γ) := by
  have hsub : Set.range c.γ ⊆ c.γ '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P c]
    exact Set.image_mono Set.Ico_subset_Icc_self
  rw [Set.Subset.antisymm hsub (Set.image_subset_range _ _)]
  exact (isCompact_Icc.image_of_continuousOn c.cont.continuousOn).isClosed

/-- **A preconnected set covered by a finite family of pairwise disjoint closed sets lies in one
of them.** -/
theorem exists_subset_of_preconnected_iUnion {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) (hsne : s.Nonempty) {ι : Type} [Fintype ι] (F : ι → Set X)
    (hF : ∀ i, IsClosed (F i)) (hdisj : Pairwise fun i j => Disjoint (F i) (F j))
    (hsub : s ⊆ ⋃ i, F i) : ∃ i, s ⊆ F i := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i : ι, (s ∩ F i).Nonempty := by
    obtain ⟨x, hx⟩ := hsne
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub hx)
    exact ⟨i, x, hx, hi⟩
  have hcover : s ⊆ F i0 ∪ (⋃ i : {i : ι // i ≠ i0}, F i.1) := by
    intro x hx
    rcases Set.mem_iUnion.mp (hsub hx) with ⟨i, hi⟩
    by_cases hix : i = i0
    · exact Or.inl (hix ▸ hi)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hix⟩, hi⟩)
  have hdisj' : s ∩ (F i0 ∩ ⋃ i : {i : ι // i ≠ i0}, F i.1) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, -, hxu, hxv⟩
    rcases Set.mem_iUnion.mp hxv with ⟨⟨i, hi⟩, hxi⟩
    exact (Set.disjoint_left.mp (hdisj (Ne.symm hi)) hxu) hxi
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hs) (F i0)
      (⋃ i : {i : ι // i ≠ i0}, F i.1) (hF i0)
      (isClosed_iUnion_of_finite fun i => hF i.1) hcover hdisj' with h | h
  · exact ⟨i0, h⟩
  · exfalso
    obtain ⟨x, hx, hxu⟩ := hi0
    rcases Set.mem_iUnion.mp (h hx) with ⟨⟨i, hi⟩, hxi⟩
    exact (Set.disjoint_left.mp (hdisj (Ne.symm hi)) hxu) hxi

/-- **A loop of `F` lying in a finite union of pairwise disjoint simple inessential loops of `F`
is inessential.** -/
theorem not_isEssential_of_range_subset_covered {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} {ι : Type} [Fintype ι]
    (c : ι → Work.CoreTopology.ClosedCurve P)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (c i).γ) (Set.range (c j).γ))
    (hsimp : ∀ i, Work.CoreTopology.IsSimple P (c i))
    (hine : ∀ i, ¬ Work.CoreTopology.IsEssential P (c i))
    (hsub : Set.range γ.γ ⊆ ⋃ i, Set.range (c i).γ) :
    ¬ Work.CoreTopology.IsEssential P γ := by
  obtain ⟨i, hi⟩ := exists_subset_of_preconnected_iUnion (isPreconnected_range γ.cont)
    ⟨γ.γ 0, ⟨0, rfl⟩⟩ (fun i => Set.range (c i).γ) (fun i => isClosed_range_closedCurve (c i))
    hdisj hsub
  exact not_isEssential_of_range_subset_isSimple (hsimp i) hi (hine i)

end

end Work.InnermostDisk
