import Mathlib
import Submission.Work.InnermostDisk.Slicing

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **Assembling a slicing of a finite disjoint union out of slicings of its pieces.**

The index type of the assembled slicing is the sigma type `Σ i, (Sl i).ι` of the component indices
of the pieces; the rank function is the rank in the piece.  The only place where the separation of
the pieces is used is `covers`: the range of a closed curve is preconnected, so (being covered by
finitely many pairwise disjoint closed sets) it lies in a single piece. -/
def sphereSlicing_iUnion {P : Work.CoreTopology.ParamTorus} {κ : Type} [Fintype κ]
    (S : κ → Set R3) (Sl : ∀ i : κ, Work.InnermostDisk.SphereSlicing P (S i))
    (hc : ∀ i : κ, IsClosed (S i))
    (hdisj : ∀ i j : κ, i ≠ j → Disjoint (S i) (S j)) :
    Work.InnermostDisk.SphereSlicing P (⋃ i, S i) where
  ι := Sigma fun i : κ => (Sl i).ι
  fintype := inferInstance
  c := fun k => (Sl k.1).c k.2
  simple := by rintro ⟨i, a⟩; exact (Sl i).simple a
  disjoint := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ hne
    rcases eq_or_ne i i' with rfl | hii
    · exact (Sl i).disjoint (fun h => hne (by subst h; rfl))
    · exact (hdisj i i' hii).mono (fun w ⟨t, ht⟩ => ht ▸ (Sl i).mem a t)
        (fun w ⟨t, ht⟩ => ht ▸ (Sl i').mem a' t)
  mem := by
    rintro ⟨i, a⟩ t
    exact Set.mem_iUnion.mpr ⟨i, (Sl i).mem a t⟩
  covers := by
    intro γ hγ
    have hsub : Set.range γ.γ ⊆ ⋃ i, S i := fun z ⟨t, ht⟩ => ht ▸ hγ t
    obtain ⟨i, hi⟩ :=
      Work.InnermostDisk.exists_subset_of_preconnected_iUnion (isPreconnected_range γ.cont)
        ⟨γ.γ 0, ⟨0, rfl⟩⟩ S hc (fun i j hij => hdisj i j hij) hsub
    obtain ⟨a, ha⟩ := (Sl i).covers γ (fun t => hi ⟨t, rfl⟩)
    exact ⟨⟨i, a⟩, ha⟩
  disc := fun k => (Sl k.1).disc k.2
  disc_inj := by rintro ⟨i, a⟩; exact (Sl i).disc_inj a
  disc_boundary := by rintro ⟨i, a⟩ θ; exact (Sl i).disc_boundary a θ
  disc_mem := by
    rintro ⟨i, a⟩ z
    exact Set.mem_iUnion.mpr ⟨i, (Sl i).disc_mem a z⟩
  rank := fun k => (Sl k.1).rank k.2
  inside := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ ⟨z, hz, hmem⟩
    rcases eq_or_ne i i' with rfl | hii
    · exact (Sl i).inside a a' ⟨z, hz, hmem⟩
    · exfalso
      obtain ⟨s, hs⟩ := hmem
      exact (Set.disjoint_left.mp (hdisj i i' hii)) ((Sl i).disc_mem a z)
        (hs ▸ (Sl i').mem a' s)
  inside_subset := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ ⟨z, hz, hmem⟩
    rcases eq_or_ne i i' with rfl | hii
    · exact (Sl i).inside_subset a a' ⟨z, hz, hmem⟩
    · exfalso
      obtain ⟨s, hs⟩ := hmem
      exact (Set.disjoint_left.mp (hdisj i i' hii)) ((Sl i).disc_mem a z)
        (hs ▸ (Sl i').mem a' s)
  covers_interior := by
    rintro ⟨i, a⟩ z hz hc'
    obtain ⟨a', ha'⟩ := (Sl i).covers_interior a z hz hc'
    exact ⟨⟨i, a'⟩, ha'⟩

/-- **A slicing of a finite disjoint union of separated pieces, from slicings of the pieces.**

`Work.Drive.Mono.sphereSlicing_union` assembles a `Work.InnermostDisk.SphereSlicing` of a *union of
two* separated closed sets from slicings of the two parts.  The level frontier of the tilted sweep can
have *three* pieces (a single sphere is not enough: a three-component counterexample at a corner of
the wall with the boundary of the box was machine-checked in this workspace), so the two-piece
assembly has to be extended to a finite family.

`S : ι → Set R3` is a finite family of pairwise disjoint closed sets and `Sl i` is a slicing of the
piece `S i`; the components of the slicings are put side by side, and because the pieces are closed,
disjoint and finite in number the range of a closed curve contained in the union (which is
preconnected) lies in one single piece.

Useful in-scope bricks: `Work.InnermostDisk.exists_subset_of_preconnected_iUnion`
(`Submission/Work/InnermostDisk/not_isEssential_of_range_subset_covered.lean`) for the finite
decomposition of a preconnected set, and `Work.Drive.Mono.sphereSlicing_union`
(`Submission/Work/Drive/Mono/TiltedTraceDataWExists_holds.lean`) for the `n = 2` case of every field
including the rank offset. -/
theorem sphereSlicing_union_family {P : Work.CoreTopology.ParamTorus} {ι : Type} [Fintype ι]
    (S : ι → Set LeanEval.KnotTheory.PardonDistortion.R3)
    (Sl : ∀ i : ι, Work.InnermostDisk.SphereSlicing P (S i))
    (hc : ∀ i : ι, IsClosed (S i))
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (S i) (S j)) :
    Nonempty (Work.InnermostDisk.SphereSlicing P (⋃ i, S i)) :=
  ⟨sphereSlicing_iUnion S Sl hc hdisj⟩

end

end Work.Drive.Mono
