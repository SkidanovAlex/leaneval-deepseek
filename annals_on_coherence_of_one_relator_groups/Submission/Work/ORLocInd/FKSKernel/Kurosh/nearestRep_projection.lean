import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.RepProjection
import Submission.Work.ORBassSerre.Tree.Seg.exists_median
import Submission.Work.ORBassSerre.Tree.Seg.reducedSpan_comm
import Submission.Work.ORBassSerre.Tree.Seg.geodesic_length_le_of_mem_reducedSpan
import Submission.Work.ORBassSerre.Tree.Seg.eq_of_mem_reducedSpan_of_geodesic_length_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The projection onto the set of chosen representatives

Let `G` act on a tree `V` and let `d : TreeDatum G V` be the spanning tree datum of the action,
with `repSet d = Set.range d.vert` the set of chosen representatives of the vertex orbits.

The hypothesis `hbetween` says that the geodesic segment between two representatives consists of
representatives, i.e. `repSet d` is *convex* (in the sense that it contains the reduced span of any
two of its points).

Under this hypothesis the nearest representative `nearestRep hT d v` of a vertex `v` behaves like
the orthogonal projection onto a convex set in a tree:

* it is a representative;
* it lies on the geodesic from `v` to *any* representative;
* it fixes every representative;
* it is the only representative lying on the geodesic from `v` to itself.

The mathematical heart is the last three points together with the tree fact that the nearest point
of a convex subset of a tree lies on the geodesic joining the point to any point of the subset: for
the median `m` of the triple `(v, r, a)`, where `r` is the nearest representative and `a` any
element of the convex set, `m` lies in the convex set and on the geodesic from `v` to `r`, so
`dist v m ≥ dist v r` (minimality) and `dist v m ≤ dist v r` (lying on the segment); hence
`m = r` and `r` lies on the geodesic from `v` to `a`.
-/

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre

universe u

section Aux

variable {W : Type*} [Quiver W] [Quiver.HasInvolutiveReverse W]

/-- In a tree, the only vertex of the trivial segment from `a` to `a` is `a`. -/
private theorem aux_eq_of_mem_reducedSpan_self (hT : IsTree W) {a c : W}
    (hc : c ∈ reducedSpan a a) : c = a := by
  obtain ⟨p, hp, hcp⟩ := hc
  have hnil : p = Quiver.Path.nil := hT.2 a p hp
  rw [hnil] at hcp
  simpa using hcp

/-- **The nearest point of a convex subset of a tree lies on every segment to the subset.**

If `R` is convex, `r ∈ R` is nearest to `v` among the points of `R`, and `a ∈ R`, then `r` lies on
the geodesic from `v` to `a`. -/
private theorem aux_mem_reducedSpan_of_convex_of_nearest (hT : IsTree W) {R : Set W}
    (hconv : ∀ a ∈ R, ∀ b ∈ R, reducedSpan a b ⊆ R)
    {v r : W} (hr : r ∈ R) (hmin : ∀ s ∈ R, dist hT v r ≤ dist hT v s)
    {a : W} (ha : a ∈ R) : r ∈ reducedSpan v a := by
  -- the median of `v`, `r` and `a` lies on the three segments joining them pairwise
  obtain ⟨m, hm₁, hm₂, hm₃⟩ := Work.ORBassSerre.Tree.Seg.exists_median (hT := hT) v r a
  -- it lies in `R`, because it lies on the segment from `r` to `a`
  have hmR : m ∈ R := hconv r hr a ha hm₂
  have h₁ : dist hT v r ≤ dist hT v m := hmin m hmR
  have h₂ : dist hT v m ≤ dist hT v r :=
    Work.ORBassSerre.Tree.Seg.geodesic_length_le_of_mem_reducedSpan hT hm₁
  have hmr : m = r :=
    Work.ORBassSerre.Tree.Seg.eq_of_mem_reducedSpan_of_geodesic_length_eq hT hm₁
      (le_antisymm h₂ h₁)
  -- hence `r = m` lies on the segment from `a` to `v`, i.e. from `v` to `a`
  rw [hmr] at hm₃
  rwa [Work.ORBassSerre.Tree.Seg.reducedSpan_comm a v] at hm₃

end Aux

theorem nearestRep_projection {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V)
    (hbetween : ∀ A B : Work.ORBassSerre.orbitV G V,
      Work.ORBassSerre.reducedSpan (d.vert A) (d.vert B)
        ⊆ Work.ORLocInd.FKSKernel.Kurosh.repSet d) :
    (∀ v : V, Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v
        ∈ Work.ORLocInd.FKSKernel.Kurosh.repSet d) ∧
    (∀ v : V, ∀ A, Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v
        ∈ Work.ORBassSerre.reducedSpan v (d.vert A)) ∧
    (∀ A, Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d (d.vert A) = d.vert A) ∧
    (∀ v : V, ∀ C, d.vert C ∈ Work.ORBassSerre.reducedSpan v
        (Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v) →
      d.vert C = Work.ORLocInd.FKSKernel.Kurosh.nearestRep hT d v) := by
  classical
  -- `repSet d` is convex: the segment between two representatives consists of representatives
  have hconv : ∀ a ∈ repSet d, ∀ b ∈ repSet d, reducedSpan a b ⊆ repSet d := by
    rintro a ⟨A, rfl⟩ b ⟨B, rfl⟩
    exact hbetween A B
  -- minimality of the nearest representative, for any element of `repSet d`
  have hmin : ∀ v : V, ∀ s ∈ repSet d, dist hT v (nearestRep hT d v) ≤ dist hT v s := by
    rintro v s ⟨B, rfl⟩
    exact nearestRep_le hT d v B
  -- the projection lies on the segment from `v` to any representative
  have hproj : ∀ v : V, ∀ a ∈ repSet d, nearestRep hT d v ∈ reducedSpan v a :=
    fun v a ha => aux_mem_reducedSpan_of_convex_of_nearest hT hconv
      (nearestRep_mem hT d v) (hmin v) ha
  refine ⟨fun v => nearestRep_mem hT d v, fun v A => hproj v (d.vert A) (vert_mem_repSet d A),
    fun A => ?_, fun v C hC => ?_⟩
  · -- a representative is the nearest representative of itself
    exact aux_eq_of_mem_reducedSpan_self hT (hproj (d.vert A) (d.vert A) (vert_mem_repSet d A))
  · -- no other representative lies between `v` and its nearest representative
    have h₁ : dist hT v (nearestRep hT d v) ≤ dist hT v (d.vert C) :=
      hmin v (d.vert C) (vert_mem_repSet d C)
    have h₂ : dist hT v (d.vert C) ≤ dist hT v (nearestRep hT d v) :=
      Work.ORBassSerre.Tree.Seg.geodesic_length_le_of_mem_reducedSpan hT hC
    exact Work.ORBassSerre.Tree.Seg.eq_of_mem_reducedSpan_of_geodesic_length_eq hT hC
      (le_antisymm h₂ h₁)

end Work.ORLocInd.FKSKernel.Kurosh
