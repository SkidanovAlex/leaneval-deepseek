import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.RepProjection
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree
import Submission.Work.ORBassSerre.Tree.Geodesic.mem_vertices_comp
import Submission.Work.ORBassSerre.Tree.Geodesic.mem_vertices_reverse
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_vertices_subset_of_reducesTo
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre

universe u

variable {G : Type u} {V : Type u} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-!
# The geodesic between two vertex representatives consists of representatives

Let `G` act on a tree `V` and let `d : TreeDatum G V` be the data of a spanning tree of the
quotient graph lifted to `V` (see `TreeDatum`).  The chosen representatives `d.vert A` of the
vertex orbits form a set `repSet d`, and for every vertex orbit `A ≠ d.root` the lifting arrow
`d.parArrow A` is an actual edge of `V` joining `d.vert (d.par A)` to `d.vert A`.

Consequently `d.vert A` is joined to the root representative `d.vert d.root` by a walk whose
vertices are all representatives (walk up the `par`-chain); the rank function strictly decreases
along `par`, so the walk terminates at the root.  Any two representatives are therefore joined by
a walk lying in `repSet d`, and since `V` is a tree any reduced path between them is the unique
reduced path, hence coincides with the reduction of that walk and so also lies in `repSet d`.

This proves that the geodesic `reducedSpan (d.vert A) (d.vert B)` is contained in `repSet d`.
-/

namespace TreeDatum

variable (d : TreeDatum G V)

/-- The plumbing edge of `A` (for `A ≠ d.root`), directed from the representative of `A`
towards the representative of its parent orbit. -/
noncomputable def upArrow (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ d.root) :
    d.vert A ⟶ d.vert (d.par A) :=
  Quiver.homOfEq (Quiver.reverse ((d.parArrow A hA).hom))
    (d.parArrow_right A hA) (d.parArrow_left A hA)

/-- **Every representative is joined to the root representative by a walk in `repSet d`.**

Walk from `A` up the `par`-chain; the rank strictly decreases, so the walk terminates at the
root, and every vertex visited is by construction a chosen representative. -/
theorem exists_upPath (A : Work.ORBassSerre.orbitV G V) :
    ∃ p : Quiver.Path (d.vert A) (d.vert d.root), ∀ v ∈ p.vertices, v ∈ repSet d := by
  have h : ∀ n, ∀ A : Work.ORBassSerre.orbitV G V, d.rank A = n →
      ∃ p : Quiver.Path (d.vert A) (d.vert d.root), ∀ v ∈ p.vertices, v ∈ repSet d := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hAn
      by_cases hroot : A = d.root
      · subst hroot
        refine ⟨Quiver.Path.nil, ?_⟩
        intro v hv
        rw [Quiver.Path.vertices_nil, List.mem_singleton] at hv
        rw [hv]
        exact vert_mem_repSet d d.root
      · have hlt : d.rank (d.par A) < n := by
          rw [← hAn]; exact d.rank_par_lt A hroot
        obtain ⟨p, hp⟩ := ih (d.rank (d.par A)) hlt (d.par A) rfl
        refine ⟨(d.upArrow A hroot).toPath.comp p, ?_⟩
        intro v hv
        rw [Work.ORBassSerre.Tree.Geodesic.mem_vertices_comp] at hv
        rcases hv with hv | hv
        · rw [Quiver.Path.vertices_toPath] at hv
          have hv' : v = d.vert A ∨ v = d.vert (d.par A) := by simpa using hv
          rcases hv' with rfl | rfl
          · exact vert_mem_repSet d A
          · exact vert_mem_repSet d (d.par A)
        · exact hp v hv
  exact h (d.rank A) A rfl

/-- **Any two representatives are joined by a walk in `repSet d`**: walk from the first to the
root, then back down to the second. -/
theorem exists_repWalk (A B : Work.ORBassSerre.orbitV G V) :
    ∃ q : Quiver.Path (d.vert A) (d.vert B), ∀ v ∈ q.vertices, v ∈ repSet d := by
  obtain ⟨pA, hA⟩ := d.exists_upPath A
  obtain ⟨pB, hB⟩ := d.exists_upPath B
  refine ⟨pA.comp pB.reverse, ?_⟩
  intro v hv
  rw [Work.ORBassSerre.Tree.Geodesic.mem_vertices_comp] at hv
  rcases hv with hv | hv
  · exact hA v hv
  · rw [Work.ORBassSerre.Tree.Geodesic.mem_vertices_reverse] at hv
    exact hB v hv

end TreeDatum

theorem reducedSpan_vert_subset_repSet {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V)
    (A B : Work.ORBassSerre.orbitV G V) :
    Work.ORBassSerre.reducedSpan (d.vert A) (d.vert B) ⊆
      Work.ORLocInd.FKSKernel.Kurosh.repSet d := by
  intro v hv
  rw [Work.ORBassSerre.mem_reducedSpan_iff] at hv
  obtain ⟨p, hp_red, hpv⟩ := hv
  obtain ⟨q, hq⟩ := d.exists_repWalk A B
  obtain ⟨r, hqr, hr_red⟩ :=
    Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced q
  have heq : p = r := Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree hT hp_red hr_red
  rw [heq] at hpv
  exact hq v (Work.ORBassSerre.Tree.Reduction.qpath_vertices_subset_of_reducesTo hqr v hpv)

end Work.ORLocInd.FKSKernel.Kurosh
