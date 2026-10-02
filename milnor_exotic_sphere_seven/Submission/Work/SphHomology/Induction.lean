import Submission.Work.SphHomology.Defs
import Submission.Work.SphHomology.Topology
import Submission.Work.SphHomology.BaseCase
import Submission.Work.SphHomology.FinsetUnion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The Mayer–Vietoris induction over a closed cover of the sphere bundle

A finite union of closed subsets of the sphere bundle, each contained in a trivialised piece, has
vanishing relative homology `H_j(S, S∖⋃)` for `j > 8 + (k-1)`.  The induction is over the `Finset`
of pieces, the step being the union step `Work.Cohomology.isZero_relChains_union` of the
Mayer–Vietoris sequence of the pair; the union is written with `Work.SphHomology.finsetUnion`, which
keeps the set-terms syntactically small.
-/

open CategoryTheory AlgebraicTopology Limits
open scoped Topology
open Set Work.TangentClasses

namespace Work.SphHomology

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {k : ℕ}

/-- **The induction step, in `Finset` form.**  If every member of a finite family of closed subsets
of the sphere bundle is contained in a trivialised piece, then the union has vanishing relative
homology above `8 + (k-1)`. -/
theorem isZero_relChains_sphSub_finsetUnion [CompactSpace B] [T2Space B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] (hk : 1 ≤ k)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z) :
    ∀ (t : Finset ι) (C : ι → Set (Work.Thom.SphSub Z)),
      (∀ i ∈ t, IsClosed (C i) ∧ C i ⊆ sphOver Z (Z.baseSet i)) →
      ∀ j, 8 + (k - 1) < j →
        IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z))
          (finsetUnion t C)ᶜ).homology j) := by
  classical
  intro t
  induction t using Finset.cons_induction with
  | empty =>
      intro C _ j _
      rw [finsetUnion_empty, Set.compl_empty]
      exact Work.Cohomology.isZero_relChains_univ _ j
  | cons a t hat ih =>
      intro C hC j hj
      have hKcl : IsClosed (finsetUnion t C) :=
        isClosed_finsetUnion fun i hi => (hC i (Finset.mem_cons_of_mem hi)).1
      have hLcl : IsClosed (C a) := (hC a (Finset.mem_cons_self a t)).1
      have hsub₀ : ∀ i ∈ t, IsClosed (C i) ∧ C i ⊆ sphOver Z (Z.baseSet i) :=
        fun i hi => hC i (Finset.mem_cons_of_mem hi)
      have hKj : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z))
          (finsetUnion t C)ᶜ).homology j) := ih C hsub₀ j hj
      have hKj1 : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z))
          (finsetUnion t C)ᶜ).homology (j + 1)) := ih C hsub₀ (j + 1) (by omega)
      have hLj : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z))
          (C a)ᶜ).homology j) :=
        isZero_relChains_sphSub_of_subset_piece hk Z hZ a hLcl
          (hC a (Finset.mem_cons_self a t)).2 hj
      have hKL' : ∀ i ∈ t, IsClosed (C i ∩ C a) ∧ C i ∩ C a ⊆ sphOver Z (Z.baseSet i) :=
        fun i hi => ⟨(hsub₀ i hi).1.inter hLcl, Set.inter_subset_left.trans (hsub₀ i hi).2⟩
      have hKLj : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z))
          (finsetUnion t C ∩ C a)ᶜ).homology j) := by
        rw [finsetUnion_inter]
        exact ih (fun i => C i ∩ C a) hKL' j hj
      have hKLj1 : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z))
          (finsetUnion t C ∩ C a)ᶜ).homology (j + 1)) := by
        rw [finsetUnion_inter]
        exact ih (fun i => C i ∩ C a) hKL' (j + 1) (by omega)
      have hmain := Work.Cohomology.isZero_relChains_union
        (M := TopCat.of (Work.Thom.SphSub Z)) (K := finsetUnion t C) (L := C a)
        hKcl hLcl j hKj hKj1 hLj hKLj hKLj1
      rw [finsetUnion_cons hat, Set.union_comm]
      exact hmain

end

end Work.SphHomology
