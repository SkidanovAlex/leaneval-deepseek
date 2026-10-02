import Submission.Work.SphHomology.Defs
import Submission.Work.Thom.DiscSphereTopology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Elementary topology of the sphere bundle of a Euclidean bundle

* `Work.SphHomology.sphSub_homeo_sphereInDisc` — the sphere bundle as a subspace of the total space
  and as a subspace of the disc bundle are the same space;
* `Work.SphHomology.compactSpace_sphSub` — the sphere bundle of a Euclidean bundle over a compact
  base is compact (a closed subspace of the compact disc bundle);
* `Work.SphHomology.closed_refinement` — a compact base admits a finite closed cover, each member of
  which lies in one trivialising set of `Z` (the shrinking lemma applied to a finite subcover).
-/

open scoped Topology
open Set
open Work.TangentClasses

namespace Work.SphHomology

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*}

/-- **The two models of the sphere bundle agree.**  The sphere bundle as a subspace of the total
space (`Work.Thom.SphSub`) is homeomorphic to the unit sphere bundle inside the closed disc bundle
(`Work.Thom.sphereInDisc`). -/
theorem sphSub_homeo_sphereInDisc (Z : RealBundle B F ι) :
    Nonempty (Work.Thom.SphSub Z ≃ₜ ↥(Work.Thom.sphereInDisc Z)) := by
  refine ⟨{ toFun := fun p =>
              ⟨⟨(p : Z.TotalSpace), Work.Thom.sphereSet_subset_closedDiscSet Z p.2⟩, p.2⟩
            invFun := fun q => ⟨(q.1 : Z.TotalSpace), q.2⟩
            left_inv := fun p => by rfl
            right_inv := fun q => by rfl
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }⟩

/-- **The sphere bundle of a Euclidean bundle over a compact base is compact.**  It is a closed
subspace of the compact closed disc bundle. -/
theorem compactSpace_sphSub [CompactSpace B] [T2Space B] [FiniteDimensional ℝ F]
    (Z : RealBundle B F ι) (hZ : Work.Thom.IsEuclidean Z) : CompactSpace (Work.Thom.SphSub Z) := by
  have hc : IsCompact (Work.Thom.sphereSet Z) :=
    (Work.Tubular.isCompact_closedDiscSet Z hZ).of_isClosed_subset
      (Work.Thom.sphereSet_isClosed hZ) (Work.Thom.sphereSet_subset_closedDiscSet Z)
  exact isCompact_iff_compactSpace.mp hc

/-- **A finite closed cover refined into trivialising sets.**  For a Euclidean bundle `Z` over a
compact Hausdorff base, there is a finite set `s` of indices and a family of closed sets `v i`,
each contained in the trivialising set `Z.baseSet i`, whose union over `i ∈ s` is the base. -/
theorem closed_refinement [CompactSpace B] [T2Space B] (Z : RealBundle B F ι) :
    ∃ (s : Finset ι) (v : ι → Set B),
      (∀ i, IsClosed (v i)) ∧ (∀ i, v i ⊆ Z.baseSet i) ∧ (⋃ i ∈ s, v i) = Set.univ := by
  classical
  obtain ⟨s, hs⟩ := (isCompact_univ (X := B)).elim_finite_subcover Z.baseSet
    (fun i => Z.isOpen_baseSet i) (fun x _ => mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩)
  have hcov : (Set.univ : Set B) ⊆ ⋃ j : {i // i ∈ s}, Z.baseSet (j : ι) := by
    intro x _
    obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact mem_iUnion.mpr ⟨⟨i, his⟩, hxi⟩
  have hfin : ∀ x ∈ (Set.univ : Set B), {j : {i // i ∈ s} | x ∈ Z.baseSet (j : ι)}.Finite :=
    fun x _ => Set.toFinite _
  obtain ⟨w, hwuniv, hwclosed, hwsub⟩ := exists_subset_iUnion_closed_subset
    (s := (Set.univ : Set B)) (u := fun j : {i // i ∈ s} => Z.baseSet (j : ι))
    isClosed_univ (fun j => Z.isOpen_baseSet (j : ι)) hfin hcov
  refine ⟨s, fun i => if h : i ∈ s then w ⟨i, h⟩ else ∅, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i ∈ s
    · simp only [dif_pos h]; exact hwclosed ⟨i, h⟩
    · simp only [dif_neg h]; exact isClosed_empty
  · intro i
    by_cases h : i ∈ s
    · simp only [dif_pos h]; exact hwsub ⟨i, h⟩
    · simp only [dif_neg h]; exact empty_subset _
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hwuniv (mem_univ x))
    exact mem_iUnion₂.mpr ⟨j.1, j.2, by simp only [dif_pos j.2]; exact hxj⟩

end

end Work.SphHomology

namespace Work.SphHomology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- The double complement of a set, as a homeomorphism: the two subtypes have the same underlying
points. -/
def complComplHomeo (s : Set X) : ↥(sᶜᶜ) ≃ₜ ↥s where
  toFun x := ⟨(x : X), of_not_not x.2⟩
  invFun y := ⟨(y : X), fun h => h y.2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The double complement of a set is homeomorphic to the set. -/
theorem compl_compl_homeo (s : Set X) : Nonempty (↥(sᶜᶜ) ≃ₜ ↥s) :=
  ⟨complComplHomeo s⟩

@[simp] theorem complComplHomeo_apply (s : Set X) (x : ↥(sᶜᶜ)) :
    ((complComplHomeo s x : ↥s) : X) = (x : X) := rfl

end

end Work.SphHomology
