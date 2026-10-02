import Submission.Work.SphHomology.Defs
import Submission.Work.SphHomology.Topology
import Submission.Work.SphHomology.Induction
import Submission.Work.Cohomology.relChains_empty_homology_iso

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
# Vanishing of the homology of the sphere bundle above `8 + (k-1)`

For a Euclidean real bundle `Z` of rank `k ≥ 1` over a compact Hausdorff base charted on `ℝ⁸`, the
singular homology of the sphere bundle `S(Z)` vanishes in all degrees `> 8 + (k-1)`: the sphere
bundle is covered by finitely many pieces, each of which is a product of an open piece of the base
with `S^{k-1}`, and the Mayer–Vietoris induction gives the bound.
-/

open CategoryTheory AlgebraicTopology Limits
open scoped Topology
open Set Work.TangentClasses

namespace Work.SphHomology

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {k : ℕ}

/-- **Vanishing of the homology of the sphere bundle above the dimension.**  Let `Z` be a Euclidean
real bundle of rank `k ≥ 1` over a compact Hausdorff base charted on `ℝ⁸`.  Then the singular
homology with `ℤ` coefficients of the sphere bundle `S(Z)` vanishes in every degree `> 8 + (k-1)`. -/
theorem isZero_homology_sphSub [CompactSpace B] [T2Space B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] (hk : 1 ≤ k)
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (hZ : Work.Thom.IsEuclidean Z)
    (n : ℕ) (hn : 8 + (k - 1) < n) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Thom.SphSub Z))).homology n) := by
  classical
  obtain ⟨s, v, hvcl, hvsub, hvuniv⟩ := closed_refinement Z
  let A : ι → Set (Work.Thom.SphSub Z) := fun i => sphOver Z (v i)
  have hA : ∀ i ∈ s, IsClosed (A i) ∧ A i ⊆ sphOver Z (Z.baseSet i) :=
    fun i _ => ⟨isClosed_sphOver Z (hvcl i), sphOver_mono Z (hvsub i)⟩
  have hkeys : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.Thom.SphSub Z))
      (finsetUnion s A)ᶜ).homology n) :=
    isZero_relChains_sphSub_finsetUnion hk Z hZ s A hA n hn
  have hcover : finsetUnion s A = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    have hp : Z.proj (p : Z.TotalSpace) ∈ ⋃ i ∈ s, v i := by rw [hvuniv]; exact mem_univ _
    obtain ⟨i, his, hpi⟩ := mem_iUnion₂.mp hp
    exact mem_finsetUnion.mpr ⟨i, his, hpi⟩
  rw [hcover, Set.compl_univ] at hkeys
  haveI := Work.Cohomology.relChains_empty_homology_iso (TopCat.of (Work.Thom.SphSub Z)) n
  exact IsZero.of_iso hkeys (asIso (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains (TopCat.of (Work.Thom.SphSub Z)) ∅)) n))

end

end Work.SphHomology
