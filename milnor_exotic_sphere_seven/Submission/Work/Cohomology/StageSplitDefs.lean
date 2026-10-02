import Mathlib
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.pd_triple

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Local homology of compact subsets of `ℝ^N`, and the stage splitting

For a compact set `K ⊆ ℝ^N` the "local homology" `LK K = H_N(ℝ^N, ℝ^N ∖ K)` is (for `N ≥ 2`)
isomorphic to `H_{N-1}(Kᶜ)`, and the map `LK K' → LK K` induced by an inclusion `K ⊆ K'` of compact
sets is the "stage map" of the complement.  This file sets up the notation used in
`Submission/Work/Cohomology/euclidean_stage_split.lean`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {N : ℕ}

/-- The local homology of `K ⊆ ℝ^N`, in the flat model `H_N(ℝ^N, ℝ^N ∖ K)`:
this is the `N`-th relative singular homology of the pair `(ℝ^N, ℝ^N ∖ K)`. -/
abbrev LKC (N : ℕ) (K : Set (EuclideanSpace ℝ (Fin N))) : ModuleCat ℤ :=
  (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K}).homology N

/-- The local homology of `K ⊆ ℝ^N` as a `ℤ`-module. -/
abbrev LK (N : ℕ) (K : Set (EuclideanSpace ℝ (Fin N))) : Type := ↥(LKC N K)

/-- **The stage map** `LK K' → LK K` induced by an inclusion `K ⊆ K'` of compact sets (it is the
map of relative homology of the pairs `(ℝ^N, ℝ^N∖K') → (ℝ^N, ℝ^N∖K)`). -/
def lkMap {K K' : Set (EuclideanSpace ℝ (Fin N))} (h : K ⊆ K') : LK N K' →ₗ[ℤ] LK N K :=
  (HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
    {y | y ∉ K'} {y | y ∉ K} (fun y hy hyK => hy (h hyK))) N).hom

/-- Functoriality of the stage maps. -/
theorem lkMap_comp {K K' K'' : Set (EuclideanSpace ℝ (Fin N))} (h₁ : K ⊆ K') (h₂ : K' ⊆ K'') :
    (lkMap (N := N) h₁).comp (lkMap (N := N) h₂) = lkMap (h₁.trans h₂) := by
  have g₁ : ({y : EuclideanSpace ℝ (Fin N) | y ∉ K''} : Set (EuclideanSpace ℝ (Fin N)))
      ⊆ {y : EuclideanSpace ℝ (Fin N) | y ∉ K'} := fun y hy hyK' => hy (h₂ hyK')
  have g₂ : ({y : EuclideanSpace ℝ (Fin N) | y ∉ K'} : Set (EuclideanSpace ℝ (Fin N)))
      ⊆ {y : EuclideanSpace ℝ (Fin N) | y ∉ K} := fun y hy hyK => hy (h₁ hyK)
  have key : HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {y | y ∉ K''} {y | y ∉ K'} g₁) N
      ≫ HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {y | y ∉ K'} {y | y ∉ K} g₂) N
      = HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {y | y ∉ K''} {y | y ∉ K} (g₁.trans g₂)) N := by
    rw [← HomologicalComplex.homologyMap_comp, relCokerMap_comp]
  have key2 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap
        (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K'} {y | y ∉ K} g₂) N) ∘ₗ
      ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap
        (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K''} {y | y ∉ K'} g₁) N)
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap
        (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K''} {y | y ∉ K} (g₁.trans g₂)) N) := by
    have hh := congrArg ModuleCat.Hom.hom key
    rwa [ModuleCat.hom_comp] at hh
  have hcongr : relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K''} {y | y ∉ K}
        (g₁.trans g₂)
      = relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K''} {y | y ∉ K}
        (fun y hy hyK => hy ((h₁.trans h₂) hyK)) := by
    have hh : (g₁.trans g₂) = (fun y hy hyK => hy ((h₁.trans h₂) hyK)) :=
      funext fun y => funext fun hy => funext fun hyK => Subsingleton.elim _ _
    rw [hh]
  rw [lkMap, lkMap]
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap
        (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K'} {y | y ∉ K} g₂) N) ∘ₗ
      ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap
        (TopCat.of (EuclideanSpace ℝ (Fin N))) {y | y ∉ K''} {y | y ∉ K'} g₁) N))
    = lkMap (h₁.trans h₂)
  rw [key2]
  rw [lkMap]

/-- The singleton is contained in a set containing the point. -/
theorem singleton_subset_iff_mem {K : Set (EuclideanSpace ℝ (Fin N))}
    {x : EuclideanSpace ℝ (Fin N)} (h : x ∈ K) : ({x} : Set _) ⊆ K :=
  Set.singleton_subset_iff.mpr h

end

end Work.Cohomology
