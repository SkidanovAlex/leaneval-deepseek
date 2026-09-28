import Mathlib
import Submission.Work.Serre.Csr.Tools

/-!
# The five lemma for a map of pairs in the preimage form

`Work.Serre.nonempty_homologyIso_relChains_incl`: for subsets `A₀ ⊆ A₁`, `B₀ ⊆ B₁` (with
`A₀ ⊆ B₀`, `A₁ ⊆ B₁`) of a space, if the inclusions `↥B₀ → ↥B₁` and `↥A₀ → ↥A₁` are
quasi-isomorphisms then so is the induced map of relative chain complexes; in particular the
relative homology groups are isomorphic in every degree.  This is the form in which the per-cell
computation of `Work.Serre.csrPerCell` compares the relative homology of the pairs
`(π⁻¹W, π⁻¹V)`.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

namespace Work.Serre

noncomputable section

/-- **The five lemma for a map of pairs given in the "preimage" form.**  For subsets
`A₀ ⊆ B₀`, `A₁ ⊆ B₁` of a space `X` with `A₀ ⊆ A₁` and `B₀ ⊆ B₁`, if the inclusions
`↥B₀ → ↥B₁` and `↥A₀ → ↥A₁` are quasi-isomorphisms, then so is the induced map of relative chain
complexes; in particular the relative homology groups are isomorphic in every degree. -/
theorem nonempty_homologyIso_relChains_incl {X : Type} [TopologicalSpace X]
    {A₀ A₁ B₀ B₁ : Set X} (hA : A₀ ⊆ A₁) (hB : B₀ ⊆ B₁) (hA₀ : A₀ ⊆ B₀) (hA₁ : A₁ ⊆ B₁)
    (hf : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥B₀) (TopCat.of ↥B₁)
        (TopCat.ofHom (subtypeInclCM hB))) k))
    (hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥A₀) (TopCat.of ↥A₁)
        (TopCat.ofHom (subtypeInclCM hA))) k)) (m : ℕ) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥B₀)
        {x : ↥B₀ | (x : X) ∈ A₀}).homology m ≅
      (Work.Cohomology.relChains (TopCat.of ↥B₁) {x : ↥B₁ | (x : X) ∈ A₁}).homology m) := by
  have hw : Work.Cohomology.subtypeIncl (TopCat.of ↥B₀) {x : ↥B₀ | (x : X) ∈ A₀}
        ≫ TopCat.ofHom (subtypeInclCM hB)
      = TopCat.ofHom (doubleSubtypeInclCM hA hB)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥B₁) {x : ↥B₁ | (x : X) ∈ A₁} := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    rfl
  have hg' : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of {x : ↥B₀ | (x : X) ∈ A₀})
        (TopCat.of {x : ↥B₁ | (x : X) ∈ A₁}) (TopCat.ofHom (doubleSubtypeInclCM hA hB))) k) :=
    isIso_chainMap_doubleSubtype (X := X) (A₀ := A₀) (A₁ := A₁) (B₀ := B₀) (B₁ := B₁)
      hA hB hA₀ hA₁ hg
  have hf' : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥B₀) (TopCat.of ↥B₁)
        (TopCat.ofHom (subtypeInclCM hB))) k) := hf
  have hIso : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
      (TopCat.of ↥B₀) (TopCat.of ↥B₁) {x : ↥B₀ | (x : X) ∈ A₀} {x : ↥B₁ | (x : X) ∈ A₁}
      (TopCat.ofHom (subtypeInclCM hB)) (TopCat.ofHom (doubleSubtypeInclCM hA hB)) hw) m) := by
    refine Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := TopCat.of ↥B₀)
      (Y := TopCat.of ↥B₁) {x : ↥B₀ | (x : X) ∈ A₀} {x : ↥B₁ | (x : X) ∈ A₁}
      (TopCat.ofHom (subtypeInclCM hB)) (TopCat.ofHom (doubleSubtypeInclCM hA hB)) hw m ?_ ?_
    · intro k
      exact hf' k
    · intro k
      exact hg' k
  exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
    (TopCat.of ↥B₀) (TopCat.of ↥B₁) {x : ↥B₀ | (x : X) ∈ A₀} {x : ↥B₁ | (x : X) ∈ A₁}
    (TopCat.ofHom (subtypeInclCM hB)) (TopCat.ofHom (doubleSubtypeInclCM hA hB)) hw) m)⟩

end

end Work.Serre
