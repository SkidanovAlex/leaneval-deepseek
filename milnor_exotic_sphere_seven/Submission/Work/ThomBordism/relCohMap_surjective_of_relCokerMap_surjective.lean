import Mathlib
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural
import Submission.Work.ThomBordism.relKronH_surjective
import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Cohomology.relChains_free
import Submission.Work.Cohomology.cappedPairMapIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- The chain map of the pair inclusion `(X,A) ⊆ (X,A')` induced by the identity of `X` is the
reduction map `relCokerMap`: a map out of the cokernel of `C_*(A) ⟶ C_*(X)` is determined by its
composite with the projection, and that composite only depends on the identity. -/
lemma relChainsMapOf_id_eq_relCokerMap_aux {X : TopCat} {A B : Set X} (h : A ⊆ B)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ (TopCat.ofHom (ContinuousMap.id X)) =
      g ≫ Work.Cohomology.subtypeIncl X B) :
    Work.Cohomology.relChainsMapOf X X A B (TopCat.ofHom (ContinuousMap.id X)) g w
      = Work.Cohomology.relCokerMap X A B h := by
  apply (cancel_epi (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A))).mp
  rw [Work.Cohomology.cokernel_π_relChainsMapOf, Work.Cohomology.relCokerMap_comp_π,
    TopCat.ofHom_id, Work.Cohomology.chainMap_id', Category.id_comp]

/-- **Naturality of the relative Kronecker pairing for the pair inclusion `(X,A) ⊆ (X,A')`.** -/
lemma relKronH_relCokerMap {X : TopCat} {A A' : Set X} (h : A ⊆ A') (n : ℕ)
    (b : Work.Thom.RelCoh ℤ n X A')
    (z : ↥((Work.Cohomology.relChains X A).homology n)) :
    (Work.Tubular.relKronH X A n)
        ((Work.Thom.relCohMap (ContinuousMap.id X) A A' h ℤ n).hom b) z
      = (Work.Tubular.relKronH X A' n) b
          ((HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A A' h) n).hom z) := by
  have hn := Work.ThomBordism.FrameSigns.relKronH_natural (X := X) (Y := X) (A := A) (B := A')
    (f := ContinuousMap.id X) h n b z
  rw [relChainsMapOf_id_eq_relCokerMap_aux h _ _] at hn
  exact hn

theorem relCohMap_surjective_of_relCokerMap_surjective {X : TopCat} {A A' : Set X} (h : A ⊆ A') (n : ℕ)
    (hj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X A A' h) n).hom)
    (hji : Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X A A' h) n).hom)
    (hker : ∀ b : Work.Thom.RelCoh ℤ n X A,
      (∀ z, Work.Tubular.relKronH X A n b z = 0) → b = 0) :
    Function.Surjective (Work.Thom.relCohMap (ContinuousMap.id X) A A' h ℤ n).hom := by
  intro b
  -- the homology map induced by the pair inclusion
  let E : ↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ]
      ↥((Work.Cohomology.relChains X A').homology n) :=
    (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A A' h) n).hom
  have hE : Function.Surjective E := hj
  have hEi : Function.Injective E := hji
  have hEbij : Function.Bijective E := ⟨hEi, hE⟩
  -- the functional `χ` of the pairing with `b`, transported to the target by the inverse of `E`
  let χ : ↥((Work.Cohomology.relChains X A).homology n) →ₗ[ℤ] ℤ :=
    Work.Tubular.relKronH X A n b
  let ψ : ↥((Work.Cohomology.relChains X A').homology n) →ₗ[ℤ] ℤ :=
    χ.comp (LinearEquiv.ofBijective E hEbij).symm.toLinearMap
  have hψ : ∀ z, ψ (E z) = χ z := by
    intro z
    show χ ((LinearEquiv.ofBijective E hEbij).symm (E z)) = χ z
    have hsymm : (LinearEquiv.ofBijective E hEbij).symm (E z) = z :=
      LinearEquiv.ofBijective_symm_apply_apply E z
    rw [hsymm]
  -- the pairing is surjective on the larger pair
  have hsurj : Function.Surjective (Work.Tubular.relKronH X A' n) :=
    relKronH_surjective X A' n (fun m => Work.Cohomology.relChains_free X A' m)
  obtain ⟨b', hb'⟩ := hsurj ψ
  refine ⟨b', ?_⟩
  have hpair : ∀ z, (Work.Tubular.relKronH X A n)
      ((Work.Thom.relCohMap (ContinuousMap.id X) A A' h ℤ n).hom b') z
      = (Work.Tubular.relKronH X A n) b z := by
    intro z
    rw [relKronH_relCokerMap h n b' z, hb']
    exact hψ z
  have hzero : ∀ z, (Work.Tubular.relKronH X A n)
      ((Work.Thom.relCohMap (ContinuousMap.id X) A A' h ℤ n).hom b' - b) z = 0 := by
    intro z
    rw [map_sub, LinearMap.sub_apply, hpair z, sub_self]
  have h0 := hker ((Work.Thom.relCohMap (ContinuousMap.id X) A A' h ℤ n).hom b' - b) hzero
  exact sub_eq_zero.mp h0

end

end Work.ThomBordism
