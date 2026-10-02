import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.B1Rel.relKronMapR_natural
import Submission.Work.Serre.csrDefs
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open CategoryTheory

/-- **Separation of points by the dual over `ℚ`**: a vector on which every `ℚ`-linear functional
vanishes is zero.  The functional is produced by extending the coordinate functional of
`ℚ ∙ z` (which sends `z` to `1`, `LinearEquiv.coord`) along `Subspace.dualLift`. -/
lemma eq_zero_of_forall_dual_eq_zero {V : Type*} [AddCommGroup V] [Module ℚ V] (z : V)
    (h : ∀ φ : V →ₗ[ℚ] ℚ, φ z = 0) : z = 0 := by
  by_contra hz
  let ψ : (ℚ ∙ z) →ₗ[ℚ] ℚ := LinearEquiv.coord ℚ V z hz
  have h1 : (Subspace.dualLift (ℚ ∙ z) ψ) z = 1 := by
    rw [Subspace.dualLift_of_mem (Submodule.mem_span_singleton_self z)]
    exact LinearEquiv.coord_self ℚ V z hz
  have h0 := h (Subspace.dualLift (ℚ ∙ z) ψ)
  rw [h1] at h0
  exact one_ne_zero h0

/-- **Naturality of the relative Kronecker pairing over `ℚ`**, in the `relCohMap` form: the pairing
of the pullback of a class of `(Y,B)` with a class of `(X,A)` is the pairing of the class with the
image class.  This is `Work.Serre.B1Rel.relKronMapR_natural` restated through the abbreviation
`Work.Thom.relCohMap`. -/
lemma relKronMapR_natural_relCohMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (β : (Work.Cohomology.relComplex ℚ (TopCat.of Y) B).homology n)
    (c : (Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n) :
    (relKronMapR ℚ (TopCat.of X) A n).hom ((Work.Thom.relCohMap f A B hf ℚ n).hom β) c
      = (relKronMapR ℚ (TopCat.of Y) B n).hom β
          ((HomologicalComplex.homologyMap (relChainsRPairMap A B f hf) n).hom c) :=
  B1Rel.relKronMapR_natural A B f hf n β c

/-- **Surjectivity of a map of pairs on relative rational cohomology forces injectivity of the induced map on relative rational homology** (the dual-directed companion of the proved `Work.Serre.relCohMap_injective_of_surjective_relHomology`).

PROOF PLAN.  Over ℚ the relative Kronecker pairing is a perfect duality: `Work.Serre.relKronMapR ℚ X A n : H^n(X,A;ℚ) →ₗ Hom(H_n(X,A;ℚ),ℚ)` is injective (`Work.Serre.relKronMapRInjective`) and surjective (`Work.Serre.relKronMapRSurjective`), and it is natural in the pair: `Work.Serre.B1Rel.relKronMapR_natural (A) (B) f hf n β c` states `⟨f^*β, c⟩ = ⟨β, f_* c⟩` for all `β : H^n(Y,B;ℚ)` and `c : H_n(X,A;ℚ)` (here `f^*` is the cohomology map of the pair map `(X,A) → (Y,B)`, which is `Work.Thom.relCohMap f A B hf ℚ n`, and `f_*` is the homology map of `Work.Serre.relChainsRPairMap A B f hf`).

Let `z : H_n(X,A;ℚ)` with `f_* z = 0`.  Take any `φ : H_n(X,A;ℚ) →ₗ[ℚ] ℚ`.  By surjectivity of the Kronecker map pick `α : H^n(X,A;ℚ)` with `⟨α, -⟩ = φ`; by hypothesis `α = f^*β` for some `β : H^n(Y,B;ℚ)`.  Then `φ(z) = ⟨α, z⟩ = ⟨f^*β, z⟩ = ⟨β, f_* z⟩ = 0`.  Hence `φ(z) = 0` for *every* `φ`, so `z = 0` by separation of points (given `z ≠ 0`, some functional is non-zero on it; use `Subspace.dualLift` as in `relKronEquiv.lean`). -/
theorem homologyInjectiveOfRelCohSurjective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (h : Function.Surjective (Work.Thom.relCohMap f A B hf ℚ n).hom) :
    Function.Injective
      (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B f hf) n).hom := by
  intro z w hzw
  -- it suffices to see that the difference dies in homology and pairs trivially with everything
  have hsub : (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B f hf) n).hom
      (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  have hsep : ∀ φ : ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n) →ₗ[ℚ] ℚ,
      φ (z - w) = 0 := by
    intro φ
    -- realise the functional by a cohomology class, and that class by a pullback
    obtain ⟨α, hα⟩ := Work.Serre.relKronMapRSurjective (TopCat.of X) A n φ
    obtain ⟨β, hβ⟩ := h α
    calc φ (z - w)
        = (Work.Serre.relKronMapR ℚ (TopCat.of X) A n).hom α (z - w) := by rw [hα]
      _ = (Work.Serre.relKronMapR ℚ (TopCat.of X) A n).hom
            ((Work.Thom.relCohMap f A B hf ℚ n).hom β) (z - w) := by rw [hβ]
      _ = (Work.Serre.relKronMapR ℚ (TopCat.of Y) B n).hom β
            ((HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B f hf) n).hom
              (z - w)) := relKronMapR_natural_relCohMap A B f hf n β (z - w)
      _ = 0 := by rw [hsub, map_zero]
  have hz : z - w = 0 := by
    by_contra hne
    let ψ : (ℚ ∙ (z - w)) →ₗ[ℚ] ℚ := LinearEquiv.coord ℚ _ (z - w) hne
    have h1 : (Subspace.dualLift (ℚ ∙ (z - w)) ψ) (z - w) = 1 := by
      rw [Subspace.dualLift_of_mem (Submodule.mem_span_singleton_self (z - w))]
      exact LinearEquiv.coord_self ℚ _ (z - w) hne
    have h0 := hsep (Subspace.dualLift (ℚ ∙ (z - w)) ψ)
    rw [h1] at h0
    exact one_ne_zero h0
  exact sub_eq_zero.mp hz

end Work.Serre
