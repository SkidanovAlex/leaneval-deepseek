import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Infinite
import Submission.Work.AbsoluteGalois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

-- `Field.absoluteGaloisGroup` is a semireducible `def`, so many of the group/field instances in
-- play below are only *definitionally* equal along this unfolding.  Enabling full definitional
-- unfolding during elaboration makes the transport along `Field.absoluteGaloisGroup ℚ = Gal(ℚ̄/ℚ)`
-- transparent to `isDefEq`, which is what lets the Galois-correspondence API (stated for
-- `Gal(K/k)`) be applied directly to `ψ.ker` (stated for `Field.absoluteGaloisGroup ℚ`).
set_option backward.isDefEq.respectTransparency false

/-- **The absolute Galois group of `ℚ` acting on the fixed field of an open kernel.**

Let `ψ : G_ℚ →* G` be a surjective homomorphism with open kernel `N = ker ψ`, and let
`F = ℚ̄^N` be the fixed field of `N`.  Then `F/ℚ` is Galois and `G ≃* Gal(F/ℚ)`, via the unique
isomorphism sending `ψ σ` to the automorphism of `F` induced by `σ`. -/
theorem fixedField_ker_autEquiv (G : Type*) [Group G]
    (ψ : Field.absoluteGaloisGroup ℚ →* G)
    (hopen : IsOpen (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)))
    (hsurj : Function.Surjective ψ) :
    ∃ e : G ≃* (↥(IntermediateField.fixedField ψ.ker) ≃ₐ[ℚ] ↥(IntermediateField.fixedField ψ.ker)),
      ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : ↥(IntermediateField.fixedField ψ.ker)),
        (e (ψ σ) x : AlgebraicClosure ℚ) = σ (x : AlgebraicClosure ℚ) := by
  -- `ℚ̄` is Galois over `ℚ` (the instance re-registered in `Basic`).
  have : IsGalois ℚ (AlgebraicClosure ℚ) := inferInstance
  -- The kernel of `ψ` is open, hence closed: the quotient by an open subgroup of a topological
  -- group is discrete, and the kernel is the preimage of a point under the (continuous) quotient
  -- map.
  have hclosed : IsClosed (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)) := by
    have : DiscreteTopology (Field.absoluteGaloisGroup ℚ ⧸ ψ.ker) :=
      QuotientGroup.discreteTopology hopen
    rw [← QuotientGroup.preimage_mk_one (N := ψ.ker)]
    exact (isClosed_discrete {1}).preimage QuotientGroup.continuous_mk
  -- Package it as a closed subgroup, so that the infinite Galois correspondence applies.
  let H : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ⟨ψ.ker, hclosed⟩
  have hHnormal : (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).Normal :=
    MonoidHom.normal_ker ψ
  have : IsGalois ℚ
      ↥(IntermediateField.fixedField
        (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :=
    IsGalois.of_fixedField_normal_subgroup
      (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  have : Normal ℚ
      ↥(IntermediateField.fixedField
        (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :=
    IsGalois.to_normal
  -- `ψ` descends to an isomorphism `G_ℚ ⧸ ker ψ ≃* G`.
  let A : Field.absoluteGaloisGroup ℚ ⧸ ψ.ker ≃* G := QuotientGroup.liftEquiv ψ.ker hsurj rfl
  -- The fundamental theorem of infinite Galois theory: `G_ℚ ⧸ ker ψ ≃* Gal(F/ℚ)`.
  let B := InfiniteGalois.normalAutEquivQuotient H
  refine ⟨A.symm.trans B, ?_⟩
  intro σ x
  -- `A.symm (ψ σ)` is the class of `σ`.
  have h1 : A.symm (ψ σ) = (σ : Gal(AlgebraicClosure ℚ/ℚ) ⧸ (H : Subgroup _)) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  -- On the class of `σ`, `B` is the restriction map.
  have h2 : (A.symm.trans B) (ψ σ)
      = AlgEquiv.restrictNormalHom
          ↥(IntermediateField.fixedField
            (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) σ := by
    rw [MulEquiv.trans_apply, h1]
    exact InfiniteGalois.normalAutEquivQuotient_apply H σ
  rw [h2]
  exact AlgEquiv.restrictNormalHom_apply _ σ x

end

end Work.AbsoluteGalois
