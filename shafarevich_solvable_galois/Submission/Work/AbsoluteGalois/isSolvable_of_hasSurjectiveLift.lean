/-
Copyright (c) 2025. All rights reserved.

# A surjective lift of an embedding problem solves it

An embedding problem `E` over `ℚ` consists of a finite Galois extension `E.L/ℚ`, a finite group
`E.G` and a surjection `E.π : E.G ↠ Gal(E.L/ℚ)`.  It is *solvable* if there is a finite Galois
extension `L'/ℚ` containing `E.L` with `L'/E.L` Galois and an isomorphism
`E.G ≃* Gal(L'/ℚ)` compatible with `E.π` (`Submission.EmbeddingProblem.IsSolvable`).

The present file proves the *easy direction* of the classical equivalence between solvability of an
embedding problem and the existence of a continuous (open-kernel) surjection `G_ℚ ↠ E.G`
compatible with the projection:

`Work.AbsoluteGalois.HasSurjectiveLift E → E.IsSolvable`.

Concretely, given such a lift `ψ : G_ℚ ↠ E.G` (with open kernel, so that its fixed field is a
finite Galois extension of `ℚ`), the solution is the fixed field `L' = fixedField ψ.ker` of the
kernel of `ψ`.  Its Galois group is `G_ℚ ⧸ ψ.ker ≅ E.G` (infinite Galois theory), and the
compatibility with `E.π` is exactly the condition that `ψ` intertwines the projection with the
restriction map `G_ℚ → Gal(E.L/ℚ)`.  The containment `E.L ⊆ L'` then follows from the compatibility,
and the `E.L`-algebra structure on `L'` is induced by the identification `E.L ≃ₐ[ℚ] M.L` of the
base field with its image in `ℚ̄`.

## Main declaration

* `Work.AbsoluteGalois.isSolvable_of_hasSurjectiveLift`.
-/
import Mathlib
import Submission.Work.AbsoluteGalois.ClosureModel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

/-- **A surjective lift solves the embedding problem.**

If `E` has a surjective lift `ψ : G_ℚ ↠ E.G` with open kernel, compatible with the projection
`E.π` (i.e. `M.autCongr (E.π (ψ σ)) = σ|_{M.L}` for the closure model `M`), then `E` is solvable:
the fixed field of `ker ψ` is a finite Galois extension of `ℚ` containing (the image of) `E.L`,
with Galois group canonically isomorphic to `E.G` compatibly with `E.π`.

This is the easy direction of `E.IsSolvable ↔ HasSurjectiveLift E`. -/
theorem isSolvable_of_hasSurjectiveLift (E : Submission.EmbeddingProblem ℚ)
    (h : Work.AbsoluteGalois.HasSurjectiveLift E) : E.IsSolvable := by
  obtain ⟨M, ψ, hopen, hsurj, hcomp⟩ := h
  -- Work with `G_ℚ = Gal(ℚ̄/ℚ)` presented as `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`, so
  -- that subtleties of the numerous (non-definitionally-equal) `Subgroup` instance paths do not
  -- arise; `ψA` is definitionally `ψ`, only its type is elaborated in the "Galois-form" world.
  let ψA : Gal(AlgebraicClosure ℚ/ℚ) →* E.G := ψ
  have hsurjA : Function.Surjective ψA := hsurj
  have hopenA : IsOpen (ψA.ker : Set Gal(AlgebraicClosure ℚ/ℚ)) := hopen
  have hcompA : ∀ σ : Gal(AlgebraicClosure ℚ/ℚ),
      M.autCongr (E.π (ψA σ)) = Work.AbsoluteGalois.restrictHom M.L σ := hcomp
  -- The candidate solution: the fixed field of `ker ψ`.
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField ψA.ker
  have hclosedA : IsClosed (ψA.ker : Set Gal(AlgebraicClosure ℚ/ℚ)) :=
    Subgroup.isClosed_of_isOpen ψA.ker hopenA
  have hfix : L'.fixingSubgroup = ψA.ker :=
    @InfiniteGalois.fixingSubgroup_fixedField ℚ (AlgebraicClosure ℚ) _ _ _
      (⟨ψA.ker, hclosedA⟩ : ClosedSubgroup Gal(AlgebraicClosure ℚ/ℚ))
      (inferInstance : IsGalois ℚ (AlgebraicClosure ℚ))
  have hfd : FiniteDimensional ℚ L' :=
    (@InfiniteGalois.isOpen_iff_finite ℚ (AlgebraicClosure ℚ) _ _ _ L'
      (inferInstance : IsGalois ℚ (AlgebraicClosure ℚ))).mp (by rw [hfix]; exact hopenA)
  have hgal : IsGalois ℚ L' := by
    have hn : Subgroup.Normal ψA.ker := MonoidHom.normal_ker ψA
    exact @IsGalois.of_fixedField_normal_subgroup ℚ (AlgebraicClosure ℚ) _ _ _ _ ψA.ker hn
  -- The isomorphism `E.G ≃* Gal(L'/ℚ)`, obtained from `G_ℚ ⧸ ker ψ ≅ E.G` and the fundamental
  -- theorem of infinite Galois theory `G_ℚ ⧸ ker ψ ≅ Gal(L'/ℚ)`.
  have hnH : (⟨ψA.ker, hclosedA⟩ : ClosedSubgroup Gal(AlgebraicClosure ℚ/ℚ)).Normal :=
    MonoidHom.normal_ker ψA
  let na := @InfiniteGalois.normalAutEquivQuotient ℚ (AlgebraicClosure ℚ) _ _ _
      (inferInstance : IsGalois ℚ (AlgebraicClosure ℚ)) ⟨ψA.ker, hclosedA⟩ hnH
  let e : E.G ≃* (L' ≃ₐ[ℚ] L') :=
    (QuotientGroup.quotientKerEquivOfSurjective ψA hsurjA).symm.trans na
  -- The key compatibility of `e` with the action: `e (ψ τ)` acts on `L'` as `τ` does.
  have key : ∀ (τ : Gal(AlgebraicClosure ℚ/ℚ)) (y : L'),
      ((e (ψA τ)) y : AlgebraicClosure ℚ) = τ (y : AlgebraicClosure ℚ) := by
    intro τ y
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψA hsurjA)
        (QuotientGroup.mk τ) = ψA τ := by
      rw [show (QuotientGroup.quotientKerEquivOfSurjective ψA hsurjA) (QuotientGroup.mk τ)
          = (QuotientGroup.kerLift ψA) (QuotientGroup.mk τ) from rfl]
      rw [QuotientGroup.kerLift_mk]
    have h2 : e (ψA τ) = na (QuotientGroup.mk τ) := by
      change ((QuotientGroup.quotientKerEquivOfSurjective ψA hsurjA).symm.trans na) (ψA τ)
        = na (QuotientGroup.mk τ)
      rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    change ((na (QuotientGroup.mk τ)) y : AlgebraicClosure ℚ) = τ (y : AlgebraicClosure ℚ)
    rw [InfiniteGalois.normalAutEquivQuotient_apply]
    exact @AlgEquiv.restrictNormalHom_apply ℚ _ (AlgebraicClosure ℚ) _ _ L' hgal.to_normal τ y
  -- The base field `E.L` sits inside `L'`: an element of `ker ψ` fixes `M.L` pointwise, because
  -- `E.π` of it is trivial and `ψ` intertwines `E.π` with restriction.
  have hle : M.L ≤ L' := by
    intro x hx
    change x ∈ IntermediateField.fixedField ψA.ker
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 : ψA σ = 1 := hσ
    have h2 : M.autCongr (E.π (ψA σ)) = 1 := by rw [h1, map_one, map_one]
    have h3 : Work.AbsoluteGalois.restrictHom M.L σ = 1 := by rw [← hcompA σ, h2]
    have h4 : (Work.AbsoluteGalois.restrictHom M.L σ) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [h3]; rfl
    have h5 := congrArg Subtype.val h4
    rw [Work.AbsoluteGalois.restrictHom_apply M.L σ ⟨x, hx⟩] at h5
    exact h5
  -- Transport the `E.L`-algebra structure on `L'` along the identification `E.L ≃ₐ[ℚ] M.L`.
  let f : E.L →ₐ[ℚ] L' := (IntermediateField.inclusion hle).comp M.e.toAlgHom
  letI : Algebra E.L L' := f.toRingHom.toAlgebra
  haveI hST : IsScalarTower ℚ E.L L' := inferInstance
  haveI hfdel : FiniteDimensional E.L L' := FiniteDimensional.right ℚ E.L L'
  haveI hgalel : IsGalois E.L L' := IsGalois.tower_top_of_isGalois ℚ E.L L'
  refine ⟨L', inferInstance, inferInstance, hfd, hgal, f.toRingHom.toAlgebra,
    hST, hfdel, hgalel, e, ?_⟩
  intro g x
  obtain ⟨σ, rfl⟩ := hsurjA g
  apply Subtype.ext
  change ((e (ψA σ)) (f x) : AlgebraicClosure ℚ) = (f (E.π (ψA σ) x) : AlgebraicClosure ℚ)
  rw [key σ (f x)]
  have hfx : ((f x : L') : AlgebraicClosure ℚ) = (M.e x : AlgebraicClosure ℚ) := rfl
  have hfy : ((f (E.π (ψA σ) x) : L') : AlgebraicClosure ℚ)
      = (M.e (E.π (ψA σ) x) : AlgebraicClosure ℚ) := rfl
  rw [hfx, hfy]
  -- evaluate the intertwining property of `ψ` at the element `M.e x`
  have hcell := congrArg (fun (u : M.L ≃ₐ[ℚ] M.L) => ((u (M.e x)) : AlgebraicClosure ℚ))
    (hcompA σ)
  simp only [Submission.EmbeddingProblem.ClosureModel.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply] at hcell
  rw [Work.AbsoluteGalois.restrictHom_apply M.L σ (M.e x)] at hcell
  exact hcell.symm

end

end Work.AbsoluteGalois
