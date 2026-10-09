/-
Copyright (c) 2025. All rights reserved.

# The base field of a closure model is independent of the model

A `ClosureModel` of an embedding problem `E` over `ℚ` identifies the abstract base field `E.L`
with an intermediate field `M.L ⊆ ℚ̄ = AlgebraicClosure ℚ`.  A priori the choice of such an
identification is not canonical: one picks a `ℚ`-embedding `E.L → ℚ̄` and takes its range.

We show that the resulting subfield of `ℚ̄` does *not* depend on the choice.  The point is that
`E.L/ℚ` is **Galois**, and a Galois subextension of `ℚ̄` is not merely `ℚ`-isomorphic but literally
*equal* to all of its conjugates: if `K ⊆ ℚ̄` is normal over `ℚ` and `φ : ℚ̄ →ₐ[ℚ] ℚ̄` is any
`ℚ`-embedding, then `φ(K) ≤ K`, because for `x ∈ K` the element `φ x` is a root of `minpoly ℚ x`,
and that polynomial splits in the normal extension `K`.

Concretely, given two closure models `M`, `M'` of `E`, the `ℚ`-isomorphism
`τ : M.L ≃ₐ[ℚ] M'.L` obtained from the two identifications is realized by a `ℚ`-embedding
`φ : ℚ̄ →ₐ[ℚ] ℚ̄` extending its composite with the inclusion `M'.L ↪ ℚ̄`
(`IntermediateField.exists_algHom_of_splits`).  Then `M'.L = φ(M.L) ≤ M.L` by normality of
`M.L`, and the reverse inclusion follows from the equality of the degrees over `ℚ`.

## Main declaration

* `Work.AbsoluteGalois.closureModel_L_eq`
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

-- The intermediate fields of `AlgebraicClosure ℚ` carry several non-definitionally-equal instance
-- paths (see the header of `Submission/Work/AbsoluteGalois/Basic.lean`); full definitional
-- unfolding makes these transparent to `isDefEq`.
set_option backward.isDefEq.respectTransparency false

-- `haveI` is the natural way to introduce the transported instances of a closure model when the
-- goal is a proposition (`M.L = M'.L`); silence the style linter's suggestion to use `have`.
set_option linter.style.haveILetI false

/-- **The base field of a closure model is independent of the model.**

Every `ClosureModel` of an embedding problem `E` over `ℚ` presents the base field `E.L` as one and
the same subfield of `ℚ̄`: two models have the same underlying intermediate field.  This uses that
`E.L/ℚ` is Galois, so that a Galois subextension of `ℚ̄` equals each of its conjugates. -/
theorem closureModel_L_eq (E : Submission.EmbeddingProblem ℚ) (M M' : E.ClosureModel) :
    M.L = M'.L := by
  haveI hMfd : FiniteDimensional ℚ ↥M.L := M.finiteDimensional
  haveI hMgal : IsGalois ℚ ↥M.L := M.isGalois
  -- `E.L` is Galois, hence so is `M.L`: in particular `M.L` is normal over `ℚ`.
  haveI hMnorm : Normal ℚ ↥M.L := hMgal.to_normal
  haveI hM'fd : FiniteDimensional ℚ ↥M'.L := M'.finiteDimensional
  haveI hM'gal : IsGalois ℚ ↥M'.L := M'.isGalois
  -- The `ℚ`-isomorphism between the two presentations of the base field.
  let τ : ↥M.L ≃ₐ[ℚ] ↥M'.L := M.e.symm.trans M'.e
  -- It is an embedding `M.L → ℚ̄` whose range is `M'.L`.
  let f : ↥M.L →ₐ[ℚ] AlgebraicClosure ℚ := (M'.L).val.comp τ.toAlgHom
  -- Extend it to a `ℚ`-endomorphism of `ℚ̄` (possible since `ℚ̄` is algebraically closed and the
  -- minimal polynomial over `ℚ` of any element of `ℚ̄` splits there).
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := ℚ) (E := AlgebraicClosure ℚ)
    (K := AlgebraicClosure ℚ) (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    (L := M.L) f
  -- `φ` restricts to `f` on `M.L`.
  have hφx : ∀ x : ↥M.L, φ (x : AlgebraicClosure ℚ) = f x := by
    intro x
    have h := DFunLike.congr_fun hφ x
    simpa only [AlgHom.comp_apply, IntermediateField.coe_val] using h
  -- Normality of `M.L` over `ℚ`: `φ` maps `M.L` into itself.
  have hmem : ∀ x : ↥M.L, φ (x : AlgebraicClosure ℚ) ∈ M.L := by
    intro x
    rw [← IntermediateField.algebraMap_apply (S := M.L) x]
    rw [← AlgHom.restrictNormal_commutes (ϕ := φ) (E := ↥M.L) x]
    rw [IntermediateField.algebraMap_apply]
    exact SetLike.coe_mem _
  -- Since `φ|_{M.L}` has range `M'.L`, this exhibits `M'.L ≤ M.L`.
  have hle : M'.L ≤ M.L := by
    intro y hy
    have hy' : φ ((τ.symm ⟨y, hy⟩ : ↥M.L) : AlgebraicClosure ℚ) = y := by
      rw [hφx]
      simp [f]
    exact hy' ▸ hmem (τ.symm ⟨y, hy⟩)
  -- Both fields have the same finite degree over `ℚ`, so the inclusion is an equality.
  exact (IntermediateField.eq_of_le_of_finrank_eq (F := M'.L) (E := M.L) hle
    ((LinearEquiv.finrank_eq τ.toLinearEquiv).symm)).symm

end

end Work.AbsoluteGalois
