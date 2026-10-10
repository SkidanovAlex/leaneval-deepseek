import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Submission.Work.GenericKernelReduction.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

/-- A solution inside the algebraic closure transports along an isomorphism of `G`-operator
groups: if `e : A ≃* B` intertwines the `G`-actions `Φ` on `A` and `Ψ` on `B`, then a solution
for the kernel `A` gives a solution for the kernel `B`. -/
theorem splitEmbeddingSolvedInClosure_of_mulEquiv {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {A : Type} [Group A] [Finite A] {B : Type} [Group B] [Finite B]
    {Φ : (L ≃ₐ[ℚ] L) →* MulAut A} {Ψ : (L ≃ₐ[ℚ] L) →* MulAut B}
    (e : A ≃* B) (he : ∀ (g : (L ≃ₐ[ℚ] L)) (a : A), e (Φ g a) = Ψ g (e a))
    (h : SplitEmbeddingSolvedInClosure L A Φ) :
    SplitEmbeddingSolvedInClosure L B Ψ := by
  obtain ⟨M, hLM, hfd, hgal, hAlg, hST, hfdL, hgalL, e', he'⟩ := h
  have hcongr : ∀ g : (L ≃ₐ[ℚ] L),
      (Φ g).trans e = e.trans (Ψ (MulEquiv.refl (L ≃ₐ[ℚ] L) g)) := by
    intro g
    refine MulEquiv.ext fun a => ?_
    simpa using he g a
  refine ⟨M, hLM, hfd, hgal, hAlg, hST, hfdL, hgalL,
    (SemidirectProduct.congr e (MulEquiv.refl (L ≃ₐ[ℚ] L)) hcongr).symm.trans e', ?_⟩
  intro g x
  rw [MulEquiv.trans_apply, he']
  have hright : SemidirectProduct.rightHom
      ((SemidirectProduct.congr e (MulEquiv.refl (L ≃ₐ[ℚ] L)) hcongr).symm g)
      = SemidirectProduct.rightHom g := by
    simp [SemidirectProduct.rightHom_eq_right]
  rw [hright]

end Work.GenericKernelReduction
