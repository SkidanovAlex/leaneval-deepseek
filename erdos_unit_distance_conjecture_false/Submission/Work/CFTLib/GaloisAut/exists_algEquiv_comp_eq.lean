import Mathlib

namespace Work.CFTLib.GaloisAut

theorem exists_algEquiv_comp_eq {F A M : Type} [Field F] [Field A] [Field M] [Algebra F A]
    [Algebra F M] [FiniteDimensional F M] [Normal F A] (f g : M →ₐ[F] A) :
    ∃ σ : A ≃ₐ[F] A, (σ : A →ₐ[F] A).comp f = g := by
  classical
  -- `f` and `g` induce isomorphisms `M ≃ₐ[F] f.fieldRange` and `M ≃ₐ[F] g.fieldRange`,
  -- hence an isomorphism of the two intermediate fields `f.fieldRange ≃ₐ[F] g.fieldRange`.
  let χ : f.fieldRange ≃ₐ[F] g.fieldRange :=
    (AlgHom.equivFieldRange f).symm.trans (AlgHom.equivFieldRange g)
  -- Since `A/F` is normal, `χ` extends to an automorphism of `A`.
  refine ⟨χ.liftNormal A, ?_⟩
  ext m
  change χ.liftNormal A (f m) = g m
  have h := χ.liftNormal_commutes A (AlgHom.equivFieldRange f m)
  simpa [χ, AlgHom.equivFieldRange_apply_coe] using h

end Work.CFTLib.GaloisAut
