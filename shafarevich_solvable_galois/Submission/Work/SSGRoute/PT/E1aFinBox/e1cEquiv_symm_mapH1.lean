import Mathlib
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.ExtChain.e1c_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the inverse of the `E1cGeneric` equivalence

`e1cEquiv R : Ext¹_G(R, Kˣ) ≃+ H¹(Γ, Hom_ℤ(R, Ωˣ))` (`E1cGeneric/Canonical.lean`) is
`AddEquiv.ofBijective (e1cMap R)`.  Its source lemma `e1cMap_natural` says that `e1cMap` intertwines
`mk₀`-precomposition on the left with `mapH1 (precompAddHom g)` on the right.  This file records the
`.symm` form of that identity, which is the form the coefficient naturality chase of the
finite-place dictionary `E1aClean.phiCan` consumes.
-/

open CategoryTheory

namespace Work.SSGRoute.PT.E1aFinBox

/-- For `g : R ⟶ R₂` equivariant and `y ∈ H¹(Γ, homCoind K R₂)`,
`(e1cEquiv R).symm (mapH1 g y) = (mk₀ g).comp ((e1cEquiv R₂).symm y) (zero_add 1)`. -/
theorem e1cEquiv_symm_mapH1 {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (R R₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    [Module.Finite ℤ R₂.V] (g : R ⟶ R₂)
    (hg : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom))
    (y : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R₂)) :
    (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) R).symm
        (Work.AbsoluteKummer.mapH1 (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg y)
      = (CategoryTheory.Abelian.Ext.mk₀ g).comp
          ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y)
          (zero_add 1) := by
  rw [AddEquiv.symm_apply_eq]
  change Work.AbsoluteKummer.mapH1 (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg y
      = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) R
          ((CategoryTheory.Abelian.Ext.mk₀ g).comp
            ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y)
            (zero_add 1))
  rw [Work.SSGRoute.ExtChain.E1cGeneric.e1cMap_natural]
  have hy : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) R₂
      ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y) = y := by
    change (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) R₂)
      ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y) = y
    exact AddEquiv.apply_symm_apply _ _
  rw [hy]

end Work.SSGRoute.PT.E1aFinBox
