import Mathlib
import Submission.Work.Thom.tsqHonest
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

noncomputable section

/-- The restriction of a cochain on `X` to the small simplices of the cover, as a cochain on the
small simplicial set. -/
noncomputable abbrev restrSmall (X : TopCat) (U V : Set X) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) : Cochain ℤ (smallSSet U V) n :=
  (((SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ)).f n).hom.dualMap t)

/-- **The cup product with a relative cochain kills the small chains lying in `A`.**  This is the
descent step for the top term of the Mayer–Vietoris comparison. -/
theorem cupHom_smallInToSmall_eq_zero (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (z : (smallChains U V).X p →ₗ[ℤ] ℤ) :
    (smallInToSmall U V A).f (p + n) ≫ cupHom ℤ (smallSSet U V) z (restrSmall X U V n t) = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [comp_zero, ← Category.assoc]
  rw [show (smallInToSmall U V A) = SSet.chainComplexMap
    (Subfunctor.homOfLe (smallInSubcomplex_le U V A)) (ModuleCat.of ℤ ℤ) from rfl]
  rw [SSet.ι_chainComplexMap_f]
  rw [ιChainComplex_cupHom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, one_smul]
  have key : (ConcreteCategory.hom ((smallSubcomplex U V).ι.app (Opposite.op ⦋p+n⦌)))
        ((ConcreteCategory.hom ((Subfunctor.homOfLe (smallInSubcomplex_le U V A)).app
          (Opposite.op ⦋p+n⦌))) σ)
      = (ConcreteCategory.hom ((smallInSubcomplex U V A).ι.app (Opposite.op ⦋p+n⦌))) σ := rfl
  have hb : genEval ℤ (smallSSet U V)
      (restrSmall X U V n t)
      (backFace (smallSSet U V) p n
        ((ConcreteCategory.hom ((Subfunctor.homOfLe (smallInSubcomplex_le U V A)).app
          (Opposite.op ⦋p+n⦌))) σ)) = 0 := by
    rw [restrSmall, genEval_dualMap, app_backFace, key]
    rw [← app_backFace (smallInSubcomplex U V A).ι p n σ]
    exact genEval_eq_zero_of_isSmallIn U V A t ht _ (backFace (smallInSSet U V A) p n σ).2
  rw [hb, mul_zero]


/-- The descent of the cup product with a relative representative to the relative small chains
`C^{U,V}(X,A)`: a functional on the small chains of degree `p` is cupped with `t` and, the result
killing the `A`-chains, descends to the cokernel. -/
noncomputable def cupDescend (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (dualComplex ℤ (smallChains U V)).X p ⟶ (dualComplex ℤ (relMVTopC X A U V)).X (p + n) :=
  ModuleCat.ofHom
    { toFun := fun ψ => ModuleCat.Hom.hom
        ((cokernelComponentIso (smallInToSmall U V A) (p + n)).hom ≫
          cokernel.desc ((smallInToSmall U V A).f (p + n))
            (cupHom ℤ (smallSSet U V) ψ (restrSmall X U V n t))
            (cupHom_smallInToSmall_eq_zero X A U V n p t ht ψ))
      map_add' := fun ψ ψ' => by
        rw [← ModuleCat.hom_add]
        congr 1
        rw [← Preadditive.comp_add]
        refine (cancel_epi (cokernelComponentIso (smallInToSmall U V A) (p + n)).hom).mpr ?_
        refine (cancel_epi (cokernel.π ((smallInToSmall U V A).f (p + n)))).mp ?_
        rw [Preadditive.comp_add]
        simp only [cokernel.π_desc]
        apply ModuleCat.hom_ext
        rw [ModuleCat.hom_add]
        exact (cupBilinear ℤ (smallSSet U V) p n).1 ψ ψ' (restrSmall X U V n t)
      map_smul' := fun a ψ => by
        rw [← ModuleCat.hom_smul]
        congr 1
        rw [← Preadditive.comp_zsmul]
        refine (cancel_epi (cokernelComponentIso (smallInToSmall U V A) (p + n)).hom).mpr ?_
        refine (cancel_epi (cokernel.π ((smallInToSmall U V A).f (p + n)))).mp ?_
        rw [Preadditive.comp_zsmul]
        simp only [cokernel.π_desc]
        apply ModuleCat.hom_ext
        rw [ModuleCat.hom_smul]
        exact (cupBilinear ℤ (smallSSet U V) p n).2.1 a ψ (restrSmall X U V n t) }

end

end Work.Thom
