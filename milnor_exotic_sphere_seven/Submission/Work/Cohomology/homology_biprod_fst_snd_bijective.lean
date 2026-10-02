import Mathlib
import Submission.Work.Cohomology.Singular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

open CategoryTheory Limits

set_option linter.style.haveILetI false

/-- The `k`-th homology functor is additive, hence preserves binary biproducts; consequently the
pair of maps induced by the biproduct projections `C ⊞ D ⟶ C` and `C ⊞ D ⟶ D` is a bijection
`H_k(C ⊞ D) ≃ H_k(C) × H_k(D)`. -/
theorem homology_biprod_fst_snd_bijective (C D : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)) (k : ℕ) :
    Function.Bijective (LinearMap.prod
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.biprod.fst : C ⊞ D ⟶ C) k))
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.biprod.snd : C ⊞ D ⟶ D) k))) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  show Function.Bijective (LinearMap.prod
    (ModuleCat.Hom.hom (F.map (biprod.fst : C ⊞ D ⟶ C)))
    (ModuleCat.Hom.hom (F.map (biprod.snd : C ⊞ D ⟶ D))))
  set e := F.mapBiprod C D with he
  set p := ModuleCat.biprodIsoProd (F.obj C) (F.obj D) with hp
  have hfac : e.hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
    Functor.mapBiprod_hom F C D
  have hbij : Function.Bijective ⇑(e.hom ≫ p.hom).hom :=
    ConcreteCategory.bijective_of_isIso (e.hom ≫ p.hom)
  have hfun : ⇑(LinearMap.prod (ModuleCat.Hom.hom (F.map (biprod.fst : C ⊞ D ⟶ C)))
      (ModuleCat.Hom.hom (F.map (biprod.snd : C ⊞ D ⟶ D))))
      = ⇑(e.hom ≫ p.hom).hom := by
    funext x
    rw [LinearMap.prod_apply, Function.prod, ModuleCat.comp_apply]
    refine Prod.ext ?_ ?_
    · have h1 : ((p.hom (e.hom x)).1) =
          (ConcreteCategory.hom (biprod.fst : F.obj C ⊞ F.obj D ⟶ F.obj C)) (e.hom x) := by
        have h := ModuleCat.biprodIsoProd_inv_comp_fst_apply (F.obj C) (F.obj D) (p.hom (e.hom x))
        rw [ModuleCat.inv_hom_apply] at h
        exact h.symm
      rw [h1, ← ModuleCat.comp_apply, hfac, biprod.lift_fst]
    · have h1 : ((p.hom (e.hom x)).2) =
          (ConcreteCategory.hom (biprod.snd : F.obj C ⊞ F.obj D ⟶ F.obj D)) (e.hom x) := by
        have h := ModuleCat.biprodIsoProd_inv_comp_snd_apply (F.obj C) (F.obj D) (p.hom (e.hom x))
        rw [ModuleCat.inv_hom_apply] at h
        exact h.symm
      rw [h1, ← ModuleCat.comp_apply, hfac, biprod.lift_snd]
  rw [hfun]
  exact hbij

end Work.Cohomology
