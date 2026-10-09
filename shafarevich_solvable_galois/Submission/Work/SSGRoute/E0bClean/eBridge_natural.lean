import Mathlib
import Submission.Work.SSGRoute.extH_groupCohomology_addEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open SSGRoute.PTExt
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace Work.SSGRoute.E0bClean

noncomputable section

theorem eBridge_natural {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff G} {B : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff H}
    (φ : Rep.res f A ⟶ B) (n : ℕ) (y : groupCohomology A n) :
    Work.SSGRoute.E0bGroupCoeff.eBridge n H B ((groupCohomology.map f φ n).hom y) =
      SSGRoute.PTExt.extHMap f φ (Work.SSGRoute.E0bGroupCoeff.eBridge n G A y) := by
  rw [Work.SSGRoute.E0bGroupCoeff.eBridge_apply, Work.SSGRoute.E0bGroupCoeff.eBridge_apply]
  have h1 : HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n
        ((groupCohomology.map f φ n).hom y)
      = HomologicalComplex.homologyMap (Work.SSGRoute.E0bGroupCoeff.lyBar f φ) n
          (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n y) := by
    have hcomp : HomologicalComplex.homologyMap (groupCohomology.cochainsMap f φ) n ≫
          HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n
        = HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
          HomologicalComplex.homologyMap (Work.SSGRoute.E0bGroupCoeff.lyBar f φ) n := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        Work.SSGRoute.cochainsMap_inhomogeneousCochainsIso_comm Coeff G H f A B φ _
          (fun m g => Work.SSGRoute.E0bGroupCoeff.lyBar_f_apply f φ m g)]
    show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso B).hom n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n) y)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.SSGRoute.E0bGroupCoeff.lyBar f φ) n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n) y)
    calc (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso B).hom n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n) y)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n ≫
            HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n)) y := by
            rw [ModuleCat.hom_comp]; rfl
      _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
            HomologicalComplex.homologyMap (Work.SSGRoute.E0bGroupCoeff.lyBar f φ) n)) y := by
            rw [hcomp]
            rfl
      _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.SSGRoute.E0bGroupCoeff.lyBar f φ) n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n) y) := by
            rw [ModuleCat.hom_comp]; rfl
  rw [h1]
  exact Work.SSGRoute.E0bGroupCoeff.Psi_natural_unit f φ n _

end

end Work.SSGRoute.E0bClean
