import Mathlib
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Kunneth.pullbackH_cohomologyClassOf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

namespace Work.Serre

lemma homologyMap_cohomologyClassOf (R : Type) [CommRing R] (X Y : SSet) (n : ℕ)
    (φ : Work.Cohomology.SSetCochainComplex R Y ⟶ Work.Cohomology.SSetCochainComplex R X)
    (β : Work.Cohomology.Cochain R Y n) (β' : Work.Cohomology.Cochain R X n)
    (hβ : Work.Cohomology.cochainDiff R Y β = 0)
    (hβ' : Work.Cohomology.cochainDiff R X β' = 0)
    (hφ : (φ.f n).hom β = β') :
    (HomologicalComplex.homologyMap φ n).hom
        (Work.Cohomology.cohomologyClassOf R Y β hβ)
      = Work.Cohomology.cohomologyClassOf R X β' hβ' := by
  have h1 : (Work.Cohomology.SSetCochainComplex R Y).homologyπ n
        ≫ HomologicalComplex.homologyMap φ n
      = HomologicalComplex.cyclesMap φ n
        ≫ (Work.Cohomology.SSetCochainComplex R X).homologyπ n :=
    HomologicalComplex.homologyπ_naturality φ n
  have h2 := congrArg (fun (g : (Work.Cohomology.SSetCochainComplex R Y).cycles n ⟶
      (Work.Cohomology.SSetCochainComplex R X).homology n) =>
      ModuleCat.Hom.hom g (Work.Cohomology.cocycleOf R Y β hβ)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have hkey : ModuleCat.Hom.hom (HomologicalComplex.cyclesMap φ n)
        (Work.Cohomology.cocycleOf R Y β hβ)
      = Work.Cohomology.cocycleOf R X β' hβ' := by
    refine Work.Cohomology.iCycles_injective R X n ?_
    have hii := congrArg (fun (g : (Work.Cohomology.SSetCochainComplex R Y).cycles n ⟶
        (Work.Cohomology.SSetCochainComplex R X).X n) =>
        ModuleCat.Hom.hom g (Work.Cohomology.cocycleOf R Y β hβ))
      (HomologicalComplex.cyclesMap_i φ n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hii
    rw [hii, Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.iCycles_cocycleOf]
    exact hφ
  exact h2.trans (congrArg (fun w => ModuleCat.Hom.hom
    ((Work.Cohomology.SSetCochainComplex R X).homologyπ n) w) hkey)

end Work.Serre
