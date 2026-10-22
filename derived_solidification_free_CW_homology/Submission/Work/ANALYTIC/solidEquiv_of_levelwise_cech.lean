import Mathlib
import Submission.Work.ANALYTIC.CechGen.Basic
import Submission.Work.ANALYTIC.CechGen.cechGen_h0
import Submission.Work.ANALYTIC.CechGen.cechGen_higher
import Submission.Work.ANALYTIC.CechGen.extendSingleIso_naturality
import Submission.Work.TOOLKIT.Main

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **Levelwise comparison of Čech resolutions.**  Let `β : X ⟶ Y` and `β' : X' ⟶ Y'` be
epimorphisms of light condensed sets and let a square `u ≫ β = β' ≫ v` be given.  If the induced
map of Čech nerves is a solid-equivalence at every simplicial level (after applying `ℤ[-]`), then
the induced map `ℤ[Y'] ⟶ ℤ[Y]` on the targets is a solid-equivalence. -/
theorem solidEquiv_of_levelwise_cech {X X' Y Y' : LightCondSet.{0}}
    (β : X ⟶ Y) (hβ : Epi β) (β' : X' ⟶ Y') (hβ' : Epi β')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v)
    (hlev : ∀ (p : ℕ), Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((free ℤ).map ((Arrow.mapCechNerve
          (Arrow.homMk (f := Arrow.mk β') (g := Arrow.mk β) u v huv)).app
            (Opposite.op (SimplexCategory.mk p)))))) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map ((free ℤ).map v)) := by
  -- descent for the two Čech complexes: degree `0` (effaceability of the cover) and positive degrees
  have haugβ : Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map (CechGen.cechAug β)) :=
    CechGen.solidEquiv_cechAug_of β (CechGen.cechGen_h0 β hβ)
      (fun n => CechGen.cechGen_higher β n)
  have haugβ' : Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map (CechGen.cechAug β')) :=
    CechGen.solidEquiv_cechAug_of β' (CechGen.cechGen_h0 β' hβ')
      (fun n => CechGen.cechGen_higher β' n)
  -- the levelwise comparison of the two Čech complexes
  have hcmp : Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map (CechGen.cechCmp β β' u v huv)) :=
    CechGen.solidEquiv_cechCmp β β' u v huv hlev
  -- naturality of the augmentation: the comparison of the targets is induced by the comparison of
  -- the Čech complexes
  have hsq := CechGen.cechAug_naturality β β' u v huv
    (fun {A B : LightCondAb} (g : A ⟶ B) =>
      CechGen.extendSingleIso_naturality ComplexShape.embeddingDownNat 0 0
        CechGen.embeddingDownNat_zero g)
  have hsq' : DerivedCategory.Q.map (CechGen.cechCmp β β' u v huv) ≫
        DerivedCategory.Q.map (CechGen.cechAug β) =
      DerivedCategory.Q.map (CechGen.cechAug β') ≫
        DerivedCategory.Q.map ((HomologicalComplex.single LightCondAb
          (ComplexShape.up ℤ) 0).map ((free ℤ).map v)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hsq]
  -- two-out-of-three
  have h2 : Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map (CechGen.cechCmp β β' u v huv) ≫
        DerivedCategory.Q.map (CechGen.cechAug β)) :=
    Work.TOOLKIT.solidEquiv_comp _ _ hcmp haugβ
  have h3 : Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map (CechGen.cechAug β') ≫
        DerivedCategory.Q.map ((HomologicalComplex.single LightCondAb
          (ComplexShape.up ℤ) 0).map ((free ℤ).map v))) := by
    rw [← hsq']
    exact h2
  exact Work.TOOLKIT.solidEquiv_of_comp_left (DerivedCategory.Q.map (CechGen.cechAug β')) _
    haugβ' h3

end Work.ANALYTIC
