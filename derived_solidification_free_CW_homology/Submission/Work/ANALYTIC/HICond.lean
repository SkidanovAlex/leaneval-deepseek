import Mathlib
import Submission.Work.ANALYTIC.HISetup

/-!
# AN6, step 3: the `× [0,1]` side of the cover

We record the light condensed interval `Icond` and, for the cover `cov Y ⟶ Y` of
`Submission/Work/ANALYTIC/HISetup.lean`, the product maps

* `covMapI Y : cov Y ⊗ Icond ⟶ Y ⊗ Icond` (the product of `covMap Y` with `Icond`),
* `covProj Y : cov Y ⊗ Icond ⟶ cov Y` (the projection),
* `prTopI Y : Y ⊗ Icond ⟶ Y` (the projection),

satisfying the square `covProj Y ≫ covMap Y = covMapI Y ≫ prTopI Y`, which is the input `huv` of
the levelwise Čech engine `Work.ANALYTIC.solidEquiv_of_levelwise_cech`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

attribute [local instance] lightCondSetHasCoproduct

/-- The interval `[0,1]` as a light condensed set. -/
abbrev Icond : LightCondSet.{0} := (TopCat.of ↥unitInterval).toLightCondSet

/-- The projection `X × Icond ⟶ X`, for a light condensed set `X`. -/
abbrev prodProj (X : LightCondSet.{0}) : X ⊗ Icond ⟶ X :=
  (X ◁ SemiCartesianMonoidalCategory.toUnit Icond) ≫ (ρ_ X).hom

/-- The product of `covMap Y` with the interval. -/
abbrev covMapI (Y : TopCat.{0}) : cov Y ⊗ Icond ⟶ Y.toLightCondSet ⊗ Icond :=
  covMap Y ▷ Icond

/-- The projection `cov Y × Icond ⟶ cov Y`. -/
abbrev covProj (Y : TopCat.{0}) : cov Y ⊗ Icond ⟶ cov Y :=
  prodProj (cov Y)

/-- The projection `Y × Icond ⟶ Y` (the condensed version of `Work.ANALYTIC.prTop`). -/
abbrev prTopI (Y : TopCat.{0}) : Y.toLightCondSet ⊗ Icond ⟶ Y.toLightCondSet :=
  prodProj Y.toLightCondSet

/-- The square of the cover with the interval commutes. -/
theorem cov_square (Y : TopCat.{0}) :
    covProj Y ≫ covMap Y = covMapI Y ≫ prTopI Y := by
  have hwe : cov Y ◁ SemiCartesianMonoidalCategory.toUnit Icond ≫
        (covMap Y ▷ (𝟙_ LightCondSet)) =
      covMap Y ▷ Icond ≫
        (Y.toLightCondSet ◁ SemiCartesianMonoidalCategory.toUnit Icond) :=
    (whisker_exchange (covMap Y) (SemiCartesianMonoidalCategory.toUnit Icond)).symm
  have hru : (ρ_ (cov Y)).hom ≫ covMap Y =
      (covMap Y ▷ (𝟙_ LightCondSet)) ≫ (ρ_ Y.toLightCondSet).hom :=
    (MonoidalCategory.rightUnitor_naturality (covMap Y)).symm
  rw [covProj, covMapI, prTopI, prodProj, prodProj, Category.assoc, hru,
    ← Category.assoc, hwe, Category.assoc]

/-- The product of the cover with the interval is again an epimorphism. -/
theorem epi_covMapI (Y : TopCat.{0}) : Epi (covMapI Y) := by
  haveI := covMap_epi Y
  rw [covMapI]
  exact Functor.map_epi (MonoidalCategory.tensorRight Icond) (covMap Y)

end Work.ANALYTIC
