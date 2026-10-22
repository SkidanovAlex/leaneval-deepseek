import Mathlib
import Submission.Work.ANALYTIC.HICond
import Submission.Work.ANALYTIC.kernel_prTop_tensor

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

attribute [local instance] lightCondSetHasCoproduct

/-! ## The two forms of the projection agree

The projection `prTop Y` of topological spaces and the condensed projection `prTopI Y` are the first
projections of the products `Y × [0,1]` and `Y ⊗ Icond`; the two products are identified by the
strong monoidality of `topCatToLightCondSet` (which preserves finite products, being a right
adjoint — `Work.ANALYTIC.instMonoidalTopCatToLightCondSet`, used through
`Functor.Monoidal.μ_fst`).  Transporting along this isomorphism of domains identifies the two
projections, hence also their images under `ℤ[-]`. -/

/-- `prTopI Y` is the first projection of the cartesian product `Y ⊗ Icond` in `LightCondSet`. -/
private lemma solidEquiv_prTopI_fst_eq (Y : TopCat.{0}) :
    SemiCartesianMonoidalCategory.fst (topCatToLightCondSet.obj Y)
      (topCatToLightCondSet.obj unitIntervalTopCat) = prTopI Y := by
  rw [prTopI, prodProj, SemiCartesianMonoidalCategory.fst_def]
  rfl

/-- The tensorator of `topCatToLightCondSet` turns the topological projection `prTop Y` into the
projection `fst` of `LightCondSet`. -/
private lemma solidEquiv_prTopI_muIso_fst (Y : TopCat.{0}) :
    (Functor.Monoidal.μIso topCatToLightCondSet Y unitIntervalTopCat).hom ≫
      topCatToLightCondSet.map (prTop Y) =
    SemiCartesianMonoidalCategory.fst (topCatToLightCondSet.obj Y)
      (topCatToLightCondSet.obj unitIntervalTopCat) := by
  rw [prTop_eq_fst, Functor.Monoidal.μIso_hom]
  exact @Functor.Monoidal.μ_fst TopCat _ _ LightCondSet _ _ topCatToLightCondSet
    instMonoidalTopCatToLightCondSet Y unitIntervalTopCat

/-- **The projections agree.**  The tensorator `μ` of `topCatToLightCondSet` (the canonical
isomorphism `Y ⊗ [0,1] ≅ Y × [0,1]` supplied by strong monoidality) carries `prTop Y` to
`prTopI Y`. -/
private lemma solidEquiv_prTopI_muIso (Y : TopCat.{0}) :
    (Functor.Monoidal.μIso topCatToLightCondSet Y unitIntervalTopCat).hom ≫
      topCatToLightCondSet.map (prTop Y) = prTopI Y :=
  (solidEquiv_prTopI_muIso_fst Y).trans (solidEquiv_prTopI_fst_eq Y)

/-- If `G = e ≫ F` with `e` an isomorphism, a solid-equivalence for `G` gives one for `F`. -/
private lemma solidEquiv_of_iso_comp {A B C : DLightCondAb} (e : A ≅ B) (F : B ⟶ C) (G : A ⟶ C)
    (h : e.hom ≫ F = G) (hG : Submission.Blueprint.SolidEquiv G) :
    Submission.Blueprint.SolidEquiv F := by
  intro N
  have hcomp : (fun g : C ⟶ derivedInclusion.obj N => F ≫ g) =
      (fun k : A ⟶ derivedInclusion.obj N => e.inv ≫ k) ∘
        (fun g : C ⟶ derivedInclusion.obj N => G ≫ g) := by
    funext g
    show F ≫ g = e.inv ≫ (G ≫ g)
    rw [← h, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hcomp]
  exact (bijective_precomp_iso e.inv (derivedInclusion.obj N)).comp (hG N)

/-- **The two forms of the projection agree.**  The projection `prTop Y` of topological spaces is
carried by `ℤ[-]` to the condensed projection `Work.ANALYTIC.prTopI Y` (the first projection of
the product with the interval, `Submission/Work/ANALYTIC/HICond.lean`), up to the canonical
isomorphism `Y × [0,1] ≅ Y ⊗ Icond` supplied by the strong monoidality of `ℤ[-]`.  Hence a
solid-equivalence for one form gives one for the other. -/
theorem solidEquiv_prTopI_dFree (Y : TopCat.{0}) :
    Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map
          ((free ℤ).map (Work.ANALYTIC.prTopI Y))) →
      Submission.Blueprint.SolidEquiv (Submission.Blueprint.dFree (Work.ANALYTIC.prTop Y)) := by
  intro h
  refine solidEquiv_of_iso_comp
    ((DerivedCategory.singleFunctor LightCondAb 0).mapIso ((free ℤ).mapIso
      (Functor.Monoidal.μIso topCatToLightCondSet Y unitIntervalTopCat)))
    (Submission.Blueprint.dFree (prTop Y))
    ((DerivedCategory.singleFunctor LightCondAb 0).map ((free ℤ).map (prTopI Y))) ?_ h
  show (DerivedCategory.singleFunctor LightCondAb 0).map ((free ℤ).map
      (Functor.Monoidal.μIso topCatToLightCondSet Y unitIntervalTopCat).hom) ≫
      (DerivedCategory.singleFunctor LightCondAb 0).map ((free ℤ).map
        (topCatToLightCondSet.map (prTop Y))) =
    (DerivedCategory.singleFunctor LightCondAb 0).map ((free ℤ).map (prTopI Y))
  rw [← Functor.map_comp, ← Functor.map_comp, solidEquiv_prTopI_muIso]
  rfl

end Work.ANALYTIC
