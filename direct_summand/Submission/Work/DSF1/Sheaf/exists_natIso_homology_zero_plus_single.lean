import Mathlib
import Submission.Work.DSG1.rdfpuBridge
import Submission.Work.DSG1.PlusSingle
import Submission.Work.DSF1.Sheaf.AcyclicToolkit
import Submission.Work.DSF1.Sheaf.isIso_homology_zero_unit_single

/-!
# `H⁰ R F A[0] ≅ F A`, naturally

For an additive, left exact functor `F : C ⥤ D` between abelian categories, with `C` having enough
injectives, the composite

`C --single_0--> D⁺(C) --R F--> D⁺(D) --H⁰--> D`

is naturally isomorphic to `F`. Indeed `H⁰ (R F (A[0])) ≅ R⁰ F (A) ≅ F (A)` because `F` is left
exact.

The proof is a packaging of the naturality of the unit `rightDerivedFunctorPlusUnit'` of the right
derived functor:

* whiskering the unit `u : F ⋙ single_0 ⟶ single_0 ⋙ R F` with `H⁰` gives a natural transformation
  `u' : F ⋙ (single_0 ⋙ H⁰) ⟶ (single_0 ⋙ R F) ⋙ H⁰`, whose component at `A` is
  `H⁰ (u_A) : H⁰ ((F A)[0]) ⟶ H⁰ (R F (A[0]))`;
* `H⁰ (u_A)` is an isomorphism because `F` is left exact: this is
  `Work.DSF1.Sheaf.isIso_homology_zero_unit_single`, transported across the identification
  `Work.DSG1.rdfpuBridge` of the unit `rightDerivedFunctorPlusUnit'` with the complex level unit
  `Functor.rightDerivedFunctorPlusUnit`;
* `single_0 ⋙ H⁰ ≅ 𝟭 D` (`Work.DSG1.plusSingleFunctorHomologyIso`).
-/

namespace Work.DSF1.Sheaf

open CategoryTheory CategoryTheory.Limits

universe u v w x

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- `H⁰` of the component at `A` of the unit `rightDerivedFunctorPlusUnit' F 0` is an
isomorphism: this is the comparison `H⁰ (R F (A[0])) ≅ R⁰ F (A)` (with both sides isomorphic to
`F A`), which is an isomorphism because `F` is left exact. -/
theorem isIso_homology_zero_rightDerivedFunctorPlusUnit' {C : Type u} [Category.{v} C]
    [Abelian C] [EnoughInjectives C] {D : Type w} [Category.{x} D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (A : C) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0).app A)) := by
  rw [Work.DSG1.rdfpuBridge F A]
  simp only [Functor.map_comp]
  have hA : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app (Work.DSG1.singlePlusObj C A))) :=
    isIso_homology_zero_unit_single F A
  haveI := hA
  infer_instance

theorem exists_natIso_homology_zero_plus_single {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F] :
    Nonempty ((CategoryTheory.Functor.comp
      (CategoryTheory.Functor.comp (DerivedCategory.Plus.singleFunctor C 0)
        F.rightDerivedFunctorPlus)
      (DerivedCategory.Plus.homologyFunctor D 0)) ≅ F) := by
  classical
  have hv : ∀ A : C, IsIso ((Functor.whiskerRight
      (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0)
      (DerivedCategory.Plus.homologyFunctor D 0)).app A) := by
    intro A
    exact isIso_homology_zero_rightDerivedFunctorPlusUnit' F A
  haveI : IsIso (Functor.whiskerRight
      (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0)
      (DerivedCategory.Plus.homologyFunctor D 0)) :=
    (NatTrans.isIso_iff_isIso_app _).mpr hv
  refine ⟨(asIso (Functor.whiskerRight
    (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' F 0)
    (DerivedCategory.Plus.homologyFunctor D 0))).symm ≪≫ ?_⟩
  exact Functor.isoWhiskerLeft F (Work.DSG1.plusSingleFunctorHomologyIso (D := D)) ≪≫
    Functor.rightUnitor F

end Work.DSF1.Sheaf
