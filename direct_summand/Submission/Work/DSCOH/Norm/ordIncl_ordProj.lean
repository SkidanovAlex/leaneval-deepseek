import Mathlib
import Submission.Work.DSCOH.Norm.Complexes

namespace Work.DSCOH.Norm

open CategoryTheory

universe u v w

/-- **Degreewise form of `ordIncl ≫ ordProj = 𝟙`** on the ordered Čech complex.

The projection `ordProj` reads off the coordinates of the semi-ordered term indexed by the
*strictly increasing* tuples, and `ordIncl` maps the ordered term back into the semi-ordered
term by the identity on those coordinates and `0` on all others.  Hence on the ordered
coordinates the composite is the identity: by `Pi.hom_ext` it suffices to compute the `x`-th
component for `x : OrdIdx ι n`, where the composite of the two `Pi.lift`s is evaluated by
`Pi.lift_comp_π`, the `dite` defining `ordIncl` resolves through the proof `x.property` that
`x` is strictly increasing, and what remains is `𝟙 ≫ π = π`. -/
lemma ordIncl_ordProj_pi {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    ordIncl P U n ≫ ordProj P U n = 𝟙 (ordTerm P U n) := by
  apply CategoryTheory.Limits.Pi.hom_ext (f := fun z : OrdIdx ι n => tupleMod P U z.val)
  intro x
  erw [CategoryTheory.Category.assoc, ordProj_comp_pi]
  erw [ordIncl_comp_pi P U n x.val x.property.monotone]
  erw [dite_eq_left x.property]
  exact (CategoryTheory.Category.id_comp _).symm

theorem ordIncl_ordProj {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) :
    Work.DSCOH.Norm.ordInclC P U ≫ Work.DSCOH.Norm.ordProjC P U =
      𝟙 (Work.DSCOH.Norm.ordT P U) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, ordInclC_f, ordProjC_f, HomologicalComplex.id_f]
  exact ordIncl_ordProj_pi P U n

end Work.DSCOH.Norm
