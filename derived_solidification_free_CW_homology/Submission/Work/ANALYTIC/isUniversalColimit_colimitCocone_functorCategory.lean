import Mathlib
import Submission.Work.ANALYTIC.isVanKampenColimit_of_isColimit_types

namespace Work.ANALYTIC

/-- **Coproducts in a functor category `C ⥤ Type` are universal.**

Route.  `isVanKampenColimit_of_evaluation` (with the target category `Type`, `J := Discrete ι`)
reduces this to the pointwise statement: for every `x : C` the evaluation cocone
`(((evaluation C Type).obj x).mapCocone (colimit.cocone F))` is a colimit cocone in `Type`, because
`evaluation C Type x` preserves `Discrete ι`-colimits (`evaluation_preservesColimitsOfShape` and
`isColimitOfPreserves`), and every colimit cocone over a discrete diagram in `Type` is van Kampen
by `Work.ANALYTIC.isVanKampenColimit_of_isColimit_types`.  Then `IsVanKampenColimit.isUniversal`
finishes. -/
theorem isUniversalColimit_colimitCocone_functorCategory {C : Type _} [CategoryTheory.Category C] {ι : Type} {F : CategoryTheory.Functor (CategoryTheory.Discrete ι) (CategoryTheory.Functor C Type)} : CategoryTheory.IsUniversalColimit (CategoryTheory.Limits.colimit.cocone F) := by
  -- It suffices to prove the van Kampen property, and this can be checked pointwise.
  refine (CategoryTheory.isVanKampenColimit_of_evaluation F
    (CategoryTheory.Limits.colimit.cocone F) ?_).isUniversal
  intro x
  -- `evaluation C Type x` preserves `Discrete ι`-colimits, so the evaluated cocone is a colimit
  -- cocone in `Type`; every such cocone over a discrete diagram is van Kampen.
  exact Work.ANALYTIC.isVanKampenColimit_of_isColimit_types
    (CategoryTheory.Limits.isColimitOfPreserves ((CategoryTheory.evaluation C Type).obj x)
      (CategoryTheory.Limits.colimit.isColimit F))

end Work.ANALYTIC
