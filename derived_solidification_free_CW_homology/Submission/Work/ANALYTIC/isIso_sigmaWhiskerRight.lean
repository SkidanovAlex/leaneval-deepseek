import Mathlib
import Submission.Work.ANALYTIC.HICond

set_option linter.style.haveILetI false

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed in
/-- **`- ⊗ [0,1]` sends coproducts to coproducts, with the obvious inclusions.**  For a family
`F : ι → LightCondSet`, the canonical map `Sigma.desc (fun y => Sigma.ι F y ▷ Icond)` from
`∐_y (F y ⊗ Icond)` to `(∐_y F y) ⊗ Icond` is an isomorphism.

This is the statement that the cocone `((∐ F) ⊗ Icond, fun y => Sigma.ι F y ▷ Icond)` is a colimit
cocone: `LightCondSet` is monoidal closed, so `- ⊗ Icond` is a left adjoint (of the internal hom
`[Icond, -]`) and preserves coproducts.  A short proof: `Sigma.desc (fun y => Sigma.ι F y ▷ Icond)`
is `sigmaComparison (tensorRight Icond) F`, which is invertible because `tensorRight Icond`
preserves the colimit `Discrete.functor F`. -/
theorem isIso_sigmaWhiskerRight {ι : Type} (F : ι → LightCondSet.{0}) [HasCoproduct F]
    [HasCoproduct (fun y => F y ⊗ Work.ANALYTIC.Icond)] :
    IsIso (Sigma.desc (fun y => Sigma.ι F y ▷ Work.ANALYTIC.Icond) :
      (∐ fun y => F y ⊗ Work.ANALYTIC.Icond) ⟶ (∐ F) ⊗ Work.ANALYTIC.Icond) := by
  -- `- ⊗ Icond` is a left adjoint (of the internal hom `[Icond, -]`), hence preserves the
  -- coproduct of `F`; equivalently its coproduct comparison map is invertible.
  haveI : PreservesColimit (Discrete.functor F) (tensorRight Work.ANALYTIC.Icond) :=
    inferInstance
  haveI : HasCoproduct (fun y => (tensorRight Work.ANALYTIC.Icond).obj (F y)) :=
    ‹HasCoproduct (fun y => F y ⊗ Work.ANALYTIC.Icond)›
  have h : IsIso (sigmaComparison (tensorRight Work.ANALYTIC.Icond) F) := inferInstance
  -- the two maps are definitionally the same
  convert h using 2 <;> rfl

end Work.ANALYTIC
