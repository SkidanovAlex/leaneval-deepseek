import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **Base change of a closed immersion along a field extension is a closed immersion.**

This is the (trivial) flatness-free half of "base change preserves the geometry": the square
```
baseChange K L X --baseChangeProj--> X
      |                              |
 baseChangeMap f                     f
      v                              v
baseChange K L Y --baseChangeProj--> Y
```
(with the projections as the second projection of the fibred product `X ×_{Spec K} Spec L`) is
cartesian, so `baseChangeMap K L f` is the base change of the closed immersion `f` along
`baseChangeProj K L Y`.  Since `IsClosedImmersion` is stable under base change, we are done. -/
theorem isClosedImmersion_baseChangeMap (K L : Type) [Field K] [Field L] [Algebra K L]
    {X Y : AlgebraicGeometry.Scheme.{0}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (f : X ⟶ Y)
    [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsClosedImmersion f] :
    AlgebraicGeometry.IsClosedImmersion (Work.K3.baseChangeMap K L f) := by
  -- The square relating `baseChangeMap K L f` to the two projections is cartesian.
  have hsq : IsPullback (baseChangeMap K L f) (baseChangeProj K L X) (baseChangeProj K L Y) f := by
    refine IsPullback.of_right ?_ ?_ (baseChange_isPullback K L Y)
    · -- the "big" square: paste the pullback square of `X` with the projection of `Y`
      have h1 : baseChangeMap K L f ≫ pullback.fst (specMap K L) (Y ↘ Spec (.of K))
          = pullback.fst (specMap K L) (X ↘ Spec (.of K)) := by
        simp only [baseChangeMap, baseChange, pullback.map, Category.comp_id]
        rw [pullback.lift_fst]
      have h2 : f ≫ (Y ↘ Spec (.of K)) = (X ↘ Spec (.of K)) :=
        ((Hom.isOver_iff (S := Spec (.of K))).mp
          (inferInstance : f.IsOver (Spec (.of K))))
      rw [h1, h2]
      exact baseChange_isPullback K L X
    · -- commutativity of the square, i.e. the second projection of `pullback.map`
      simp only [baseChangeMap, baseChangeProj, baseChange, pullback.map, Category.comp_id]
      rw [pullback.lift_snd]
  -- `baseChangeMap K L f` is the base change of `f` along `baseChangeProj K L Y`.
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
    (inferInstance : AlgebraicGeometry.IsClosedImmersion f)

end Work.K3
