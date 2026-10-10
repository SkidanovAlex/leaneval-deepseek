import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.smooth_baseChangeMap` — smoothness is preserved by base change

Base change along a field extension `K → L` preserves smoothness: if `f : X ⟶ Y` is a smooth
morphism of `K`-schemes, then the induced morphism
`baseChangeMap K L f : X ×_K Spec L ⟶ Y ×_K Spec L` of `L`-schemes is smooth.

The proof is the standard one.  The `baseChangeMap` is pinned by the two equations
`baseChangeMap K L f ≫ pullback.fst = pullback.fst` and
`baseChangeMap K L f ≫ pullback.snd = pullback.snd ≫ f`; together with the two pullback squares
`baseChange_isPullback K L X`, `baseChange_isPullback K L Y` and the compatibility
`f ≫ (Y ↘ Spec K) = (X ↘ Spec K)` these exhibit

```
X ×_K L --baseChangeMap K L f--> Y ×_K L
   |                                  |
   v                                  v
   X -------------- f -------------> Y
```

as a pullback square (`IsPullback.of_right`).  Transposing the square, the left vertical
`baseChangeMap K L f` becomes the base change of the smooth morphism `f`, so
`MorphismProperty.of_isPullback` (with the instance `smooth_isStableUnderBaseChange`) concludes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.K3

theorem smooth_baseChangeMap (K L : Type) [Field K] [Field L] [Algebra K L]
    {X Y : AlgebraicGeometry.Scheme.{0}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (f : X ⟶ Y)
    [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.Smooth f] :
    AlgebraicGeometry.Smooth (Work.K3.baseChangeMap K L f) := by
  -- the two components of `baseChangeMap K L f`
  have hgX : baseChangeMap K L f ≫ pullback.fst (specMap K L) (Y ↘ Spec (CommRingCat.of K)) =
      pullback.fst (specMap K L) (X ↘ Spec (CommRingCat.of K)) := by
    simp only [baseChangeMap, pullback.map, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hgY : baseChangeMap K L f ≫ pullback.snd (specMap K L) (Y ↘ Spec (CommRingCat.of K)) =
      pullback.snd (specMap K L) (X ↘ Spec (CommRingCat.of K)) ≫ f := by
    simp only [baseChangeMap, pullback.map, Category.comp_id]
    exact pullback.lift_snd _ _ _
  -- `f` commutes with the structure morphisms
  have hf : f ≫ (Y ↘ Spec (CommRingCat.of K)) = (X ↘ Spec (CommRingCat.of K)) :=
    (AlgebraicGeometry.Scheme.Hom.isOver_iff (S := Spec (CommRingCat.of K))).mp inferInstance
  -- the base-change square of `f` is cartesian
  have hQ : IsPullback (baseChangeMap K L f) (baseChangeProj K L X) (baseChangeProj K L Y) f := by
    refine IsPullback.of_right
      (X₁₁ := baseChange K L X) (X₁₂ := baseChange K L Y) (X₁₃ := Spec (CommRingCat.of L))
      (X₂₁ := X) (X₂₂ := Y) (X₂₃ := Spec (CommRingCat.of K))
      (h₁₁ := baseChangeMap K L f)
      (h₁₂ := pullback.fst (specMap K L) (Y ↘ Spec (CommRingCat.of K)))
      (h₂₁ := f)
      (h₂₂ := (Y ↘ Spec (CommRingCat.of K)))
      (v₁₁ := pullback.snd (specMap K L) (X ↘ Spec (CommRingCat.of K)))
      (v₁₂ := pullback.snd (specMap K L) (Y ↘ Spec (CommRingCat.of K)))
      (v₁₃ := specMap K L) ?_ ?_ (baseChange_isPullback K L Y)
    · rw [hgX, hf]; exact baseChange_isPullback K L X
    · exact hgY
  -- transposed, `baseChangeMap K L f` is the base change of the smooth morphism `f`
  exact MorphismProperty.of_isPullback hQ.flip ‹AlgebraicGeometry.Smooth f›

end Work.K3
