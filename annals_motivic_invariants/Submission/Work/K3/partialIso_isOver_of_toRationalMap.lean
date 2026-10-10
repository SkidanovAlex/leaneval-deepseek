import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.K3

/-- A partial isomorphism whose underlying rational map is the forward map of a birational map
defined over `𝕜` is itself defined over `𝕜`.

Since `X` is reduced and `Spec 𝕜` is separated, a partial map `f : X.PartialMap Y` is a
`𝕜`-map as soon as its rational map is (`PartialMap.isOver_toRationalMap_iff_of_isSeparated`).
The hypothesis `i.toRationalMap = ψ.hom` turns `ψ.IsOver 𝕜` into `i.toRationalMap.IsOver 𝕜`,
and `i.toRationalMap` is by definition the rational map of `i.toPartialMap`. -/
theorem partialIso_isOver_of_toRationalMap (𝕜 : Type) [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [AlgebraicGeometry.IsReduced X]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (i : X.PartialIso Y) (ψ : X.BirationalMap Y)
    [ψ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (hi : i.toRationalMap = ψ.hom) :
    i.toPartialMap.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
  rw [← PartialMap.isOver_toRationalMap_iff_of_isSeparated]
  change i.toRationalMap.IsOver (Spec (CommRingCat.of 𝕜))
  rw [hi]
  infer_instance

end Work.K3
