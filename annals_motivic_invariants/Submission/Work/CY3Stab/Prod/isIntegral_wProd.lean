import Mathlib
import Submission.Work.CY3Stab.Cylinder

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The cylinder `𝔸ᵏ ×_𝕜 X` of an integral `𝕜`-scheme is integral.

Route (all pieces are in Mathlib; `infer_instance` does NOT close it because the available
`IsIntegral (pullback f g)` instance carries a `[IsLocallyNoetherian Y]` hypothesis which is not
available here):
* `IrreducibleSpace (WProd X k)` is the instance
  `[GeometricallyIrreducible f] [UniversallyOpen f] [IrreducibleSpace Y] :
     IrreducibleSpace ↥(pullback f g)` (Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean)
  applied to `f := AffineK k ↘ Spec 𝕜` — use `inferInstanceAs`/`change` with
  `Limits.pullback (AffineK k ↘ Spec 𝕜) (X ↘ Spec 𝕜)`, and note
  `Work.K3Inputs.geometricallyIntegral_affineN 𝕜 k : GeometricallyIntegral (AffineK k ↘ Spec 𝕜)`.
* `IsReduced (WProd X k)` from
  `GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents` applied to the projection
  `pullback.snd (AffineK k ↘ Spec 𝕜) (X ↘ Spec 𝕜)`, using `[GeometricallyReduced …]` (from the
  `GeometricallyIntegral` instance via typeclass search), `[Flat …]` (base change of the flat
  `AffineK k ↘ Spec 𝕜`), `[IsReduced X]` and `[Finite (irreducibleComponents X)]` (from
  `IrreducibleSpace X` via `irreducibleComponents_eq_singleton`).
* conclude with `rw [isIntegral_iff_irreducibleSpace_and_isReduced]`. -/
theorem isIntegral_wProd {𝕜 : Type} [Field 𝕜] {X : AlgebraicGeometry.Scheme.{0}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] [AlgebraicGeometry.IsIntegral X] (k : ℕ) : AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) := by
  -- `𝔸ᵏ ⟶ Spec 𝕜` is geometrically integral (hence geometrically irreducible and geometrically
  -- reduced), and smooth (hence flat, hence universally open).
  haveI hAg : GeometricallyIntegral (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) :=
    Work.K3Inputs.geometricallyIntegral_affineN 𝕜 k
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨?_, ?_⟩
  · -- `𝔸ᵏ ×ₛ X` is irreducible: base change of the geometrically irreducible, universally open
    -- `𝔸ᵏ ⟶ Spec 𝕜` along `X ⟶ Spec 𝕜` with `X` irreducible.
    infer_instance
  · -- A variety is reduced iff it is reduced at its generic points; `X` is irreducible, so it has
    -- a single irreducible component and `pullback.snd` is geometrically reduced and flat.
    haveI : Finite (irreducibleComponents X) := by
      rw [irreducibleComponents_eq_singleton (X := X)]
      infer_instance
    exact GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
      (pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)))

end Work.CY3Stab.Prod
