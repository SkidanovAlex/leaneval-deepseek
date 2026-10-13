/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/IntPkgO.lean` — the open-class integrability bundle
`IntPkgO`

The four coercivity estimates of the frozen `CoercivityFix/Coer1T` chapter consume the
integrability certificate bundle `Work.FTS.CoercivityFix.Coer1.IntPkg` (defined in
`CoercivityFix/Coer1/Defs.lean`, proved for `RegQ α 2 f` in `CoercivityFix/Coer1/IntFacts.lean`).
That bundle is **not** available on the open class: three of its fields are
`zibp_f : ZIBP f`, `zibp_Dz : ZIBP (Dz f)`, `zibp_Dth : ZIBP (Dth f)`, and `ZIBP`'s first field is
`smooth : LocData.SmoothQuad u` — the flatness-at-`z = 0` condition that `RegQo` does not supply
(and that is *false* for the route's projected slices, `not_smoothQuad_Pz_Jeps`).

This file is the verbatim open-class analogue: the same field list, with the three
`z`-integration-by-parts fields taken in the open class `CoercivityFix.Coer1SO.ZIBPO` (defined by
the sibling `Coer1SO` chapter) instead of `ZIBP`.  The remaining fields are pure `IntegrableOn`
certificates and are literally the same.

The planned consumer is `IntPkg_O` (`RegQo α 2 f → IntPkgO α f`), the open-class re-run of
`CoercivityFix.Coer1.IntPkg_Q`, after which the four slot estimates of `Coer1T` can be ported
one by one with `CoerAdm` replaced by `CoerAdmO`.

Everything here is `sorry`-free (the module only *defines* a structure).
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1SO.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The open-class integrability bundle**: `CoercivityFix.Coer1.IntPkg` with the three
`z`-integration-by-parts fields taken in the open class `CoercivityFix.Coer1SO.ZIBPO`. -/
structure IntPkgO (α : ℝ) (f : Fn) : Prop where
  /-- the squared `D_z`-blocks with the `η`-weight -/
  sqDzEta : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `η`-weight -/
  sqMixedEta : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the `γ`-weight -/
  sqMixedGam : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared `D_z`-blocks with the plain radial weight -/
  sqDzOne : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the squared mixed blocks with the plain radial weight -/
  sqMixedOne : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the `η`-weight -/
  intL_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the `η`-weight -/
  intL_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the `γ`-weight -/
  intL_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the plain radial weight -/
  intL_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `Lhat`-pairing of `D_z f` with the `η`-weight -/
  intLhat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `D_z`-commutator defect against `D_z f` with the `η`-weight -/
  intE2hat_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the `η`-weight -/
  hint_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_z f` with the `η`-weight -/
  hint_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
      * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `D_θ f` with the `γ`-weight -/
  hint_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the transport pairing of `f` with the plain radial weight -/
  hint_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * f z θ
      * Work.Spaces.w z ^ 2 / (1 + z)))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `z`-integration-by-parts hypotheses for `f` -/
  zibp_f : Work.FTS.CoercivityFix.Coer1SO.ZIBPO f
  /-- the `z`-integration-by-parts hypotheses for `D_z f` -/
  zibp_Dz : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dz f)
  /-- the `z`-integration-by-parts hypotheses for `D_θ f` -/
  zibp_Dth : Work.FTS.CoercivityFix.Coer1SO.ZIBPO (Work.Spaces.Dth f)

end Work.FTS.StrongEps.EpsE4Thr
