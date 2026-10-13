/-
# `Coer1SO/Defs.lean` — the open-class vocabulary of the `z`-integration by parts

The `z`-integration by parts of §6 and the integrability bundle `IntPkg` are stated in
`Submission/Work/FTS/CoercivityFix/Coer1/` for the *interior* class
`Work.FTS.LocData.SmoothQuad` (`C^∞` on the half-strip `z > -1`).  The level-four coercivity
of the open class `RegQo α 4`, however, only provides `SmoothOpen` (`C^∞` on the *open*
quadrant `z > 0`), and the two classes are not comparable in the direction needed: the
projected mollified slice is `SmoothOpen` but never `SmoothQuad`.

This file fixes the corresponding vocabulary:

* `ZIBPO u` — the open-class `z`-integration-by-parts package: `SmoothOpen u` (instead of
  `SmoothQuad u`), the two boundary limits and the a.e. honesty of the two one-dimensional
  integrals of the fundamental theorem of calculus.  It is the verbatim analogue of
  `Work.FTS.CoercivityFix.Coer1.ZIBP` with `smooth : SmoothOpen u`.
* `IP2O α f` — the fragment of the integrability bundle
  (`Work.FTS.CoercivityFix.Coer1.IntPkg`) that the base estimate
  `H1IP α (D_z f) f` of the `D_z`-clause consumes, with the same fields but open-class
  regularity.

Both structures are pure `Prop`s; they are proved for `RegQo α 2` data in the sibling modules
`zibpO_of.lean` / `IP2O_of.lean` and consumed in the `D_z`-clause port of the assembly.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1SO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The open-class `z`-integration-by-parts package -/

/-- **The `z`-integration-by-parts hypotheses in the open class.**  This is
`Work.FTS.CoercivityFix.Coer1.ZIBP` with the smoothness field weakened from the analytic
`SmoothQuad` to the honest `SmoothOpen` (`C^∞` on the open quadrant `(0,∞) × (0,π/2)`, the
class carried by `RegQo`).

Every consumer of `ZIBP` in the `z`-IBP of §6 uses the smoothness only through the
differentiability of the `z`-slices at `z > 0` and the chain rule there, both of which
`SmoothOpen` supplies; the boundary limits are asked on the open angular interval and the two
one-dimensional integrals only a.e. in the angle, exactly as before. -/
structure ZIBPO (u : Fn) : Prop where
  /-- the datum is `C^∞` on the open quadrant -/
  smooth : Work.FTS.EllipticEst.SmoothOpen u
  /-- the boundary term `z (u w)²` vanishes at `z = 0⁺` -/
  bd0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0)
  /-- the boundary term `z (u w)²` vanishes at `z = ∞` -/
  bdTop : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0)
  /-- a.e. in the angle, `(u w)²` is `z`-integrable -/
  intSq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    MeasureTheory.IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0)
  /-- a.e. in the angle, the derivative of the boundary term is `z`-integrable -/
  intDeriv : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0)

/-! ## The fragment of `IntPkg` consumed by the base estimate of the `D_z`-clause -/

/-- **The integrability fragment of the `D_z`-clause at level 2, in the open class.**  This
carries exactly the certificates that `H1IP α (D_z f) f ≤ 10²²·|f|²_{ℋ¹}` consumes (see the
frozen proof in `Assembly/V_bounds.lean`): the squared `D_z`-blocks at levels `0, 1` in the
`η`-weight, the squared `f`-, `D_z f`- and `D_θ f`-blocks in the plain radial weight, the
`D_θ f`-block in the `γ`-weight, the four `𝓛`-pairings, and the a.e. commutation
`D_z D_θ f = D_θ D_z f` used to identify the last pairing. -/
structure IP2O (α : ℝ) (f : Fn) : Prop where
  /-- `(D_z f)²·ρ_η` is jointly integrable -/
  sqDzEta_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `f²·ρ_η` is jointly integrable -/
  sqDzEta_zero : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      f z θ ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `f²·w²` is jointly integrable -/
  sqDzOne_zero : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => f z θ ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `(D_z f)²·w²` is jointly integrable -/
  sqDzOne_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.Dz f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `(D_θ f)²·w²` is jointly integrable -/
  sqDthOne : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `(D_θ f)²·ρ_γ` is jointly integrable -/
  sqDthGam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the `η`-weight is jointly integrable -/
  intL_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the `η`-weight is jointly integrable -/
  intL_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the plain radial weight is jointly integrable -/
  intL_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the plain radial weight is jointly integrable -/
  intL_Dz_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the plain radial weight is jointly integrable -/
  intL_Dth_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the `γ`-weight is jointly integrable -/
  intL_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `D_z` and `D_θ` commute almost everywhere on the quadrant -/
  dzDthComm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.Spaces.Dth f) z θ = Work.Spaces.Dth (Work.Spaces.Dz f) z θ

end Work.FTS.CoercivityFix.Coer1SO
