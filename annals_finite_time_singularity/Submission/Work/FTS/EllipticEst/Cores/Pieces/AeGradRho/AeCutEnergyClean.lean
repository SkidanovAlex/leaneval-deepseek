/-
Copyright: work module for the Elgindi finite-time singularity project.

# The truncated `w²`-weighted energy inequality in the `AeData` class (statement only)

This module fixes the *statement* of the crux of Step 1 of Elgindi's `prop:H2`: the
`w²`-weighted energy inequality for a datum `Work.FTS.EllipticEst.H2W.Ae.AeData α u G`, proved
first for a *compactly supported* radial cut-off `φ ∈ C²` with `0 ≤ φ ≤ 1` which vanishes in a
neighbourhood of `z = 0`.  It is exactly the conclusion of
`Work.FTS.EllipticEst.H2W.AeProof.AeCutEnergyV2` (whose proof is still missing), minus the
(unused) a.e.-continuity hypothesis.

The statement is packaged as the `Prop` `AeCutEnergyProp` so that it can be passed as a
hypothesis; its inhabitant is proved in `AeCutEnergyProof.lean`.  The plan of the proof is
recorded in `NOTES_aeCutEnergy.md` in this directory.

## Route

With `W z := φ z * (w z)^2` and `K := 13/2 + (3 α² + (3/2) α (5+α))`:

1. `A_φ := ∫⁻_z ofReal (W z z²) * (∫⁻_θ ofReal ((∂_z u)²)) < ⊤` (the radial finiteness),
   which is the clean-cone lemma `AngAWeak.AeCutA.aeCutAfiniteA`;
2. per `θ`, `zIBP_compact` (two `z`-integrations by parts, the boundary terms vanishing because
   `W` is compactly supported in `(0,∞)`) gives
   `∫_z W (α²z²u_zz + α(5+α)zu_z) u = -α²∫_z W (z u_z)² + (α²/2)∫_z (z²W)'' u² - (α(5+α)/2)∫_z (zW)' u²`;
   combined with the equation `bslOp α u = G` this is the per-`θ` identity
   `α² α_θ = ι_θ + α² γ_θ + α(5+α) ε_θ - κ_θ`;
3. the `θ`-slice self-form `LzeroSelfFormHon` gives, for a.e. `z`,
   `∫_θ (∂_θu)² ≤ ∫_θ Lzero u·u + 6 ∫_θ u²`;
4. Fubini combines 2 and 3 (all the joint integrability coming from 1 and from
   `HkMem α 0 (z²∂_zzu)`, `HkMem α 0 G`);
5. the weight algebra `weight_algebra_fts` (`(z²w²)'' ≤ 6w²`, `|(zw²)'| ≤ 3w²`) produces the
   constant `K` and the explicit truncation error, and `∫⁻`-to-Bochner conversions finish.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst.Cores.Pieces.AeGradRho

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The radial cut weight `W = φ w²` of the truncated energy inequality. -/
def cutW (φ : ℝ → ℝ) (z : ℝ) : ℝ := φ z * (Work.Spaces.w z) ^ 2

/-- **The statement of the truncated `w²`-weighted energy inequality** of Step 1 of `prop:H2` in
the `AeData` class, as a `Prop`.  For a `C²` cut-off `φ` with `0 ≤ φ ≤ 1`, compact support and
`φ = 0` near `z = 0`,

`α²∫⁻ (φw²z²)(∫⁻ (∂_zu)²) + ∫⁻ (φw²)(∫⁻ (∂_θu)²)
   ≤ K ∫⁻ (φw²)(∫⁻ u²) + ½∫⁻ (φw²)(∫⁻ G²σ) + err`,

where `K = 13/2 + 3α² + (3/2)α(5+α)` and `err` is the explicit truncation error.  Same statement
as `H2W.AeProof.AeCutEnergyV2`, minus the (unused) a.e.-continuity hypothesis. -/
def AeCutEnergyProp (α : ℝ) (u G : ℝ → ℝ → ℝ) : Prop :=
  Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
  (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
  (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
    Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
  ∀ (φ : ℝ → ℝ),
    ContDiff ℝ 2 φ → HasCompactSupport φ → (∀ z : ℝ, z ≤ 0 → φ z = 0) →
    (∀ z : ℝ, 0 ≤ φ z) → (∀ z : ℝ, φ z ≤ 1) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → φ z = 0) →
    ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤) →
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
    ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
        * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      + ENNReal.ofReal (1 / 2)
        * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
              + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))

end Work.FTS.EllipticEst.Cores.Pieces.AeGradRho
