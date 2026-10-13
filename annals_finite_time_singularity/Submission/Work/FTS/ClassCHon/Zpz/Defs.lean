/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for `Work.FTS.ClassCHon.Zpz.cmode_Dz`

The target lemma is the compatibility of the angular mode coefficient `cmode m` with the
radial operator `D_z = z ∂_z`:

  `cmode m (D_z F) z = z · d/dz (cmode m F) z`   for `z > 0`,

for a source `F` which is `C^∞` on the open quadrant and honest in `ℋ²`.

Since `cmode m F z = N_m(F, z) / D_m` with `D_m = ∫_θ e_m² cos θ` a positive constant
(`Work.FTS.PhiStar.Gegenbauer.FamNormValue`), the lemma reduces to the purely `θ`-integrated
statement

  `N_m(∂_z F, z) = d/dz N_m(F, z)`,

where `N_m(G, z) = ∫_{Iθ} G z θ · φ_m(θ) dθ` and `φ_m(θ) = e_m(θ) cos θ` is the angular weight.
The derivative is taken under the integral sign, which needs the `z`-differential quotient of
the slices to be dominated by an `L¹`-in-`θ` quantity; the domination comes from the `ℋ²`
membership through the second-order `θ`-slice bound

  `∫_θ |∂_z² F(τ,θ)| dθ ≤ (2/τ²) ∫_θ √(HkIntegrand α 2 F τ θ)`.

This file fixes the vocabulary shared by the target and its auxiliary lemmas; the definitions
`phiW`, `numW`, `pwF` and `Hsq` live here so that the auxiliary lemmas (which are proved in
parallel, in `Submission/Work/FTS/ClassCHon/Zpz/Aux/`) can refer to them.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false

/-- The angular weight `φ_m(θ) = e_m(θ)·cos θ` of the `m`-th mode. -/
def phiW (m : ℕ) (θ : ℝ) : ℝ :=
  Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ

/-- The numerator of the mode coefficient `cmode m F z`, written as a set integral over the
closed angular interval `Iθ = [0,π/2]`. -/
def numW (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, F z θ * phiW m θ

/-- The `θ`-integral of `∂_z F · φ_m`: the numerator of `cmode m (∂_z F) z`, i.e. the function
whose value at `z` is the derivative of `numW m F` at `z`. -/
def pwF (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * phiW m θ

/-- The `θ`-slice `L¹`-mass of `√(HkIntegrand α 2 F ·)` at radius `τ`. -/
def Hsq (α : ℝ) (F : ℝ → ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)

end Work.FTS.ClassCHon.Zpz
