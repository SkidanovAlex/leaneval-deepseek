/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions for the `γ`-weighted slice Hardy inequality `Work.FTS.GalBasis.cut.sliceGamma`

For `γ > 1` there is a universal constant `C` with

  `∫_0^{π/2} G² sin(2θ)^{-γ} ≤ C ∫_0^{π/2} (G')² sin(2θ)^{2-γ}`

for every `G` of class `C¹` on `(0, π/2)` whose `(1-γ)`-trace `sin(2θ)^{1-γ}·G²` vanishes
at both endpoints (as a *limit*, which is what makes the inequality true: with endpoint
*values* only, `G = 1` near `0` with the values patched to `0` is a counterexample) and whose
two weighted integrals are integrable.

This module holds the vocabulary of the proof: the two weights `sgW`, `sgW0`, the flux
`sgA = Φ·sgW` of the completion of squares with its logarithmic derivative `sgPhi` and its
derivative `sgAd`, the two integrands `sgF`, `sgD`, the trace `sgE`, the increasing cover
`sgAlpha ↓ 0`, `sgBeta ↑ π/2` and the boundary-error term `sgFlux`, together with the
elementary pointwise facts on `Icc 0 (π/2)`.

The estimate itself is `Work.FTS.GalBasis.cut.sliceGamma_core` (module
`Submission.Work.FTS.GalBasis.cut.SliceGammaCore`) on a closed subinterval and
`Work.FTS.GalBasis.cut.sliceGamma` (module `Submission.Work.FTS.GalBasis.cut.sliceGamma`)
on the whole interval.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cut

set_option autoImplicit false

/-! ## The pointwise data -/

/-- `sin(2θ)`. -/
def sgS (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- `cos(2θ)`. -/
def sgC (θ : ℝ) : ℝ := Real.cos (2 * θ)

/-- The derivative weight `sin(2θ)^(2-γ)`. -/
def sgW (γ : ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - γ)

/-- The function weight `sin(2θ)^(-γ)`. -/
def sgW0 (γ : ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-γ)

/-- `Φ(θ) = -2b·cos(2θ)/sin(2θ)`, the logarithmic derivative of the test function of the
completion of squares. -/
def sgPhi (b : ℝ) (θ : ℝ) : ℝ := -2 * b * Real.cos (2 * θ) / Real.sin (2 * θ)

/-- `A(θ) = -2b·cos(2θ)·sin(2θ)^(1-γ) = Φ(θ)·sin(2θ)^(2-γ)`, the flux of the completion of
squares. -/
def sgA (γ b : ℝ) (θ : ℝ) : ℝ := -2 * b * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (1 - γ)

/-- The derivative of `sgA`. -/
def sgAd (γ b : ℝ) (θ : ℝ) : ℝ :=
  4 * b * (Real.sin (2 * θ)) ^ (2 - γ)
    + 4 * b * (γ - 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)

/-- The flux `A(θ)·G(θ)²` whose derivative is integrated by parts. -/
def sgCfun (γ b : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ := sgA γ b θ * (G θ) ^ 2

/-- The function-weight integrand `G(θ)²·sin(2θ)^(-γ)`. -/
def sgF (γ : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ := (G θ) ^ 2 * sgW0 γ θ

/-- The derivative-weight integrand `(deriv G)(θ)²·sin(2θ)^(2-γ)`. -/
def sgD (γ : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ := (deriv G θ) ^ 2 * sgW γ θ

/-- The `(1-γ)`-trace `sin(2θ)^(1-γ)·G(θ)²` controlled at both endpoints. -/
def sgE (γ : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (1 - γ) * (G θ) ^ 2

/-- `α_n = 1/(n+1) ↓ 0`. -/
def sgAlpha (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- `β_n = π/2 - 1/(n+1) ↑ π/2`. -/
def sgBeta (n : ℕ) : ℝ := Real.pi / 2 - 1 / ((n : ℝ) + 1)

/-- The boundary-error term of the limiting argument. -/
def sgFlux (γ b : ℝ) (G : ℝ → ℝ) (n : ℕ) : ℝ :=
  |sgA γ b (sgBeta n) * (G (sgBeta n)) ^ 2| + |sgA γ b (sgAlpha n) * (G (sgAlpha n)) ^ 2|

/-! ## Elementary pointwise facts -/

theorem sgS_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sgS θ := by
  rw [sgS]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sgS_sq_add_sgC_sq (θ : ℝ) : (sgS θ) ^ 2 + (sgC θ) ^ 2 = 1 := by
  rw [sgS, sgC]
  exact Real.sin_sq_add_cos_sq (2 * θ)

theorem sgW_pos {γ : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sgW γ θ := by
  rw [sgW]
  exact Real.rpow_pos_of_pos (sgS_pos hθ) _

theorem sgW0_pos {γ : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sgW0 γ θ := by
  rw [sgW0]
  exact Real.rpow_pos_of_pos (sgS_pos hθ) _

theorem sgW_nonneg_of_Icc {γ : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ sgW γ θ := by
  rw [sgW]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _

theorem sgW0_nonneg_of_Icc {γ : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ sgW0 γ θ := by
  rw [sgW0]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _

end Work.FTS.GalBasis.cut
