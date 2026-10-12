import Mathlib.Algebra.Order.Star.Real
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-217 — the 𝒯_B kinetic layer, Step-0: the spectral coefficient core

(Work-in-progress module.  Per SmallBoxDesignNote Sessions 215–216, FS's
sharp Bogolubov bound lives in the renormalized small-box kinetic (eq:appTB)

    𝒯_B = ½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q_B + Q_Bχ_B[√−Δ−(dsℓ)⁻¹]₊⁻²χ_BQ_B

whose `[√−Δ−c]₊⁻²`-spectral factor the corpus does not yet name.  Defining
that factor as an OPERATOR requires the spectral theorem for `√−Δ` with a
positive-part functional calculus — infra the corpus does not have.  But in
EVERY analytic use (the Bogolubov derivation, eq:simpleaprioribog/refined,
the `A(p) = |B|/(n+1)·[|p|−(dsℓ)⁻¹]²₊`-coefficients of `lm:appbogolubov`)
the spectral factor enters ONLY through its well-defined momentum-space
content — the coefficient `[|p| − c]₊²` (the SQUARE of the positive part,
`p ↦ (max ‖p‖ c 0)²`-type) and the full-space convolution-kernel/quadratic
form built on it.  This module lays down that honest, well-defined core:

  * `fsKinCoeff c r := (max (r - c) 0) ^ 2` — the `[r−c]₊²` coefficient
    (radial in the momentum magnitude `r := ‖p‖`; `c := (dsℓ)⁻¹` > 0);
  * hygiene lemmas (sorry-free, immediately formal): nonnegativity,
    vanishing below `c`, the square-form on `r > c`, monotonicity;
  * the module doc records the next infra step: the box-momentum
    representation (a Fourier basis on the centred box with the `χ_B`
    localizers) on which the kinetic word
    `𝒯_B(Φ) := (kinetic-gap part) + Σᵢ⟨QᵢΦ, χ·[√−Δ−c]₊⁻²·χ·QᵢΦ⟩` becomes
    the `∫ |B(p)|²/…`-quadratic form that `bogolubov_sharp_bound_target`
    (SmallBoxBogolubovTarget) consumes — the next module after this one.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Real

namespace Submission.BoseGases

/-- **the FS `[r−c]₊²`-spectral coefficient**: `r ↦ (max (r−c) 0)²` — the
well-defined momentum-space content of the `[√−Δ−c]₊⁻²`-factor that every
Bogolubov estimate uses (`r := ‖p‖`, `c := (dsℓ)⁻¹`). -/
def fsKinCoeff (c r : ℝ) : ℝ :=
  (max (r - c) 0) ^ 2

/-- nonnegativity: `0 ≤ [r−c]₊²`. -/
lemma fsKinCoeff_nonneg (c r : ℝ) : 0 ≤ fsKinCoeff c r := by
  exact sq_nonneg (max (r - c) 0)

/-- the coefficient vanishes where `r ≤ c`: `[r−c]₊² = 0`. -/
lemma fsKinCoeff_of_le {c r : ℝ} (hr : r ≤ c) : fsKinCoeff c r = 0 := by
  dsimp [fsKinCoeff]
  have hmax : max (r - c) 0 = 0 := by
    exact max_eq_right (by nlinarith)
  rw [hmax]
  norm_num

/-- the square form on `c < r`: `[r−c]₊² = (r−c)²`. -/
lemma fsKinCoeff_of_lt {c r : ℝ} (hc : 0 ≤ c) (hr : c < r) : fsKinCoeff c r = (r - c) ^ 2 := by
  dsimp [fsKinCoeff]
  have hmax : max (r - c) 0 = r - c := by
    exact max_eq_left (by nlinarith)
  rw [hmax]

/-- monotone in `r` from `r ≥ c` on: `c ≤ r ≤ r'` ⟹ `[r−c]₊² ≤ [r′−c]₊²`
(the coefficient grows like the square of the excess over `c`). -/
lemma fsKinCoeff_mono {c r r' : ℝ} (hrc : c ≤ r) (hrr : r ≤ r') :
    fsKinCoeff c r ≤ fsKinCoeff c r' := by
  dsimp [fsKinCoeff]
  have h1 : 0 ≤ r - c := by linarith
  have h2 : 0 ≤ r' - c := by linarith
  have h3 : r - c ≤ r' - c := by linarith
  have hm1 : max (r - c) 0 = r - c := max_eq_left h1
  have hm2 : max (r' - c) 0 = r' - c := max_eq_left h2
  rw [hm1, hm2]
  exact sq_le_sq.mpr (by rw [abs_of_nonneg h1, abs_of_nonneg h2]; exact h3)

end Submission.BoseGases
