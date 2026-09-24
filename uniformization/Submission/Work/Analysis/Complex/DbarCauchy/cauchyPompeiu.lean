import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero
import Submission.Work.Analysis.Complex.DbarCauchy.integral_comp_normSq

/-!
# The Cauchy–Pompeiu key identity

For `φ : ℂ → ℂ` of class `C²` with compact support,
`∫ η, ((∂̄φ)(η) - (∂̄φ)(0) · cut η)/η = -2π φ(0)`.

The proof regularizes the singularity at `η = 0` with the radial cutoff `cutChi δ`, which is `0` on
the ball of radius `δ/√2` and `1` outside the ball of radius `δ`; the identity
`∫ ∂̄G = 0` for compactly supported `G` (`integral_dbar_eq_zero`) converts the regularized integral
into `-∫ (∂̄ cutChi δ) φ / η`, whose limit `δ → 0⁺` is evaluated with the radial integration formula
`integral_comp_normSq`.
-/

open MeasureTheory
open scoped Topology

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- The radial profile `σ ↦ smoothTransition (2σ/δ² - 1)` of the cutoff of radius `δ`. -/
def cutProf (δ : ℝ) (σ : ℝ) : ℝ := Real.smoothTransition (2 * σ / δ ^ 2 - 1)

/-- The cutoff of radius `δ`: `0` on the ball of radius `δ/√2` and `1` outside the ball of
radius `δ`. -/
def cutChi (δ : ℝ) (η : ℂ) : ℂ := ((cutProf δ (‖η‖ ^ 2) : ℝ) : ℂ)

theorem cutProf_eq_zero {δ : ℝ} (hδ : 0 < δ) {σ : ℝ} (hσ : σ ≤ δ ^ 2 / 2) : cutProf δ σ = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h1 : 2 * σ / δ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  linarith

theorem cutProf_eq_one {δ : ℝ} (hδ : 0 < δ) {σ : ℝ} (hσ : δ ^ 2 ≤ σ) : cutProf δ σ = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have h1 : 1 ≤ 2 * σ / δ ^ 2 - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    linarith
  linarith

theorem cutChi_eq (δ : ℝ) (η : ℂ) : cutChi δ η = ((cutProf δ (‖η‖ ^ 2) : ℝ) : ℂ) := rfl

theorem contDiff_cutChi (δ : ℝ) (n : ℕ∞) : ContDiff ℝ ((n : WithTop ℕ∞)) (cutChi δ) := by
  have h1 : ContDiff ℝ n (fun η : ℂ => ‖η‖ ^ 2) := contDiff_norm_sq (𝕜 := ℝ)
  have h2 : ContDiff ℝ n (fun η : ℂ => 2 * (‖η‖ ^ 2) / δ ^ 2 - 1) :=
    ContDiff.sub ((contDiff_const.mul h1).div_const (δ ^ 2)) contDiff_const
  have h3 : ContDiff ℝ n (fun η : ℂ => cutProf δ (‖η‖ ^ 2)) := by
    have : (fun η : ℂ => cutProf δ (‖η‖ ^ 2)) = fun η : ℂ => Real.smoothTransition (2 * ‖η‖ ^ 2 / δ ^ 2 - 1) := rfl
    rw [this]
    exact Real.smoothTransition.contDiff.comp h2
  exact ContDiff.comp Complex.ofRealCLM.contDiff h3

/-- The `∂̄` of the cutoff of radius `δ`, divided by `η`. -/
theorem dbar_cutChi_div (δ : ℝ) (hδ : 0 < δ) {η : ℂ} (hη : η ≠ 0) :
    dbar (cutChi δ) η / η = 2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ) := by
  have hderiv : ∀ σ : ℝ, HasDerivAt (cutProf δ) (deriv (cutProf δ) σ) σ := by
    intro σ
    have hd : Differentiable ℝ (cutProf δ) := by
      have h1 : Differentiable ℝ (fun σ : ℝ => 2 * σ / δ ^ 2 - 1) :=
        ((differentiable_id.const_mul 2).div_const (δ ^ 2)).sub_const 1
      exact ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).comp h1
    exact (hd σ).hasDerivAt
  change dbar (fun w : ℂ => ((cutProf δ (‖w‖ ^ 2) : ℝ) : ℂ)) η / η
    = 2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)
  rw [dbar_radialC (cutProf δ) (deriv (cutProf δ)) hderiv η]
  field_simp

/-!
## Status

The cutoff family `cutChi δ` (together with its profile lemmas, smoothness, and the explicit
formula for `∂̄ (cutChi δ) / η`) is set up here.  The remaining steps of the Cauchy–Pompeiu key
identity `∫ η, ((∂̄φ)(η) - (∂̄φ)(0) · cut η)/η = -2π φ(0)` are:

1. `∫ η, cutChi δ η · ((∂̄φ η)/η) = -∫ η, (∂̄ (cutChi δ) η) · (φ η/η)` for `φ` of class `C²` with
   compact support: apply `integral_dbar_eq_zero` to the `C¹`-with-compact-support function
   `η ↦ cutChi δ η · φ η/η` (which vanishes identically on the ball of radius `δ/√2`) and expand
   `∂̄` of the product with `dbar_mul`, `dbar_inv`;
2. `Filter.Tendsto (fun δ => ∫ η, cutChi δ η · ((∂̄φ η)/η)) (𝓝[>] 0) ...`: this equals
   `∫ η, ((∂̄φ)(η) - (∂̄φ)(0) · cut η)/η` in the limit, since `∫ η, cutChi δ η · cut η/η = 0` by
   oddness and `cutChi δ → 1` pointwise;
3. `∫ η, (∂̄ (cutChi δ) η) · (φ η/η) → 2π φ(0)` as `δ → 0⁺`: here `(∂̄ (cutChi δ) η)/η =
   2 · deriv (cutProf δ) (‖η‖²)` (`dbar_cutChi_div`) and the radial integration formula
   `integral_comp_normSq` reduces the limit to
   `2π ∫_0^∞ deriv (cutProf δ) = 2π (cutProf δ ∞ - cutProf δ 0) = 2π`.
-/

end Work.Analysis.Complex.DbarCauchy

end
