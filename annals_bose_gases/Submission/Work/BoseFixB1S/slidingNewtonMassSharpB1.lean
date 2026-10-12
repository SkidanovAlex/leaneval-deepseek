import ChallengeDeps
import Submission.Work.BoseFixB1S.conv3Small_dev_quadratic
import Submission.Work.BoseFixB1S.conv3chi_dev_quadratic
import Submission.Work.BoseFixB1S.pairW_newtonian_sharp
import Submission.Work.BoseFixB1S.sharpMassAux
import Submission.Work.BoseFixB1S.wSmallScaledComparisonAlt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Sharp sliding Newtonian mass of the `dℓ`-localised two-factor kernel**
(FS `eq:appw1sliding` mass term, sharp form): the momentum-space Newtonian energy of the
`ℓd`-renormalised kernel

    𝒲 = wSmallScaled M (ℓd) (g₀) / convScale ℓ
      = g₀ / ( (χ_M⋆χ_M)(·/(ℓd)) · (χ⋆χ)(·/ℓ) )

is bounded by `2(1 + K((R/ℓ)² + (R/(ℓd))²))·g₀ω₀(0)`, uniformly in the sliding parameters
`ℓ, d` in the dilute regime `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`.  The constant `2` is sharp: as
`ℓ, d → ∞` at fixed `R` the kernel tends to `g₀` and the bound tends to
`(2π)^{-3}∫|ĝ₀|²/p² = 2·g₀ω₀(0)`.

Assembly (`Submission/Work/BoseFixB1S/sharpMassAux.lean`,
`slidingNewtonMassSharp_of_pieces`) from four inputs:

* `conv3chi_dev_quadratic` — the global quadratic deviation `|(χ⋆χ)(t) − 1| ≤ C₁‖t‖²`;
* `conv3Small_dev_quadratic` — the same for the cosine-`M` self-convolution (`M ≥ 1`);
* `wSmallScaled_sharp_comparison_alt` — the sharp a.e. pointwise comparison
  `0 ≤ 𝒲 ≤ (1 + 2C₂/smallConvLower M·(R/(ℓd))² + 2C₁(R/ℓ)²)·g₀`
  (on the support of `g₀` the two denominators are `≥ smallConvLower M` and `≥ 1/2`);
* `pairW_newtonian_sharp` — the position-space Newtonian identity
  `(2π)^{-3}∫(pairW W)²/‖q‖² ≤ (1/4π)∬WW/‖x−y‖` followed by the Newton identity
  `∬g₀g₀/‖x−y‖ = 8π·g₀ω₀(0)` and the comparison `𝒲 ≤ (1+δ)g₀`. -/
theorem slidingNewtonMassSharpB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0),
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.pairW (fun x : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
                / Submission.BoseGases.convScale ℓ x) q) ^ 2 / ‖q‖ ^ 2
        ≤ 2 * (1 + K * ((R / ℓ) ^ 2 + (R / (ℓ * d)) ^ 2))
            * Submission.BoseGases.g0w0Mass (v := v) h :=
  slidingNewtonMassSharp_of_pieces (v := v) (R := R) (M := M) hv_supp hR0 hv hvrad hv1 h hM
    conv3chi_dev_quadratic (conv3Small_dev_quadratic hM)
    (fun {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
        (hC₁ : ∀ t : E3, |Submission.BoseGases.conv3 Submission.BoseGases.chi
          Submission.BoseGases.chi t - 1| ≤ C₁ * ‖t‖ ^ 2)
        (hC₂ : ∀ t : E3, |Submission.BoseGases.conv3Small M t - 1| ≤ C₂ * ‖t‖ ^ 2)
        {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R ≤ ℓ * d / 16)
        (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) =>
      wSmallScaled_sharp_comparison_alt hv_supp hR0 hv hvrad h hM hC₁0 hC₂0 hC₁ hC₂ hℓ hd hR hRχ)
    (fun {δ : ℝ} (hδ : 0 ≤ δ) {W : E3 → ℝ} (hWint : MeasureTheory.Integrable W)
        (hW0 : 0 ≤ᵐ[MeasureTheory.volume] W)
        (hWsupp : ∀ x : E3, R ≤ ‖x‖ → W x = 0)
        (hWle : ∀ᵐ x : E3, W x ≤ (1 + δ) * Submission.BoseGases.g0 v h x) =>
      pairW_newtonian_sharp hR0 hδ hv hvrad hv_supp h hWint hW0 hWsupp hWle)

end Work.BoseFixB1S
