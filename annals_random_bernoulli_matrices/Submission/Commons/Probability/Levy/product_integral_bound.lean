import Mathlib
import Submission.Commons.Probability.Levy.product_integral_core_r1
import Submission.Commons.Probability.Levy.product_integral_bound_of_r1_core

open MeasureTheory
open scoped ENNReal BigOperators

/-!
# `Commons.Probability.Levy.product_integral_bound`

The Esséen-type product bound: for probability measures `μ i` with Lévy concentration deficits
`δᵢ = 1 − Qᵢ(ρᵢ)` at radii `0 < ρᵢ ≤ r` and `D = Σ δᵢ ρᵢ² > 0`, the integral of the product
of the characteristic-function moduli over `[−1/r, 1/r]` is `O(1/√D)`.

## Proof structure (assembly)

* `Commons.Probability.Levy.product_integral_core_r1` — the dimensionless (`r = 1`, `ρᵢ ≤ 1`)
  core, proved from the per-variable level-set bound
  (`essen_level_set_bound`), the joint-sublevel ("overlap") bound
  (`product_overlap_bound`), the exp-multiplicative bound
  `∏‖φᵢ‖ ≤ exp(−½ Σ (1−‖φᵢ‖²))` and the layer-cake integral.
* `Commons.Probability.Levy.product_integral_bound_of_r1_core` — the scaling step: it shows that
  the `r = 1` core (with constant `C`) implies the general statement, by rescaling each `μ i`
  by `x ↦ x / r` (which preserves the deficits and turns `∫_{−1/r}^{1/r}∏‖φ_μ(t)‖ dt` into
  `r⁻¹ ∫_{−1}^{1} ∏‖φ_ν(s)‖ ds`).

All four ingredients were proved by colleagues and committed to the shared commons; this file
only glues them together.
-/

namespace Commons.Probability.Levy

lemma product_integral_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (μ : Fin m → Measure ℝ) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
        (r : ℝ), 0 < r → (ρ : Fin m → ℝ) → (∀ i : Fin m, 0 < ρ i) →
        (∀ i : Fin m, ρ i ≤ r) →
        (0 < ∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
            * (ρ i) ^ 2) →
        (∫ t in (-(1 / r))..(1 / r), ∏ i : Fin m, ‖charFun (μ i) t‖) ≤
          C / Real.sqrt (∑ i : Fin m,
            (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
              * (ρ i) ^ 2) := by
  rcases product_integral_core_r1 with ⟨C, hC, hcore⟩
  exact ⟨C, hC, product_integral_bound_of_r1_core C hC hcore⟩

end Commons.Probability.Levy
