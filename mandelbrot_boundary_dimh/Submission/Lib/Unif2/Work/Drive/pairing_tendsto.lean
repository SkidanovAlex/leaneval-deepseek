import Mathlib
import Submission.Lib.Unif2.Work.Drive.energyGreenRung

/-!
# Limits and monotonicity for the Dirichlet pairing term

Two tools that the "last mile" of the energy route to the symmetry of the Green function (and the
two-pole flux identity `Work.Drive.pairFlux_twoPole_cancel`) need:

* `Work.Drive.pairTerm_tendsto_of_dominated` — dominated convergence for the pairing in its
  *test-function* slot: if the gradients of the clamped pullbacks of `χ n` converge pointwise a.e. to
  that of `χlim` and the integrands are dominated by an integrable `g`, then
  `pairTerm … f (χ n) → pairTerm … f χlim`.  This is the "gap" of the energy route: it turns the pole
  identity `pairing … gA Ψ = 2π Ψ a` (proved for smooth test functions) into its limiting form, and
  lets the level-set cutoffs tend to `1`.

* `Work.Drive.pairTerm_mono_in_weight` — the pairing term is monotone in its weight, and homogeneous
  under rescaling: if `0 ≤ W₁ ≤ c W₂` pointwise then `pairTerm W₁ f f ≤ c · pairTerm W₂ f f`.  This is
  what turns the pointwise smallness of `gB` on the collar `{gA < t}`
  (`Work.Kernel.sup_lt_of_level_lt`) into the smallness of the *collar pairing*.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Dominated convergence for the Dirichlet pairing term** (second slot). -/
theorem pairTerm_tendsto_of_dominated {x : X} {ρ σ : ℝ} {W f χlim : X → ℝ}
    {χ : ℕ → X → ℝ} {g : ℂ → ℝ}
    (hgrad : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => gradient (clampedPullback x ρ (χ n)) z) atTop
        (𝓝 (gradient (clampedPullback x ρ χlim) z)))
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : ℂ => clampedPullback x σ W z *
      inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ (χ n)) z)) (volume : Measure ℂ))
    (hdom : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖clampedPullback x σ W z * inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ (χ n)) z)‖ ≤ g z)
    (hint : Integrable g) :
    Tendsto (fun n => pairTerm x ρ σ W f (χ n)) atTop (𝓝 (pairTerm x ρ σ W f χlim)) := by
  rw [pairTerm]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence g hmeas hint hdom ?_
  filter_upwards [hgrad] with z hz
  exact tendsto_const_nhds.mul (tendsto_const_nhds.inner hz)

/-- **Monotonicity and homogeneity of the pairing term in its weight.** -/
theorem pairTerm_mono_in_weight {x : X} {ρ σ : ℝ} {W₁ W₂ f : X → ℝ} {c : ℝ}
    (h0 : ∀ z : ℂ, 0 ≤ clampedPullback x σ W₁ z)
    (h : ∀ z : ℂ, clampedPullback x σ W₁ z ≤ c * clampedPullback x σ W₂ z)
    (hi₁ : PairIntegrable x ρ σ W₁ f f) (hi₂ : PairIntegrable x ρ σ W₂ f f) :
    pairTerm x ρ σ W₁ f f ≤ c * pairTerm x ρ σ W₂ f f := by
  rw [pairTerm, pairTerm, ← integral_const_mul]
  refine integral_mono_ae hi₁ (hi₂.const_mul c) ?_
  filter_upwards with z
  have hnn : 0 ≤ inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
      (gradient (clampedPullback x ρ f) z) := real_inner_self_nonneg
  calc clampedPullback x σ W₁ z * inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ f) z)
      ≤ (c * clampedPullback x σ W₂ z) * inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ f) z) :=
        mul_le_mul_of_nonneg_right (h z) hnn
    _ = c * (clampedPullback x σ W₂ z * inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ f) z)) := by ring

end Work.Drive
