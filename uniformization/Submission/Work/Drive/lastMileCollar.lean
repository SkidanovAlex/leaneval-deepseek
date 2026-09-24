import Mathlib
import Submission.Work.Drive.lastMileTools

/-!
# The collar step of the last mile: certificates from gradient bounds, and Cauchy–Schwarz

Two tools of the *collar* step **(C)** of the last mile:

* `Work.Drive.pairIntegrable_of_gradient_bounds` — the `PairIntegrable` certificates of the energy
  route reduce to *growth bounds on the gradients*: `‖∇f‖ ≤ C/‖z-p‖` (the logarithmic pole) and
  `‖∇χ‖ ≤ K` (smoothness off the pole).  This is the form in which they are discharged for the
  Green functions, using the pole expansion and the smoothness away from the pole.

* `Work.Drive.pairing_mixed_le` — **Cauchy–Schwarz for the whole pairing with a weight family**: if
  the two *diagonal* weighted energies are `A` and `B`, the *mixed* one is bounded by `(A+B)/2`.
  Combined with the level identity `Work.Drive.pairing_comp_eq_weighted` at both poles this gives the
  smallness of the mixed pairing in the collar `{gA < t}`, which is what closes the reciprocity
  argument.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
theorem pairIntegrable_of_gradient_bounds {x : X} {ρ σ : ℝ} {W f χ : X → ℝ} {p : ℂ} {C K : ℝ}
    (hWc : Continuous (clampedPullback x σ W))
    (hWcs : HasCompactSupport (clampedPullback x σ W))
    (hf : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖gradient (clampedPullback x ρ f) z‖ ≤ C / ‖z - p‖)
    (hχ : ∀ᵐ z ∂(volume : Measure ℂ), ‖gradient (clampedPullback x ρ χ) z‖ ≤ K)
    (hmeas : AEStronglyMeasurable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
        (gradient (clampedPullback x ρ χ) z)) volume) :
    PairIntegrable x ρ σ W f χ :=
  pairIntegrable_of_growth hWc hWcs (by
    filter_upwards [hf, hχ] with z h1 h2
    calc ‖inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ χ) z)‖
        ≤ ‖gradient (clampedPullback x ρ f) z‖ * ‖gradient (clampedPullback x ρ χ) z‖ :=
          norm_inner_le_norm _ _
      _ ≤ (C / ‖z - p‖) * K := mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = C * K / ‖z - p‖ := by ring) hmeas

/-- **Cauchy–Schwarz for the pairing with a weight family.** -/
theorem pairing_mixed_le {ι : Type*} [Fintype ι] {y : ι → X} {ρ σ : ι → ℝ} {ψ : ι → X → ℝ}
    {W : ι → X → ℝ} {f g : X → ℝ} {A B : ℝ}
    (hW : ∀ i z, 0 ≤ (ψ i * W i) z)
    (hfg : ∀ i, PairIntegrable (y i) (ρ i) (σ i) (ψ i * W i) f g)
    (hff : ∀ i, PairIntegrable (y i) (ρ i) (σ i) (ψ i * W i) f f)
    (hgg : ∀ i, PairIntegrable (y i) (ρ i) (σ i) (ψ i * W i) g g)
    (hf : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (clampedPullback (y i) (ρ i) f) z)
    (hg : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (clampedPullback (y i) (ρ i) g) z)
    (hA : ∑ i, pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f f = A)
    (hB : ∑ i, pairTerm (y i) (ρ i) (σ i) (ψ i * W i) g g = B) :
    |∑ i, pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f g| ≤ (A + B) / 2 := by
  have h1 : |∑ i, pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f g|
      ≤ ∑ i, |pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f g| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ i, |pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f g|
      ≤ ∑ i, (pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f f
          + pairTerm (y i) (ρ i) (σ i) (ψ i * W i) g g) / 2 :=
    Finset.sum_le_sum fun i _ =>
      pairTerm_abs_le (fun z => hW i z) (hfg i) (hff i) (hgg i) (hf i) (hg i)
  have h3 : ∑ i, (pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f f
        + pairTerm (y i) (ρ i) (σ i) (ψ i * W i) g g) / 2
      = (∑ i, pairTerm (y i) (ρ i) (σ i) (ψ i * W i) f f
        + ∑ i, pairTerm (y i) (ρ i) (σ i) (ψ i * W i) g g) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hA, hB] at h3
  linarith [h1, h2, h3.le, h3.ge]

end Work.Drive
