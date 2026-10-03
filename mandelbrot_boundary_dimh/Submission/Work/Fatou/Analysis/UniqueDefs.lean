import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Constructed
import Submission.Work.Fatou.Setup
import Submission.Work.FatouCH.uniqueSetup

/-!
# Fatou uniqueness from the constructed coordinate: setup

Definitions shared by `Work.Fatou.Analysis.fatouUniqueOfConstructed` and its helper lemmas.

`Work.Fatou.FatouConstructed` produces, for every admissible region `Qreg b₁ b₂` and every
near-translation `F` on it, a Fatou coordinate `Φ₀` together with two extra properties:

* `SurjMod b₁ b₂ Φ₀` — `Φ₀` hits every class modulo `ℤ` (Shishikura A.2.3);
* `OrbitRel b₁ b₂ F Φ₀` — the orbit relation A.2.1(i) *for `Φ₀` itself*: if
  `Φ₀ z' = Φ₀ z + k` (`k : ℕ`) then `z' = F^[k] z` and all intermediate iterates lie in the
  region.

These are exactly the hypotheses consumed by the uniqueness argument below.  We also record
`DerivEst`, the single-point form (the `C₂` half) of Shishikura's Lemma A.2.4(i), which is what
the uniqueness proof uses to compare the derivatives of two Fatou coordinates deep inside the
region.
-/

set_option linter.unusedVariables false

namespace Work.Fatou.Analysis

open MandelDim

noncomputable section

/-- The orbit relation A.2.1(i) for a fixed coordinate `Φ₀` on `Qreg b₁ b₂`. -/
def OrbitRel (b₁ b₂ : Option ℂ) (F Φ₀ : ℂ → ℂ) : Prop :=
  ∀ z ∈ MandelDim.Qreg b₁ b₂, ∀ z' ∈ MandelDim.Qreg b₁ b₂, ∀ k : ℕ,
    Φ₀ z' = Φ₀ z + (k : ℂ) →
      (∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂) ∧ F^[k] z = z'

/-- Surjectivity modulo `ℤ` (A.2.3): every `w : ℂ` is `Φ₀ z - n` for some `z` in the region and
some `n : ℤ`. -/
def SurjMod (b₁ b₂ : Option ℂ) (Φ₀ : ℂ → ℂ) : Prop :=
  ∀ w : ℂ, ∃ z ∈ MandelDim.Qreg b₁ b₂, ∃ n : ℤ, Φ₀ z = w + n

/-- The single-point `C₂` form of Lemma A.2.4(i) with fixed constants: on a ball of radius
`R ≥ R₁` inside the region, `deriv Φ` is within `C₂ / R` of `1 / v`. -/
def DerivEst (R₁ C₁ C₂ : ℝ) (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) : Prop :=
  R₁ ≤ R → DifferentiableOn ℂ Φ (Metric.ball z₀ R) → Set.InjOn Φ (Metric.ball z₀ R) →
    DifferentiableOn ℂ v (Metric.ball z₀ R) →
    (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
    (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
    ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R

/-- Unfolding `MandelDim.FatouDerivEstimate` into `DerivEst` with explicit constants. -/
theorem exists_derivEst_of_fatouDerivEstimate (h : MandelDim.FatouDerivEstimate) :
    ∃ R₁ C₁ C₂ : ℝ, 0 < R₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), DerivEst R₁ C₁ C₂ Φ v z₀ R := by
  obtain ⟨R₁, C₁, C₂, h1, h2, h3, h4⟩ := h
  exact ⟨R₁, C₁, C₂, h1, h2, h3, fun Φ v z₀ R hR hd hinj hvd hv hab =>
    (h4 Φ v z₀ R hR hd hinj hvd hv hab).2⟩

end

end Work.Fatou.Analysis
