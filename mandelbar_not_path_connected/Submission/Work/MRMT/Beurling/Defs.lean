/-
Work.MRMT — the Beurling transform: definitions.

CONVENTION.  We use the Fourier transform `𝓕` of Mathlib
(`MeasureTheory.Lp.fourierTransformₗᵢ`, the `L²`-normalised version of
`∫ f(x) exp(-2πi ⟪x,ξ⟫) dx`).  The **Beurling transform** is the Fourier multiplier
with symbol

`m(ξ) = ξ̄ / ξ`   (`= exp(-2 i arg ξ)` for `ξ ≠ 0`, and `m(0) = 0`),

i.e. `𝓕 (S f)(ξ) = m(ξ) 𝓕 f (ξ)`.  Equivalently `S` is the singular integral operator
with kernel `-1/(π z²)`.  Note `|m| = 1` a.e., so `S` is an isometry of `L²(ℂ)`.

The symbol is *not* smooth at `0`, so it cannot be used as a multiplier on Schwartz
functions (`SchwartzMap.fourierMultiplierCLM` requires `HasTemperateGrowth`, hence
`C^∞`); consequently the `L²` operator is constructed from the multiplication operator
on `L²` by an a.e. bounded measurable function, conjugated by `𝓕`.
-/
import Submission.Work.MRMT.Basic
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Fourier.LpSpace

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex SchwartzMap Function
open scoped Distributions Topology ENNReal ComplexConjugate

namespace Work.MRMT

/-- The Beurling symbol `ξ̄/ξ`, with the value `0` at the origin. -/
def beurlingSymbol (ξ : ℂ) : ℂ := if ξ = 0 then 0 else conj ξ / ξ

@[simp] theorem beurlingSymbol_zero : beurlingSymbol 0 = 0 := by simp [beurlingSymbol]

theorem beurlingSymbol_of_ne_zero {ξ : ℂ} (hξ : ξ ≠ 0) : beurlingSymbol ξ = conj ξ / ξ := by
  simp [beurlingSymbol, hξ]

/-- The measure of a point of `ℂ` is zero, so `ξ ≠ 0` a.e. -/
theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure ℂ), ξ ≠ 0 := by
  rw [ae_iff]
  have : {x : ℂ | ¬ x ≠ 0} = {0} := by ext x; simp
  rw [this, measure_singleton]

theorem norm_beurlingSymbol_le (ξ : ℂ) : ‖beurlingSymbol ξ‖ ≤ 1 := by
  rw [beurlingSymbol]
  split_ifs with h
  · simp
  · rw [norm_div, norm_conj, div_le_one (norm_pos_iff.mpr h)]

theorem norm_beurlingSymbol_of_ne_zero {ξ : ℂ} (hξ : ξ ≠ 0) : ‖beurlingSymbol ξ‖ = 1 := by
  rw [beurlingSymbol_of_ne_zero hξ, norm_div, norm_conj,
    div_self (norm_ne_zero_iff.mpr hξ)]

theorem beurlingSymbol_ne_zero {ξ : ℂ} (hξ : ξ ≠ 0) : beurlingSymbol ξ ≠ 0 := by
  intro h
  have := norm_beurlingSymbol_of_ne_zero hξ
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-- The symbol is unimodular off the origin. -/
theorem beurlingSymbol_mul_conj {ξ : ℂ} (hξ : ξ ≠ 0) :
    beurlingSymbol ξ * conj (beurlingSymbol ξ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_beurlingSymbol_of_ne_zero hξ,
    one_pow, Complex.ofReal_one]

theorem ae_norm_beurlingSymbol : ∀ᵐ ξ ∂(volume : Measure ℂ), ‖beurlingSymbol ξ‖ = 1 := by
  filter_upwards [ae_ne_zero] with ξ hξ
  exact norm_beurlingSymbol_of_ne_zero hξ

theorem aestronglyMeasurable_beurlingSymbol :
    AEStronglyMeasurable beurlingSymbol (volume : Measure ℂ) := by
  have hmeas : AEStronglyMeasurable (fun ξ : ℂ => conj ξ / ξ) (volume : Measure ℂ) :=
    ((Complex.continuous_conj.measurable).div measurable_id).aestronglyMeasurable
  refine AEStronglyMeasurable.congr hmeas ?_
  filter_upwards [ae_ne_zero] with ξ hξ
  exact (beurlingSymbol_of_ne_zero hξ).symm

end Work.MRMT
