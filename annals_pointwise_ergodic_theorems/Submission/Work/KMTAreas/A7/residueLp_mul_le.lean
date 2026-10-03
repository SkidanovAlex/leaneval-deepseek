/-
# The `ℓ^p`-Hölder inequality for the residue average of a bilinear form

This module proves `Work.KMTAreas.A7.residueLp_mul_le`, the estimate

  `‖q⁻¹ ∑_{n₀<q} U x n₀ · V x n₀‖_{ℓ^r(ℤ)}
      ≤ ‖residueLp p₁ q U‖_{ℓ^{p₁}(ℤ)} · ‖residueLp p₂ q V‖_{ℓ^{p₂}(ℤ)}`

where `r = (p₁⁻¹ + p₂⁻¹)⁻¹` and `residueLp p q W x = ((q)⁻¹ ∑_{n₀<q} W x n₀ ^ p) ^ (1/p)`
(`Work.KMTAreas.A7.LargeInterface`).  It is the "linearisation" step used to bound the twisted
bilinear multiplier of the paper's §8 by the norms of its two fibers.

The proof is the product of two Hölder inequalities, exactly matching the two sums involved:

* **in the residue variable** (`Work.KMTAreas.A7.residueSum_mul_le`, the pointwise inequality): for
  each fixed `x`,
  `q⁻¹ ∑_{n₀<q} u_{n₀} v_{n₀} ≤ (q⁻¹ ∑_{n₀<q} u_{n₀}^{p₁})^{1/p₁} (q⁻¹ ∑_{n₀<q} v_{n₀}^{p₂})^{1/p₂}`,
  which is Hölder for the uniform probability measure on `{0,…,q-1}` with the "spare" exponent
  coming from `p₁⁻¹ + p₂⁻¹ ≤ 1` (reduce to the conjugate case with `p₁` and its conjugate, then
  use the monotonicity of `ℓˢ` sums in `s`);
* **in the `ℤ` variable**: `‖A · B‖_{ℓ^r} ≤ ‖A‖_{ℓ^{p₁}} ‖B‖_{ℓ^{p₂}}` whenever
  `r⁻¹ = p₁⁻¹ + p₂⁻¹` — Hölder for `ℝ≥0∞`-valued functions, which is
  `Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm` (all functions on `ℤ` are
  measurable for the counting measure).

Putting the two together with `eLpNorm_mono_enorm` gives the claim.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.KMTAreas.A7.residueSum_mul_le
import Submission.Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory ENNReal
open scoped BigOperators ENNReal

theorem residueLp_mul_le (q : ℕ) (p₁ p₂ : ENNReal) (hp₁ : 1 < p₁) (hp₂ : 1 < p₂)
    (h₁top : p₁ < ⊤) (h₂top : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) (U V : ℤ → ℕ → ENNReal) :
    MeasureTheory.eLpNorm
        (fun x : ℤ => (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, U x n₀ * V x n₀)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (Work.KMTAreas.A7.residueLp p₁.toReal q U) p₁
          MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm (Work.KMTAreas.A7.residueLp p₂.toReal q V) p₂
          MeasureTheory.Measure.count := by
  have hp₁0 : p₁ ≠ 0 := (lt_trans zero_lt_one hp₁).ne'
  have hp₂0 : p₂ ≠ 0 := (lt_trans zero_lt_one hp₂).ne'
  -- the real exponents and the hypothesis `p₁⁻¹ + p₂⁻¹ ≤ 1` transported to `ℝ`
  have hlt₁ : (1 : ℝ) < p₁.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by simp) h₁top.ne).mpr hp₁
  have hlt₂ : (1 : ℝ) < p₂.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by simp) h₂top.ne).mpr hp₂
  have hsumR : (p₁.toReal)⁻¹ + (p₂.toReal)⁻¹ ≤ 1 := by
    have h := ENNReal.toReal_mono (show (1 : ENNReal) ≠ ⊤ by norm_num) hsum
    rwa [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp₁0) (ENNReal.inv_ne_top.mpr hp₂0),
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h
  -- the pointwise Hölder inequality in the residue variable
  have hpt : ∀ x : ℤ, (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, U x n₀ * V x n₀
      ≤ residueLp p₁.toReal q U x * residueLp p₂.toReal q V x := by
    intro x
    have h := residueSum_mul_le q p₁.toReal p₂.toReal hlt₁ hlt₂ hsumR
      (fun n => U x n) (fun n => V x n)
    rw [show ((q : ENNReal)⁻¹ * ∑ n ∈ Finset.range q, U x n ^ p₁.toReal) ^ (1 / p₁.toReal)
          = residueLp p₁.toReal q U x from by
            rw [residueLp, ← ENNReal.rpow_neg_one]; rfl,
        show ((q : ENNReal)⁻¹ * ∑ n ∈ Finset.range q, V x n ^ p₂.toReal) ^ (1 / p₂.toReal)
          = residueLp p₂.toReal q V x from by
            rw [residueLp, ← ENNReal.rpow_neg_one]; rfl] at h
    exact h
  calc MeasureTheory.eLpNorm
        (fun x : ℤ => (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, U x n₀ * V x n₀)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm
          (fun x : ℤ => residueLp p₁.toReal q U x * residueLp p₂.toReal q V x)
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count := by
        refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
        simpa [enorm_eq_self, Pi.mul_apply] using hpt x
    _ ≤ MeasureTheory.eLpNorm (residueLp p₁.toReal q U) p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm (residueLp p₂.toReal q V) p₂ MeasureTheory.Measure.count :=
        Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm
          (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (q := p₁) (r := p₂) (inv_inv _)
          (Measurable.of_discrete.aemeasurable) (Measurable.of_discrete.aemeasurable)

end Work.KMTAreas.A7
