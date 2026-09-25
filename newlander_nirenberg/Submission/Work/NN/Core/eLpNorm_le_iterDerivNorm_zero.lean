import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.volume_polydisc

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace Work.NN.Core

/-- **`L²` is controlled by the `C⁰`-norm.**  On a polydisc `polydisc 0 ρ` with positive radii
there is a constant `V > 0` such that for every a.e. strongly measurable `f : ℂⁿ → ℂ`
    `‖f‖_{L²(polydisc)} ≤ V · sup_{z ∈ polydisc} ‖f z‖`,
where the supremum is the `i = 0` iterated-derivative norm `iterDerivNorm 0 f (polydisc 0 ρ)`
(taken over the polydisc itself).  The constant can be taken to be
`√(π^n ∏ ρ_j²) + 1 = (volume (polydisc 0 ρ))^{1/2} + 1`.

Proof: `eLpNorm_le_of_ae_enorm_bound` bounds the `L²`-seminorm by
`(sup ‖f‖) · (μ univ)^{1/2}`, and `μ univ = volume (polydisc 0 ρ)` is the finite product
`∏_j π ρ_j²` (`volume_polydisc`). -/
lemma eLpNorm_le_iterDerivNorm_zero {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ V : ℝ, 0 < V ∧ ∀ (f : Work.NN.Core.Cn n → ℂ),
      MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ)) →
      MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))
        ≤ ENNReal.ofReal V * Work.CR.Flat.iterDerivNorm 0 f (Work.CR.Flat.polydisc 0 ρ) := by
  refine ⟨Real.sqrt (∏ j : Fin n, Real.pi * ρ j ^ 2) + 1, ?_, ?_⟩
  · have h0 : (0:ℝ) ≤ Real.sqrt (∏ j : Fin n, Real.pi * ρ j ^ 2) := Real.sqrt_nonneg _
    linarith
  · intro f hf
    set P := Work.CR.Flat.polydisc 0 ρ with hP
    set μ : MeasureTheory.Measure (Work.NN.Core.Cn n) := MeasureTheory.volume.restrict P with hμ
    set C : ℝ≥0∞ := Work.CR.Flat.iterDerivNorm 0 f P with hC
    have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 ρ
    -- `‖f z‖ ≤ C` for a.e. `z`: the polydisc has full `μ`-measure and `iterDerivNorm 0` is the
    -- supremum of `‖f z‖` over the polydisc.
    have hbd : ∀ᵐ z ∂μ, ‖f z‖ₑ ≤ C := by
      rw [hμ, MeasureTheory.ae_restrict_iff' hPopen.measurableSet]
      filter_upwards with z hz
      have h1 := Work.CR.Flat.le_iterDerivNorm 0 f P hz
      rw [norm_iteratedFDerivWithin_zero] at h1
      simpa [hC] using h1
    -- `L²`-bound by the pointwise bound times the `(1/2)`-power of the total mass.
    have hmain := MeasureTheory.eLpNorm_le_of_ae_enorm_bound (p := 2) hf hbd
    have hpow : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
    -- The total mass is the volume of the polydisc, hence the finite product `∏_j π ρ_j²`.
    have hvol : μ Set.univ = ENNReal.ofReal (∏ j : Fin n, Real.pi * ρ j ^ 2) := by
      rw [hμ, MeasureTheory.Measure.restrict_apply_univ, hP, Work.NN.Core.volume_polydisc]
      rw [show (∏ j : Fin n, ENNReal.ofReal (ρ j) ^ 2 * ENNReal.ofReal Real.pi)
          = ∏ j : Fin n, ENNReal.ofReal (Real.pi * ρ j ^ 2) from
        Finset.prod_congr rfl fun j _ => by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (le_of_lt (hρ j))]
          ring]
      exact (ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
        (f := fun j : Fin n => Real.pi * ρ j ^ 2) (fun j _ => by positivity)).symm
    have hsqrt : (μ Set.univ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (Real.sqrt (∏ j : Fin n, Real.pi * ρ j ^ 2) + 1) := by
      rw [hvol, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1/2),
        Real.sqrt_eq_rpow]
      exact ENNReal.ofReal_le_ofReal
        (by linarith [Real.sqrt_nonneg (∏ j : Fin n, Real.pi * ρ j ^ 2)])
    calc MeasureTheory.eLpNorm f 2 μ
        ≤ C • (μ Set.univ) ^ (2 : ℝ≥0∞).toReal⁻¹ := hmain
      _ = C * (μ Set.univ) ^ (1/2 : ℝ) := by rw [hpow, smul_eq_mul]
      _ ≤ C * ENNReal.ofReal (Real.sqrt (∏ j : Fin n, Real.pi * ρ j ^ 2) + 1) :=
            mul_le_mul_right hsqrt C
      _ = ENNReal.ofReal (Real.sqrt (∏ j : Fin n, Real.pi * ρ j ^ 2) + 1) * C := mul_comm _ _

end Work.NN.Core
