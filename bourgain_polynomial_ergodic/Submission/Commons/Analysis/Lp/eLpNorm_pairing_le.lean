import Mathlib.Analysis.CStarAlgebra.Module.Constructions

namespace Commons.Analysis.Lp

open MeasureTheory ENNReal

/-- Hölder's inequality for the pairing of two functions with values in a complex inner product
space: `‖∫ x, ⟪u x, v x⟫‖ ≤ ‖u‖_p * ‖v‖_q` for conjugate exponents `p`, `q`. -/
theorem eLpNorm_pairing_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {u v : ℝ → H} {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) (hu : MeasureTheory.AEStronglyMeasurable u MeasureTheory.volume) (hv : MeasureTheory.AEStronglyMeasurable v MeasureTheory.volume) : enorm (∫ x : ℝ, inner ℂ (u x) (v x)) ≤ MeasureTheory.eLpNorm u (ENNReal.ofReal p) * MeasureTheory.eLpNorm v (ENNReal.ofReal q) := by
  have hp_pos : 0 < p := by linarith
  have hq_pos : 0 < q := by linarith
  have hpqH : Real.HolderConjugate p q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa [one_div] using hpq⟩
  have hmu : AEMeasurable (fun x : ℝ => ‖u x‖ₑ) volume := by
    simpa only [enorm_eq_nnnorm] using (hu.nnnorm.aemeasurable).coe_nnreal_ennreal
  have hmv : AEMeasurable (fun x : ℝ => ‖v x‖ₑ) volume := by
    simpa only [enorm_eq_nnnorm] using (hv.nnnorm.aemeasurable).coe_nnreal_ennreal
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp_pos
  have hq_ne_zero : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq_pos
  have hp_ne_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq_ne_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have heq_u : eLpNorm u (ENNReal.ofReal p) = (∫⁻ x : ℝ, ‖u x‖ₑ ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := u) (μ := volume) hp_ne_zero hp_ne_top hu,
        ENNReal.toReal_ofReal hp_pos.le]
  have heq_v : eLpNorm v (ENNReal.ofReal q) = (∫⁻ x : ℝ, ‖v x‖ₑ ^ q) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := v) (μ := volume) hq_ne_zero hq_ne_top hv,
        ENNReal.toReal_ofReal hq_pos.le]
  have hinner : ∀ x : ℝ, ‖inner ℂ (u x) (v x)‖ₑ ≤ ‖u x‖ₑ * ‖v x‖ₑ := fun x => by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr (nnnorm_inner_le_nnnorm (u x) (v x))
  have h1 : enorm (∫ x : ℝ, inner ℂ (u x) (v x)) ≤ ∫⁻ x : ℝ, ‖inner ℂ (u x) (v x)‖ₑ :=
    enorm_integral_le_lintegral_enorm (μ := volume) (fun x : ℝ => inner ℂ (u x) (v x))
  have h2 : (∫⁻ x : ℝ, ‖inner ℂ (u x) (v x)‖ₑ) ≤ ∫⁻ x : ℝ, ‖u x‖ₑ * ‖v x‖ₑ :=
    lintegral_mono hinner
  have h3 : (∫⁻ x : ℝ, ‖u x‖ₑ * ‖v x‖ₑ) ≤
      (∫⁻ x : ℝ, ‖u x‖ₑ ^ p) ^ (1 / p) * (∫⁻ x : ℝ, ‖v x‖ₑ ^ q) ^ (1 / q) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := volume) hpqH hmu hmv
  refine le_trans h1 (le_trans h2 (le_trans h3 (le_of_eq ?_)))
  rw [heq_u, heq_v]

end Commons.Analysis.Lp