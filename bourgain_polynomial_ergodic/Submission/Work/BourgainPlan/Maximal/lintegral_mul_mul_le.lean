import Mathlib

namespace Work.BourgainPlan.Maximal

open MeasureTheory

/-- Three-function Hölder (generalized Hölder with exponents `p`, `p`, `p/(p-2)`), for `p > 2`.
The exponents sum to one: `1/p + 1/p + (p-2)/p = 1`. -/
theorem lintegral_mul_mul_le {p : ℝ} (hp : 2 < p) {a b c : ℝ → ENNReal}
    (ha : AEMeasurable a) (hb : AEMeasurable b) (hc : AEMeasurable c) :
    ∫⁻ x, a x * b x * c x
      ≤ (∫⁻ x, a x ^ p) ^ (1 / p) * (∫⁻ x, b x ^ p) ^ (1 / p)
        * (∫⁻ x, c x ^ (p / (p - 2))) ^ ((p - 2) / p) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  set f : Fin 3 → ℝ → ENNReal :=
    ![fun x => a x ^ p, fun x => b x ^ p, fun x => c x ^ (p / (p - 2))] with hf
  set P : Fin 3 → ℝ := ![1 / p, 1 / p, (p - 2) / p] with hP
  have hpt : ∀ x, ∏ i : Fin 3, f i x ^ P i = a x * b x * c x := by
    intro x
    have hpa : (a x ^ p) ^ p⁻¹ = a x := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (ne_of_gt hp0), ENNReal.rpow_one]
    have hpb : (b x ^ p) ^ p⁻¹ = b x := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (ne_of_gt hp0), ENNReal.rpow_one]
    have hpc : (c x ^ (p / (p - 2))) ^ ((p - 2) / p) = c x := by
      rw [← ENNReal.rpow_mul]
      have hexp : p / (p - 2) * ((p - 2) / p) = 1 := by field_simp
      rw [hexp, ENNReal.rpow_one]
    rw [Fin.prod_univ_three]
    simp only [hf, hP]
    simp
    rw [hpa, hpb, hpc]
  have hR : ∏ i : Fin 3, (∫⁻ x, f i x) ^ P i
      = (∫⁻ x, a x ^ p) ^ (1 / p) * (∫⁻ x, b x ^ p) ^ (1 / p)
        * (∫⁻ x, c x ^ (p / (p - 2))) ^ ((p - 2) / p) := by
    rw [Fin.prod_univ_three]
    simp only [hf, hP]
    simp
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := volume) (Finset.univ : Finset (Fin 3))
      (f := f) (p := P) ?_ ?_ ?_
  · calc ∫⁻ x, a x * b x * c x
        = ∫⁻ x, ∏ i : Fin 3, f i x ^ P i := (lintegral_congr hpt).symm
      _ ≤ ∏ i : Fin 3, (∫⁻ x, f i x) ^ P i := key
      _ = (∫⁻ x, a x ^ p) ^ (1 / p) * (∫⁻ x, b x ^ p) ^ (1 / p)
            * (∫⁻ x, c x ^ (p / (p - 2))) ^ ((p - 2) / p) := hR
  · intro i _
    fin_cases i
    · simpa [hf] using ha.pow_const p
    · simpa [hf] using hb.pow_const p
    · simpa [hf] using hc.pow_const (p / (p - 2))
  · rw [Fin.sum_univ_three]
    simp only [hP]
    simp
    field_simp
    ring
  · intro i _
    fin_cases i
    · simp only [hP]
      simp
      positivity
    · simp only [hP]
      simp
      positivity
    · simp only [hP]
      simp
      positivity

end Work.BourgainPlan.Maximal
