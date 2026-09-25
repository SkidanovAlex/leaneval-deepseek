import Mathlib

open MeasureTheory

namespace Work.BourgainPlan.Maximal

/-- **Hölder for the `(q-1)`-th power on a probability space.**  For a probability measure `μ` and
an a.e. measurable `A : α → ℝ≥0∞`,

`∫⁻ x, A x ^ (q-1) ∂μ ≤ (∫⁻ x, A x ^ q ∂μ) ^ ((q-1)/q)`   (`1 < q`).

This is `ENNReal.lintegral_mul_le_Lp_mul_Lq` with the conjugate exponents `q/(q-1)` and `q` and the
test function `g ≡ 1` (using `μ univ = 1`): the left-hand side is `∫ (A^{q-1} · 1)` and the right
factors are `(∫ (A^{q-1})^{q/(q-1)})^{1/(q/(q-1))} = (∫ A^q)^{(q-1)/q}` and `(∫ 1^q)^{1/q} = 1`.
It is the step that converts Bourgain's (7.41) `C ∫ (Σ_k g_k * L_k)^{q-1}` into `C ρ^{q-1}`, where
`ρ^q = ∫ (Σ_k g_k * L_k)^q` is the constant of (7.39); the probability normalisation is what removes
any dependence on the size of the underlying finite group `ℤ_J`. -/
theorem lintegral_rpow_pred_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (A : α → ENNReal) (hA : AEMeasurable A μ) {q : ℝ}
    (hq : 1 < q) :
    MeasureTheory.lintegral μ (fun x => A x ^ (q - 1)) ≤
      (MeasureTheory.lintegral μ (fun x => A x ^ q)) ^ ((q - 1) / q) := by
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  -- `q / (q - 1)` and `q` are Hölder conjugate exponents
  have hpq : (q / (q - 1)).HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hq1]
      linarith
    · rw [inv_div]
      field_simp
      ring
  -- Hölder with `f = A ^ (q-1)` and `g ≡ 1`
  have hH : ∫⁻ x, (A x ^ (q - 1)) * 1 ∂μ ≤
      (∫⁻ x, (A x ^ (q - 1)) ^ (q / (q - 1)) ∂μ) ^ (1 / (q / (q - 1))) *
        (∫⁻ x, (1 : ENNReal) ^ q ∂μ) ^ (1 / q) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hA.pow_const (q - 1)) aemeasurable_const
  calc ∫⁻ x, A x ^ (q - 1) ∂μ
      = ∫⁻ x, (A x ^ (q - 1)) * 1 ∂μ := lintegral_congr fun x => (mul_one _).symm
    _ ≤ (∫⁻ x, (A x ^ (q - 1)) ^ (q / (q - 1)) ∂μ) ^ (1 / (q / (q - 1))) *
          (∫⁻ x, (1 : ENNReal) ^ q ∂μ) ^ (1 / q) := hH
    _ = (∫⁻ x, A x ^ q ∂μ) ^ ((q - 1) / q) := by
        -- `(A^(q-1))^(q/(q-1)) = A^q`
        have h1 : (∫⁻ x, ((A x) ^ (q - 1)) ^ (q / (q - 1)) ∂μ) = ∫⁻ x, A x ^ q ∂μ :=
          lintegral_congr fun x => by
            rw [← ENNReal.rpow_mul, show (q - 1) * (q / (q - 1)) = q by
              rw [mul_div_assoc', mul_div_cancel_left₀ q (by linarith : q - 1 ≠ 0)]]
        -- `∫ 1^q = μ univ = 1`
        have h2 : (∫⁻ x, (1 : ENNReal) ^ q ∂μ) = 1 := by simp
        rw [h1, h2, ENNReal.one_rpow, mul_one, one_div, inv_div]

end Work.BourgainPlan.Maximal
