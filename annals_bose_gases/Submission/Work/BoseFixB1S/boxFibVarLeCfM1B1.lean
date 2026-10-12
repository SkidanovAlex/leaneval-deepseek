import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxFibVarLeCfM1B1` — the fibre-variance bound against `C_f · M₁`

For a measurable set `A` of volume `V > 0` and a measurable, nonnegative fibre function
`fib` on `A` which is bounded by `C_f` there, the variance of `fib` over `A` is at most
`C_f` times its mass:

    ∫_A (fib - (∫_A fib)/V)²  ≤  C_f · ∫_A fib .

This is the *trivial* half of the fibre-fluctuation bookkeeping: the exact variance
identity

    ∫_A (fib - m)² = ∫_A fib² - m² V          (m = (∫_A fib)/V)

together with the pointwise bound `fib² ≤ C_f·fib` (valid on `A` because `0 ≤ fib ≤ C_f`
there, no sign condition on `C_f` being needed) and the sign `m² V ≥ 0` gives it at once.
No geometric input (`ℓ`, the cube `A ⊆ acube ℓ`) is used; those hypotheses only serve to
name the object of the ambient argument.
-/

namespace Work.BoseFixB1S

open MeasureTheory

set_option linter.unusedVariables false in
/-- **The fibre variance is bounded by `C_f` times the fibre mass.**  See the module
docstring. -/
theorem boxFibVarLeCfM1B1 {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    {Cf : ℝ} (hfible : ∀ z ∈ A, fib z ≤ Cf)
    (hint : MeasureTheory.IntegrableOn fib A) :
    (∫ z in A, (fib z - (∫ z in A, fib z) / V) ^ 2) ≤ Cf * (∫ z in A, fib z) := by
  classical
  set S : ℝ := ∫ z in A, fib z with hS
  set m : ℝ := S / V with hm
  have hmV : m * V = S := by rw [hm]; exact div_mul_cancel₀ S (ne_of_gt hV)
  -- `V > 0` forces `A` to have finite measure.
  have hvoltop : (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A ≠ ⊤ := by
    intro h
    rw [h, ENNReal.toReal_top] at hVeq
    linarith
  -- `fib ^ 2` is dominated by the integrable function `C_f * fib` on `A`.
  have haeb : ∀ᵐ z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A,
      ‖fib z ^ 2‖ ≤ Cf * fib z := by
    rw [MeasureTheory.ae_restrict_iff' hA]
    filter_upwards with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (fib z))]
    have h := mul_le_mul_of_nonneg_right (hfible z hz) (hfib0 z)
    simpa [pow_two] using h
  have hfib2 : MeasureTheory.IntegrableOn (fun z => fib z ^ 2) A :=
    MeasureTheory.Integrable.mono' (hint.integrable.const_mul Cf)
      ((((continuous_pow 2).measurable).comp hfm).aestronglyMeasurable) haeb
  have hconst : MeasureTheory.IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => m ^ 2) A :=
    MeasureTheory.integrableOn_const hvoltop (by simp)
  -- the exact variance identity `∫_A (fib - m)² = ∫_A fib² - m² V = ∫_A fib² - m S`
  have hId : (∫ z in A, (fib z - m) ^ 2) = (∫ z in A, fib z ^ 2) - m * S := by
    have hI1 : MeasureTheory.IntegrableOn (fun z => fib z ^ 2 - 2 * m * fib z) A :=
      hfib2.sub (hint.integrable.const_mul (2 * m))
    have hstep0 : (∫ z in A, (fib z - m) ^ 2)
        = ∫ z in A, (fib z ^ 2 - 2 * m * fib z + m ^ 2) := by
      apply MeasureTheory.setIntegral_congr_fun hA
      intro z _
      ring
    have hstep1 : (∫ z in A, (fib z ^ 2 - 2 * m * fib z + m ^ 2))
        = (∫ z in A, (fib z ^ 2 - 2 * m * fib z)) + (∫ z in A, m ^ 2) :=
      MeasureTheory.integral_add hI1 hconst
    have hstep2 : (∫ z in A, (fib z ^ 2 - 2 * m * fib z))
        = (∫ z in A, fib z ^ 2) - (∫ z in A, 2 * m * fib z) :=
      MeasureTheory.integral_sub hfib2 (hint.integrable.const_mul (2 * m))
    have hstep3 : (∫ z in A, 2 * m * fib z) = 2 * m * S :=
      MeasureTheory.integral_const_mul (2 * m) fib
    have hstep4 : (∫ z in A, m ^ 2) = m ^ 2 * V := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real_def,
        ← hVeq]
      ring
    rw [hstep0, hstep1, hstep2, hstep3, hstep4]
    have halg : m ^ 2 * V = m * S := by rw [sq, mul_assoc, hmV]
    rw [halg]
    ring
  -- `∫_A fib² ≤ C_f · ∫_A fib`, from the pointwise bound `fib² ≤ C_f · fib` on `A`
  have hsq : (∫ z in A, fib z ^ 2) ≤ Cf * S := by
    have hmono := MeasureTheory.setIntegral_mono_on hfib2 (hint.integrable.const_mul Cf) hA
      (fun z hz => by
        have h := mul_le_mul_of_nonneg_right (hfible z hz) (hfib0 z)
        simpa [pow_two] using h)
    calc (∫ z in A, fib z ^ 2) ≤ ∫ z in A, Cf * fib z := hmono
      _ = Cf * S := MeasureTheory.integral_const_mul Cf fib
  have hmS : 0 ≤ m * S := by
    have h : m * S = S ^ 2 / V := by rw [hm, div_mul_eq_mul_div, sq]
    rw [h]
    exact div_nonneg (sq_nonneg S) hV.le
  calc (∫ z in A, (fib z - m) ^ 2)
      = (∫ z in A, fib z ^ 2) - m * S := hId
    _ ≤ (∫ z in A, fib z ^ 2) := by linarith
    _ ≤ Cf * S := hsq

end Work.BoseFixB1S
