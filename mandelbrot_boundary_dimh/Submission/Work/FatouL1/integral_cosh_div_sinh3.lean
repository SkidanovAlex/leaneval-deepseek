import Mathlib
import Submission.Work.FatouL1.tendsto_sinhPi_div_sqrt
import Submission.Work.FatouL1.integrable_of_even_of_integrableOn_Ioi

/-!
# The integral `∫ y, cosh (π (y - a)) / (A + sinh (π (y - a)) ^ 2) ^ (3/2)`

For `a : ℝ` and `A > 0`,

  `∫ y, cosh (π (y - a)) / ((A + sinh (π (y - a)) ^ 2) * sqrt (A + sinh (π (y - a)) ^ 2)) = 2 / (π A)`

and the integrand is integrable.

The antiderivative of `z ↦ cosh (π z) / ((A + sinh (π z) ^ 2) * sqrt (A + sinh (π z) ^ 2))`
is `z ↦ sinh (π z) / (A * sqrt (A + sinh (π z) ^ 2))` (divided by `π`), which increases from
`-1/A` to `1/A`; the half line `(0, ∞)` therefore contributes `1/(π A)` and the evenness of the
integrand doubles this.  A final translation moves the centre from `0` to `a`.
-/

namespace Work.FatouL1

open MeasureTheory Set Filter
open scoped Real Topology

/-- `u ↦ u / sqrt (A + u ^ 2)`; its derivative is `A / ((A + u ^ 2) * sqrt (A + u ^ 2))`. -/
private noncomputable def Paux (A u : ℝ) : ℝ := u / Real.sqrt (A + u ^ 2)

/-- An antiderivative of `π • cosh (π ·) / (…)^(3/2)`. -/
private noncomputable def Gaux (A z : ℝ) : ℝ := (1 / A) * Paux A (Real.sinh (Real.pi * z))

/-- The integrand `cosh (π z) / ((A + sinh (π z) ^ 2) * sqrt (A + sinh (π z) ^ 2))`. -/
private noncomputable def Kaux (A z : ℝ) : ℝ :=
  Real.cosh (Real.pi * z) /
    ((A + Real.sinh (Real.pi * z) ^ 2) * Real.sqrt (A + Real.sinh (Real.pi * z) ^ 2))

/-- An antiderivative of `Kaux A`, namely `(1/π) * Gaux A`. -/
private noncomputable def Jaux (A z : ℝ) : ℝ := (1 / Real.pi) * Gaux A z

private lemma hasDerivAt_Paux (A u : ℝ) (hA : 0 < A) :
    HasDerivAt (Paux A) (A / ((A + u ^ 2) * Real.sqrt (A + u ^ 2))) u := by
  have hAu : (0 : ℝ) < A + u ^ 2 := by positivity
  have hinner : HasDerivAt (fun u : ℝ => A + u ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_id u).pow 2).const_add A
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (A + u ^ 2))
      ((2 * u) / (2 * Real.sqrt (A + u ^ 2))) u := hinner.sqrt hAu.ne'
  have hDne : Real.sqrt (A + u ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hAu).ne'
  have hnum : HasDerivAt (fun u : ℝ => u) (1 : ℝ) u := hasDerivAt_id u
  have h := hnum.div hsqrt hDne
  refine h.congr_deriv ?_
  field_simp
  rw [Real.sq_sqrt hAu.le]
  ring

/-- The derivative of the antiderivative `Gaux A` is `π • Kaux A`. -/
private lemma hasDerivAt_Gaux (A z : ℝ) (hA : 0 < A) :
    HasDerivAt (Gaux A) (Real.pi * Kaux A z) z := by
  have hsin : HasDerivAt (fun z : ℝ => Real.sinh (Real.pi * z))
      (Real.pi * Real.cosh (Real.pi * z)) z := by
    have h1 : HasDerivAt (fun z : ℝ => Real.pi * z) Real.pi z := by
      simpa using (hasDerivAt_id z).const_mul (Real.pi)
    have h2 := (Real.hasDerivAt_sinh (Real.pi * z)).comp z h1
    simpa [Function.comp_def, mul_comm] using h2
  have h3 : HasDerivAt (fun u : ℝ => (1 / A) * Paux A u)
      ((1 / A) * (A / ((A + (Real.sinh (Real.pi * z)) ^ 2) *
        Real.sqrt (A + (Real.sinh (Real.pi * z)) ^ 2))))
      (Real.sinh (Real.pi * z)) :=
    (hasDerivAt_Paux A (Real.sinh (Real.pi * z)) hA).const_mul (1 / A)
  have h := h3.comp z hsin
  refine h.congr_deriv ?_
  unfold Kaux
  have hD : ((A + (Real.sinh (Real.pi * z)) ^ 2) *
      Real.sqrt (A + (Real.sinh (Real.pi * z)) ^ 2)) ≠ 0 := by positivity
  field_simp

/-- `Gaux A` tends to `1 / A` at `+∞`. -/
private lemma tendsto_Gaux (A : ℝ) (hA : 0 < A) :
    Tendsto (Gaux A) atTop (𝓝 (1 / A)) := by
  have h := (tendsto_sinhPi_div_sqrt A hA).const_mul (1 / A)
  rw [mul_one] at h
  exact h

/-- The derivative of the antiderivative `Jaux A` is `Kaux A`. -/
private lemma hasDerivAt_Jaux (A z : ℝ) (hA : 0 < A) :
    HasDerivAt (Jaux A) (Kaux A z) z := by
  have h := (hasDerivAt_Gaux A z hA).const_mul (1 / Real.pi)
  refine h.congr_deriv ?_
  field_simp

/-- `Jaux A` tends to `(1/π) * (1/A)` at `+∞`. -/
private lemma tendsto_Jaux (A : ℝ) (hA : 0 < A) :
    Tendsto (Jaux A) atTop (𝓝 ((1 / Real.pi) * (1 / A))) :=
  (tendsto_Gaux A hA).const_mul (1 / Real.pi)

private lemma Kaux_nonneg (A z : ℝ) (hA : 0 < A) : 0 ≤ Kaux A z := by
  unfold Kaux
  positivity

/-- `Kaux A` is even. -/
private lemma Kaux_even (A z : ℝ) : Kaux A (-z) = Kaux A z := by
  unfold Kaux
  rw [show Real.pi * (-z) = -(Real.pi * z) by ring]
  simp only [Real.cosh_neg, Real.sinh_neg, neg_sq]

/-- The half line integral `∫_{(0,∞)} Kaux A = 1 / (π A)`. -/
private lemma integral_Kaux_Ioi (A : ℝ) (hA : 0 < A) :
    ∫ z in Ioi (0 : ℝ), Kaux A z = 1 / (Real.pi * A) := by
  have hderiv : ∀ z ∈ Ici (0 : ℝ), HasDerivAt (Jaux A) (Kaux A z) z :=
    fun z _ => hasDerivAt_Jaux A z hA
  have hpos : ∀ z ∈ Ioi (0 : ℝ), 0 ≤ Kaux A z := fun z _ => Kaux_nonneg A z hA
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
      (l := (1 / Real.pi) * (1 / A)) hderiv hpos (tendsto_Jaux A hA)
  have hJ0 : Jaux A 0 = 0 := by simp [Jaux, Gaux, Paux]
  rw [h, hJ0, sub_zero]
  field_simp

/-- `Kaux A` is integrable on `(0, ∞)`. -/
private lemma integrableOn_Kaux_Ioi (A : ℝ) (hA : 0 < A) :
    IntegrableOn (Kaux A) (Ioi 0) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (a := 0) (l := (1 / Real.pi) * (1 / A))
    (fun z _ => hasDerivAt_Jaux A z hA) (fun z _ => Kaux_nonneg A z hA) (tendsto_Jaux A hA)

/-- `Kaux A` is integrable on `ℝ`. -/
private lemma integrable_Kaux (A : ℝ) (hA : 0 < A) : Integrable (Kaux A) :=
  integrable_of_even_of_integrableOn_Ioi (fun z => Kaux_even A z)
    (integrableOn_Kaux_Ioi A hA)

/-- `∫_ℝ Kaux A = 2 / (π A)`. -/
private lemma integral_Kaux (A : ℝ) (hA : 0 < A) :
    ∫ z, Kaux A z = 2 / (Real.pi * A) := by
  have hev : (fun z : ℝ => Kaux A |z|) = Kaux A := by
    funext z
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg (not_le.mp hz), Kaux_even]
  rw [← hev, integral_comp_abs, integral_Kaux_Ioi A hA]
  field_simp

theorem integral_cosh_div_sinh3 (a A : ℝ) (hA : 0 < A) :
    MeasureTheory.Integrable
        (fun y : ℝ => Real.cosh (Real.pi * (y - a)) /
          ((A + Real.sinh (Real.pi * (y - a)) ^ 2) *
            Real.sqrt (A + Real.sinh (Real.pi * (y - a)) ^ 2))) ∧
      (∫ y : ℝ, Real.cosh (Real.pi * (y - a)) /
          ((A + Real.sinh (Real.pi * (y - a)) ^ 2) *
            Real.sqrt (A + Real.sinh (Real.pi * (y - a)) ^ 2))) = 2 / (Real.pi * A) := by
  have hk : Integrable (Kaux A) := integrable_Kaux A hA
  have hval : ∫ z, Kaux A z = 2 / (Real.pi * A) := integral_Kaux A hA
  have hme : MeasurableEmbedding (fun y : ℝ => y + (-a)) :=
    (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
  have hmp : MeasurePreserving (fun y : ℝ => y + (-a)) volume volume :=
    MeasureTheory.measurePreserving_add_right volume (-a)
  have hint : Integrable (fun y : ℝ => Kaux A (y + (-a))) :=
    (hmp.integrable_comp_emb hme).mpr hk
  have hval' : ∫ y, Kaux A (y + (-a)) = 2 / (Real.pi * A) := by
    rw [MeasureTheory.MeasurePreserving.integral_comp hmp hme (Kaux A), hval]
  refine ⟨?_, ?_⟩
  · simpa [Kaux, sub_eq_add_neg] using hint
  · simpa [Kaux, sub_eq_add_neg] using hval'

end Work.FatouL1
