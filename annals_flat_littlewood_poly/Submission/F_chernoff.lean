import Mathlib

/-!
Real-valued exponential Chebyshev (Chernoff) bounds (child task).

TASK: prove `prob_ge_le_of_mgf` and `prob_abs_ge_le_of_mgf` below (fill in the
proofs).  Add helpers above as needed.

Setup: `μ` is a probability measure (real-valued measure of a set is
`μ.real s : ℝ` = `(μ s).toReal`, see `MeasureTheory/Measure/Real.lean`).
`Z : α → ℝ` is measurable and satisfies the sub-Gaussian moment-generating
inequality `hmgf` with variance parameter `σsq > 0`, i.e. for ALL real `t`
(positive or negative)  E exp (t·Z) ≤ exp (t²·σsq / 2), and each exponential
is integrable (`hint`).

Conclusion (one-sided): for `a ≥ 0`,
   μ.real {x | a ≤ Z x} ≤ exp (-a² / (2·σsq)).

PROOF of the one-sided bound: take λ := a / σsq ≥ 0 (division by σsq > 0).
By Markov (mathlib: `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`, which
reads `ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ` for `f` nonnegative-a.e. and
integrable) applied to `f := fun x => Real.exp (λ * Z x)` and
`ε := Real.exp (λ * a)`:
   exp(λa) · μ.real {exp(λa) ≤ exp(λZ)} ≤ ∫ exp(λZ) ≤ exp (λ²σsq/2).
Since λ ≥ 0 the map z ↦ exp(λ z) is monotone, so
   {a ≤ Z} ⊆ {exp(λa) ≤ exp(λZ)}.
Conclude μ.real {a ≤ Z} ≤ exp(-λa) · exp(λ²σsq/2) = exp(-a²/(2σsq))
(divide both sides by the positive number exp(λa)).
The set {exp (λ*a) ≤ exp (λ * Z x)} may be written
`{x | Real.exp (λ*a) ≤ Real.exp (λ * Z x)}`.

For the two-sided version apply the one-sided bound to `Z` and to `-Z`
(negating preserves `hmgf` and `hint` by substituting `t ↦ -t`) and use
`MeasureTheory.measureReal_union_le` plus {a ≤ |Z|} ⊆ {a ≤ Z} ∪ {a ≤ -Z}.

Useful facts: `Real.exp_pos`, `Real.exp_le_exp` (monotonicity),
`Real.exp_add`/`Real.exp_sub` for the exponent arithmetic,
`ENNReal.toReal` facts via `MeasureTheory.measureReal_def` if needed.
`IsProbabilityMeasure μ` makes the measure finite; indicator/integral facts
like `MeasureTheory.integral_indicator_one` may help if you go through
indicators, but the direct Markov lemma above should suffice.
-/

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Submission.Discrepancy

/-- One-sided sub-Gaussian tail bound from an MGF bound. -/
lemma prob_ge_le_of_mgf {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {Z : α → ℝ} (hZ : Measurable Z) (σsq : ℝ) (hσsq : 0 < σsq)
    (hint : ∀ t : ℝ, Integrable (fun x : α => Real.exp (t * Z x)) μ)
    (hmgf : ∀ t : ℝ, (∫ x : α, Real.exp (t * Z x) ∂μ) ≤ Real.exp (t ^ 2 * σsq / 2)) :
    ∀ a : ℝ, 0 ≤ a → μ.real {x : α | a ≤ Z x} ≤ Real.exp (-(a ^ 2) / (2 * σsq)) := by
  intro a ha
  let t : ℝ := a / σsq
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg ha hσsq.le
  have hmain : Real.exp (t * a) * μ.real {x : α | a ≤ Z x} ≤ Real.exp (t ^ 2 * σsq / 2) := by
    have hmarkov : Real.exp (t * a) * μ.real {x : α | Real.exp (t * a) ≤ Real.exp (t * Z x)} ≤
        (∫ x : α, Real.exp (t * Z x) ∂μ) :=
      MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (μ := μ)
        (f := fun x : α => Real.exp (t * Z x))
        (hf_nonneg := ae_of_all μ (fun x => (Real.exp_pos _).le))
        (hf_int := hint t)
        (Real.exp (t * a))
    have hsub : {x : α | a ≤ Z x} ⊆ {x : α | Real.exp (t * a) ≤ Real.exp (t * Z x)} := by
      intro x hx
      exact (Real.exp_le_exp).2 (mul_le_mul_of_nonneg_left hx ht)
    have hmono : μ.real {x : α | a ≤ Z x} ≤
        μ.real {x : α | Real.exp (t * a) ≤ Real.exp (t * Z x)} :=
      measureReal_mono hsub (measure_ne_top μ _)
    calc
      Real.exp (t * a) * μ.real {x : α | a ≤ Z x}
          ≤ Real.exp (t * a) * μ.real {x : α | Real.exp (t * a) ≤ Real.exp (t * Z x)} := by
              exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
      _ ≤ (∫ x : α, Real.exp (t * Z x) ∂μ) := hmarkov
      _ ≤ Real.exp (t ^ 2 * σsq / 2) := hmgf t
  have hdiv : μ.real {x : α | a ≤ Z x} ≤ Real.exp (t ^ 2 * σsq / 2) / Real.exp (t * a) := by
    exact (le_div_iff₀' (Real.exp_pos (t * a))).mpr hmain
  have hcalc : t ^ 2 * σsq / 2 - t * a = -(a ^ 2) / (2 * σsq) := by
    dsimp [t]
    field_simp [hσsq.ne']
    ring
  calc
    μ.real {x : α | a ≤ Z x} ≤ Real.exp (t ^ 2 * σsq / 2) / Real.exp (t * a) := hdiv
    _ = Real.exp (t ^ 2 * σsq / 2 - t * a) := (Real.exp_sub _ _).symm
    _ = Real.exp (-(a ^ 2) / (2 * σsq)) := by rw [hcalc]

/-- Two-sided sub-Gaussian tail bound from an MGF bound. -/
lemma prob_abs_ge_le_of_mgf {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {Z : α → ℝ} (hZ : Measurable Z) (σsq : ℝ) (hσsq : 0 < σsq)
    (hint : ∀ t : ℝ, Integrable (fun x : α => Real.exp (t * Z x)) μ)
    (hmgf : ∀ t : ℝ, (∫ x : α, Real.exp (t * Z x) ∂μ) ≤ Real.exp (t ^ 2 * σsq / 2)) :
    ∀ a : ℝ, 0 ≤ a → μ.real {x : α | a ≤ |Z x|} ≤ 2 * Real.exp (-(a ^ 2) / (2 * σsq)) := by
  intro a ha
  let bound := Real.exp (-(a ^ 2) / (2 * σsq))
  have hintNeg : ∀ t : ℝ, Integrable (fun x : α => Real.exp (t * (-Z x))) μ := by
    intro t
    have hEq : (fun x : α => Real.exp ((-t) * Z x)) =ᵐ[μ]
        (fun x : α => Real.exp (t * (-Z x))) := by
      filter_upwards with x
      congr 1
      ring
    exact (hint (-t)).congr hEq
  have hmgfNeg : ∀ t : ℝ, (∫ x : α, Real.exp (t * (-Z x)) ∂μ) ≤ Real.exp (t ^ 2 * σsq / 2) := by
    intro t
    calc
      (∫ x : α, Real.exp (t * (-Z x)) ∂μ) = (∫ x : α, Real.exp ((-t) * Z x) ∂μ) := by
        apply integral_congr_ae
        filter_upwards with x
        congr 1
        ring
      _ ≤ Real.exp ((-t) ^ 2 * σsq / 2) := hmgf (-t)
      _ = Real.exp (t ^ 2 * σsq / 2) := by congr 1; ring
  have hge := prob_ge_le_of_mgf (μ := μ) (Z := Z) hZ σsq hσsq hint hmgf a ha
  have hle := prob_ge_le_of_mgf (μ := μ) (Z := fun x => -Z x) hZ.neg σsq hσsq hintNeg hmgfNeg a ha
  have hsub : {x : α | a ≤ |Z x|} ⊆ {x : α | a ≤ Z x} ∪ {x : α | a ≤ -Z x} := by
    intro x hx
    have hx' : a ≤ |Z x| := by simpa using hx
    exact (le_abs.mp hx')
  calc
    μ.real {x : α | a ≤ |Z x|} ≤ μ.real ({x : α | a ≤ Z x} ∪ {x : α | a ≤ -Z x}) :=
      measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {x : α | a ≤ Z x} + μ.real {x : α | a ≤ -Z x} := measureReal_union_le _ _
    _ ≤ bound + bound := by
        dsimp [bound]
        exact add_le_add hge hle
    _ = 2 * bound := by ring

end Discrepancy

end Submission
