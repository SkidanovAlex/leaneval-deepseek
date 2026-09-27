import Mathlib

namespace Work.EKLC7

open MeasureTheory

/-- If a function `Ψ`, bounded and measurable, is strictly positive on a `β`-finite measurable
set `A`, and its integral over `A` vanishes, then `A` is `β`-null.

This is the analytic heart of the "separation L²" step: a positive function with zero integral
forces the underlying set, and in particular the measure it is integrated against, to be trivial. -/
theorem SepL2MeasureZeroPos
    {β : MeasureTheory.Measure (ℝ × ℝ)} [MeasureTheory.IsFiniteMeasureOnCompacts β]
    {Ψ : ℝ × ℝ → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : ∀ z, |Ψ z| ≤ C)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAfin : β A ≠ ⊤)
    (hpos : ∀ z ∈ A, 0 < Ψ z) (hint : ∫ z in A, Ψ z ∂β = 0) :
    β A = 0 := by
  -- The measure `β` restricted to `A` is finite, because `β A ≠ ⊤`.
  have hfin : IsFiniteMeasure (β.restrict A) := by
    constructor
    rw [Measure.restrict_apply (s := A) (t := Set.univ) MeasurableSet.univ]
    simp only [Set.univ_inter]
    exact lt_top_iff_ne_top.mpr hAfin
  -- `Ψ` is nonnegative almost everywhere for `β.restrict A`: off `A` the measure vanishes,
  -- and on `A` it is strictly positive by `hpos`.
  have hnonneg : 0 ≤ᵐ[β.restrict A] Ψ := by
    show ∀ᵐ z ∂(β.restrict A), 0 ≤ Ψ z
    rw [ae_restrict_iff' hA]
    filter_upwards with z hz
    exact le_of_lt (hpos z hz)
  -- `Ψ` is integrable against the finite measure `β.restrict A`, being measurable and bounded.
  have hInt : Integrable Ψ (β.restrict A) :=
    Integrable.of_bound hΨ.aestronglyMeasurable C (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]; exact hC z))
  -- A nonnegative integrable function with vanishing integral is zero almost everywhere.
  have hae : Ψ =ᵐ[β.restrict A] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hInt).mp hint
  have hzero : (β.restrict A) {z | Ψ z ≠ 0} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hae
    simpa using hae
  -- `A ⊆ {Ψ ≠ 0}`, so `(β.restrict A) A ≤ (β.restrict A) {Ψ ≠ 0} = 0`.
  have hsub : A ⊆ {z | Ψ z ≠ 0} := fun z hz => ne_of_gt (hpos z hz)
  have hAzero : (β.restrict A) A = 0 :=
    le_antisymm (le_trans (measure_mono hsub) (le_of_eq hzero)) (by simp)
  -- Finally `(β.restrict A) A = β A`.
  rwa [Measure.restrict_apply hA, Set.inter_self] at hAzero

end Work.EKLC7
