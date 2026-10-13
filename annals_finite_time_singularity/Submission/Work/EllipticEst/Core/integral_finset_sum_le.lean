import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped ENNReal

namespace Work.EllipticEst.Core

/-- `toReal` of an `ℝ≥0∞`-valued finite sum is at most the sum of the `toReal`s (the two differ
exactly when the sum is infinite, in which case the left-hand side is `0`). -/
private lemma toReal_finset_sum_le {ι : Type*} (s : Finset ι) (L : ι → ℝ≥0∞) :
    (∑ i ∈ s, L i).toReal ≤ ∑ i ∈ s, (L i).toReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.toReal_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans ENNReal.toReal_add_le (add_le_add le_rfl ih)

/-- Subadditivity of the Bochner integral over a finite family of nonnegative, a.e.-measurable
functions: `∫ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ∫ f i`.  No integrability is assumed.  (Requires
`open MeasureTheory` / `import Mathlib`.) -/
theorem integral_finset_sum_le {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {ι : Type*} (s : Finset ι) {f : ι → α → ℝ}
    (hmeas : ∀ i ∈ s, AEMeasurable (f i) μ)
    (hnn : ∀ i ∈ s, 0 ≤ᵐ[μ] f i) :
    ∫ a, ∑ i ∈ s, f i a ∂μ ≤ ∑ i ∈ s, ∫ a, f i a ∂μ := by
  classical
  -- a.e. joint nonnegativity of the whole family
  have key : ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ᵐ[μ] f i) → ∀ᵐ a ∂μ, ∀ i ∈ s, 0 ≤ f i a := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert j t hjt ih =>
      intro h
      have h1 : 0 ≤ᵐ[μ] f j := h j (Finset.mem_insert_self j t)
      have h2 : ∀ i ∈ t, 0 ≤ᵐ[μ] f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      filter_upwards [h1, ih h2] with a ha1 ha2
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact ha1
      · exact ha2 i hi
  have hjoint : ∀ᵐ a ∂μ, ∀ i ∈ s, 0 ≤ f i a := key s hnn
  have hsum_nn : 0 ≤ᵐ[μ] (fun a => ∑ i ∈ s, f i a) :=
    hjoint.mono fun a ha => Finset.sum_nonneg fun i hi => ha i hi
  have hsum_meas : AEStronglyMeasurable (fun a => ∑ i ∈ s, f i a) μ :=
    Finset.aestronglyMeasurable_fun_sum s fun i hi => (hmeas i hi).aestronglyMeasurable
  -- pointwise (a.e.) additivity of `ENNReal.ofReal` over the finite sum
  have hcongr : (fun a => ENNReal.ofReal (∑ i ∈ s, f i a))
      =ᵐ[μ] (fun a => ∑ i ∈ s, ENNReal.ofReal (f i a)) :=
    hjoint.mono fun a ha => ENNReal.ofReal_sum_of_nonneg ha
  have hR : ∑ i ∈ s, ∫ a, f i a ∂μ
      = ∑ i ∈ s, (∫⁻ a, ENNReal.ofReal (f i a) ∂μ).toReal :=
    Finset.sum_congr rfl fun i hi =>
      integral_eq_lintegral_of_nonneg_ae (hnn i hi) ((hmeas i hi).aestronglyMeasurable)
  rw [hR, integral_eq_lintegral_of_nonneg_ae hsum_nn hsum_meas, lintegral_congr_ae hcongr,
    lintegral_finsetSum' s (fun i hi => (hmeas i hi).ennreal_ofReal)]
  exact toReal_finset_sum_le s _

end Work.EllipticEst.Core
