import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseSplit

theorem sqSubAddSq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] {f h : α → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) (hh : MeasureTheory.AEStronglyMeasurable h μ)
    {Cf Ch : ℝ} (hfb : ∀ᵐ x ∂μ, |f x| ≤ Cf) (hhb : ∀ᵐ x ∂μ, |h x| ≤ Ch)
    (horth : ∫ x, h x * (f x - h x) ∂μ = 0) :
    (∫ x, (f x - h x) ^ 2 ∂μ) + (∫ x, (h x) ^ 2 ∂μ) = ∫ x, (f x) ^ 2 ∂μ := by
  -- Integrability of `f` and `h` from the a.e. bounds and finiteness of `μ`.
  have hf_int : Integrable f μ := Integrable.of_bound hf |Cf| (by
    filter_upwards [hfb] with x hx
    simpa [Real.norm_eq_abs] using le_trans hx (le_abs_self Cf))
  have hh_int : Integrable h μ := Integrable.of_bound hh |Ch| (by
    filter_upwards [hhb] with x hx
    simpa [Real.norm_eq_abs] using le_trans hx (le_abs_self Ch))
  have hfh_int : Integrable (fun x => f x - h x) μ := hf_int.sub hh_int
  -- Integrability of the three quadratic quantities, all bounded a.e. by the
  -- nonnegative constants built out of `|Cf|`, `|Ch|` (no case distinctions).
  have hb1 : ∀ᵐ x ∂μ, ‖(fun y => (f y - h y) ^ 2) x‖ ≤ (|Cf| + |Ch|) ^ 2 := by
    filter_upwards [hfb, hhb] with x hx1 hx2
    have h1 : |f x - h x| ≤ |Cf| + |Ch| := by
      calc |f x - h x| ≤ |f x| + |h x| := abs_sub _ _
        _ ≤ |Cf| + |Ch| :=
          add_le_add (le_trans hx1 (le_abs_self Cf)) (le_trans hx2 (le_abs_self Ch))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (f x - h x), abs_nonneg (f x - h x)]
  have h1 : Integrable (fun x => (f x - h x) ^ 2) μ :=
    Integrable.of_bound (hfh_int.aestronglyMeasurable.pow 2) _ hb1
  have hb2 : ∀ᵐ x ∂μ, ‖(fun y => (h y) ^ 2) x‖ ≤ (|Ch|) ^ 2 := by
    filter_upwards [hhb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |h x| ≤ |Ch| := le_trans hx (le_abs_self Ch)
    nlinarith [sq_abs (h x), abs_nonneg (h x)]
  have h2 : Integrable (fun x => (h x) ^ 2) μ :=
    Integrable.of_bound (hh_int.aestronglyMeasurable.pow 2) _ hb2
  have hb3 : ∀ᵐ x ∂μ, ‖(fun y => h y * (f y - h y)) x‖ ≤ |Ch| * (|Cf| + |Ch|) := by
    filter_upwards [hfb, hhb] with x hx1 hx2
    have h1 : |f x - h x| ≤ |Cf| + |Ch| := by
      calc |f x - h x| ≤ |f x| + |h x| := abs_sub _ _
        _ ≤ |Cf| + |Ch| :=
          add_le_add (le_trans hx1 (le_abs_self Cf)) (le_trans hx2 (le_abs_self Ch))
    rw [Real.norm_eq_abs, abs_mul]
    have hc : |h x| ≤ |Ch| := le_trans hx2 (le_abs_self Ch)
    nlinarith [abs_nonneg (h x), abs_nonneg (f x - h x), abs_nonneg Ch, abs_nonneg Cf]
  have h3 : Integrable (fun x => h x * (f x - h x)) μ :=
    Integrable.of_bound ((hh_int.aestronglyMeasurable.mul hfh_int.aestronglyMeasurable)) _ hb3
  have hb4 : ∀ᵐ x ∂μ, ‖(fun y => (f y) ^ 2) x‖ ≤ (|Cf|) ^ 2 := by
    filter_upwards [hfb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |f x| ≤ |Cf| := le_trans hx (le_abs_self Cf)
    nlinarith [sq_abs (f x), abs_nonneg (f x)]
  have h4 : Integrable (fun x => (f x) ^ 2) μ :=
    Integrable.of_bound (hf_int.aestronglyMeasurable.pow 2) _ hb4
  -- Pointwise expansion: `(f-h)^2 + h^2 = f^2 - 2 h (f-h)`.
  have key : ∀ᵐ x ∂μ,
      (f x - h x) ^ 2 + (h x) ^ 2 = (f x) ^ 2 - 2 * (h x * (f x - h x)) := by
    filter_upwards with x
    ring
  calc (∫ x, (f x - h x) ^ 2 ∂μ) + (∫ x, (h x) ^ 2 ∂μ)
      = ∫ x, ((f x - h x) ^ 2 + (h x) ^ 2) ∂μ := (integral_add h1 h2).symm
    _ = ∫ x, ((f x) ^ 2 - 2 * (h x * (f x - h x))) ∂μ := integral_congr_ae key
    _ = (∫ x, (f x) ^ 2 ∂μ) - 2 * (∫ x, h x * (f x - h x) ∂μ) := by
          rw [integral_sub h4 (h3.const_mul 2), integral_const_mul]
    _ = ∫ x, (f x) ^ 2 ∂μ := by rw [horth]; ring

end Work.BoseSplit
