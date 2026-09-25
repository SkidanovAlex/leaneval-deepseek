import Mathlib

open MeasureTheory ENNReal

namespace MeasureTheory

/-- Compatibility alias for the measure-theoretic `ℒᵖ`-membership predicate `MeasureTheory.MemLp`,
spelled `Memℓp` with the script `ℓ` of the requested statement.  It is a definitional copy of
`MeasureTheory.MemLp`, so the statement of `Work.IonescuWainger.memLp_count_two_iff` reads exactly
as requested while denoting the honest `Lp`-space membership predicate. -/
abbrev Memℓp {α : Type*} {ε : Type*} [MeasurableSpace α] [ENorm ε] [TopologicalSpace ε]
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  MeasureTheory.MemLp f p μ

end MeasureTheory

namespace Work.IonescuWainger

/-- For a nonnegative real function `g`, its `ENNReal`-valued `ofReal`-series is finite if and only
if `g` is summable.  (For nonnegative `g` the usual `ENNReal` convention "a divergent `∑'` is `⊤`"
coincides with divergence of the real series.) -/
lemma tsum_ofReal_lt_top_iff_summable {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) :
    (∑' i, ENNReal.ofReal (g i)) < ∞ ↔ Summable g := by
  rw [lt_top_iff_ne_top]
  rw [show (∑' i, ENNReal.ofReal (g i)) = ∑' i, ((g i).toNNReal : ℝ≥0∞) from by
    simp [ENNReal.ofReal]]
  rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact summable_congr fun i => by rw [Real.coe_toNNReal', max_eq_left (hg i)]

/-- **`ℓ²(ℤ)` membership against the counting measure is square-summability**: the counting
measure on `ℤ` is discrete and `σ`-finite, so `f ∈ ℓ²(ℤ)` (in the `MeasureTheory.MemLp` sense,
i.e. the predicate required to build an element of `MeasureTheory.lp (fun _ : ℤ => ℂ) 2`) holds if
and only if `Σ_n ‖f n‖² < ∞`.  This is the bridge between the `Memℓp`/`eLpNorm` language of the
Ionescu–Wainger modules and the elementary `Summable` estimates. -/
theorem memLp_count_two_iff {f : ℤ → ℂ} :
    MeasureTheory.Memℓp f 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ↔ Summable (fun n : ℤ => ‖f n‖ ^ 2) := by
  have hmeas : AEStronglyMeasurable f (Measure.count : Measure ℤ) :=
    (Measurable.of_discrete (f := f)).aestronglyMeasurable
  have hkey : eLpNorm f 2 (Measure.count : Measure ℤ) < ∞ ↔
      Summable (fun n : ℤ => ‖f n‖ ^ 2) := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hmeas]
    rw [lintegral_count]
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
    have hrpow : ∀ a : ℤ, ‖f a‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖f a‖ ^ 2) := fun a => by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        Real.rpow_two]
    simp_rw [hrpow]
    exact tsum_ofReal_lt_top_iff_summable (fun n => sq_nonneg _)
  change MeasureTheory.MemLp f 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ↔
    Summable (fun n : ℤ => ‖f n‖ ^ 2)
  exact hkey

end Work.IonescuWainger
