import Mathlib
import Submission.Work.Drive.shiftedNeedleDefs

/-!
# The window facts of the shifted needle's single-ray condition

The shifted needle `t ↦ needleFam r D lam δ₁ δ₂ ε (t + period/4)` has its base point at the middle
of the retained arc (`arcFrac = 1/2`), and its geometry in the loop parameter `τ = t + period/4`
runs, as `t` increases over one period, through the four branches of the chamfered loop.  This module
collects the elementary facts about the **loop-parameter window** `{τ - δ₁ u | u ∈ [-1,1]}` that the
case analysis of the single-ray condition consumes:

* `Work.Drive.sweepParam_le_half_of_mem`, `…_of_mem_Ico_period` — the loop parameter on the two
  relevant period cells;
* `Work.Drive.window_arc_left`, `Work.Drive.window_arc_right` — the window lies in the *arc branch*
  (`sweepParam ≤ 1/2`) in the two arc zones;
* `Work.Drive.baseWindow_frac` — on the base window (`τ = period/4`) the branch fraction is within
  `2 δ₁/period` of `1/2`;
* `Work.Drive.integral_needleFrac_ge`, `Work.Drive.integral_needleFrac_le` — a pointwise bound on
  the branch fraction over the window transfers to its `sweepBump`-average.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- The loop parameter on the first half period. -/
lemma sweepParam_le_half_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ period / 2) :
    sweepParam x ≤ 1 / 2 := by
  have hp : (0 : ℝ) < period := period_pos
  rw [sweepParam_eq_div ⟨h0, by linarith⟩, div_le_iff₀ hp]
  linarith

/-- **The window is in the arc branch (first arc zone).** -/
lemma window_arc_left {δ τ : ℝ} (hδ : 0 ≤ δ) (h1 : 0 < τ - δ) (h2 : τ + δ ≤ period / 2) :
    ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (τ - δ * u) ≤ 1 / 2 := by
  intro u hu
  have hu'' : |u| ≤ 1 := by rw [abs_le]; exact hu
  have hu' : -1 ≤ u ∧ u ≤ 1 := abs_le.mp hu''
  have hle : δ * u ≤ δ := by
    calc δ * u ≤ δ * 1 := mul_le_mul_of_nonneg_left hu'.2 hδ
      _ = δ := mul_one δ
  have hge : -δ ≤ δ * u := by
    calc -δ = δ * (-1) := by ring
      _ ≤ δ * u := mul_le_mul_of_nonneg_left hu'.1 hδ
  exact sweepParam_le_half_of_mem (by linarith) (by linarith)

/-- **The window is in the arc branch (second arc zone, past one period).** -/
lemma window_arc_right {δ τ : ℝ} (hδ : 0 ≤ δ) (h1 : period ≤ τ - δ)
    (h2 : τ + δ ≤ 3 * period / 2) :
    ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (τ - δ * u) ≤ 1 / 2 := by
  intro u hu
  have hp : (0 : ℝ) < period := period_pos
  have hu'' : |u| ≤ 1 := by rw [abs_le]; exact hu
  have hu' : -1 ≤ u ∧ u ≤ 1 := abs_le.mp hu''
  have hle : δ * u ≤ δ := by
    calc δ * u ≤ δ * 1 := mul_le_mul_of_nonneg_left hu'.2 hδ
      _ = δ := mul_one δ
  have hge : -δ ≤ δ * u := by
    calc -δ = δ * (-1) := by ring
      _ ≤ δ * u := mul_le_mul_of_nonneg_left hu'.1 hδ
  have hmem : τ - δ * u ∈ Set.Ico period (2 * period) := ⟨by linarith, by linarith⟩
  rw [sweepParam_of_mem_Ico_period hmem]
  have h3 : (τ - δ * u) / period ≤ 3 / 2 := by
    rw [div_le_iff₀ hp]; linarith
  linarith

/-- **The base window is in the arc branch.** -/
lemma baseWindow_arc {δ : ℝ} (hδ : 0 < δ) (h3 : 16 * δ ≤ period) :
    ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (period / 4 - δ * u) ≤ 1 / 2 := by
  refine window_arc_left hδ.le ?_ ?_
  · linarith [period_pos]
  · linarith

/-- **The branch fraction on the base window is within `2 δ/period` of `1/2`.** -/
lemma baseWindow_frac {lam δ : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) (h2 : 0 < δ)
    (h3 : 16 * δ ≤ period) :
    ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      |needleFrac lam (period / 4 - δ * u) - 1 / 2| ≤ 2 * (δ / period) := by
  intro u hu
  have hp : (0 : ℝ) < period := period_pos
  have hu'' : |u| ≤ 1 := by rw [abs_le]; exact hu
  have hu' : -1 ≤ u ∧ u ≤ 1 := abs_le.mp hu''
  have hle : δ * u ≤ δ := by
    calc δ * u ≤ δ * 1 := mul_le_mul_of_nonneg_left hu'.2 h2.le
      _ = δ := mul_one δ
  have hge : -δ ≤ δ * u := by
    calc -δ = δ * (-1) := by ring
      _ ≤ δ * u := mul_le_mul_of_nonneg_left hu'.1 h2.le
  have hmem : period / 4 - δ * u ∈ Set.Ico (0 : ℝ) period :=
    ⟨by linarith, by linarith⟩
  have hsp : sweepParam (period / 4 - δ * u) = 1 / 4 - (δ * u) / period := by
    rw [sweepParam_eq_div hmem]
    field_simp
  have hsle : sweepParam (period / 4 - δ * u) ≤ 1 / 2 := by
    rw [hsp]
    have h4 : -δ / period ≤ δ * u / period := div_le_div_of_nonneg_right hge hp.le
    have h5 : -δ / period = -(δ / period) := by ring
    have h6 : δ / period ≤ 1 / 16 := by rw [div_le_iff₀ hp]; linarith
    linarith
  rw [needleFrac_arc hsle, hsp]
  have hkey : lam + (1 - 2 * lam) * (2 * (1 / 4 - δ * u / period)) - 1 / 2
      = (1 - 2 * lam) * (-(2 * (δ * u / period))) := by ring
  rw [hkey, abs_mul]
  have habs : |1 - 2 * lam| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hsecond : |-(2 * (δ * u / period))| ≤ 2 * (δ / period) := by
    have h2u : |δ * u / period| ≤ δ / period := by
      rw [abs_div, abs_of_pos hp, div_le_div_iff_of_pos_right hp, abs_mul,
        abs_of_nonneg h2.le]
      calc δ * |u| ≤ δ * 1 := mul_le_mul_of_nonneg_left hu'' h2.le
        _ = δ := mul_one δ
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  calc |1 - 2 * lam| * |-(2 * (δ * u / period))| ≤ 1 * (2 * (δ / period)) :=
        mul_le_mul habs hsecond (abs_nonneg _) (by positivity)
    _ = 2 * (δ / period) := by ring

/-! ## From a pointwise bound over the window to its `sweepBump`-average -/

lemma intervalIntegrable_bump_mul_needleFrac {lam δ τ : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) :
    IntervalIntegrable (fun u : ℝ => sweepBump u * needleFrac lam (τ - δ * u)) volume (-1) 1 := by
  refine IntervalIntegrable.mono_fun' (sweepBump_continuous.intervalIntegrable (-1) 1) ?_ ?_
  · have hm : Measurable (fun u : ℝ => sweepBump u * needleFrac lam (τ - δ * u)) :=
      (Continuous.measurable sweepBump_continuous).mul ((measurable_needleFrac lam).comp
        (measurable_const.sub (measurable_const.mul measurable_id)))
    exact hm.aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg u)]
    have h := (needleFrac_unit (τ := τ - δ * u) h0 h1).2
    have hnn := (needleFrac_unit (τ := τ - δ * u) h0 h1).1
    rw [abs_of_nonneg hnn]
    calc sweepBump u * needleFrac lam (τ - δ * u) ≤ sweepBump u * 1 :=
          mul_le_mul_of_nonneg_left h (sweepBump_nonneg u)
      _ = sweepBump u := mul_one _

/-- **A lower bound on the window gives a lower bound on the `sweepBump`-average.** -/
lemma integral_needleFrac_ge {lam δ τ c : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (h : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → c ≤ needleFrac lam (τ - δ * u)) :
    c ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ * u) := by
  have hint := intervalIntegrable_bump_mul_needleFrac (δ := δ) (τ := τ) h0 h1
  have hconst : IntervalIntegrable (fun u : ℝ => sweepBump u * c) volume (-1) 1 :=
    (sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hconst hint
    (fun u hu => by
      rcases le_or_gt |u| 1 with h' | h'
      · exact mul_le_mul_of_nonneg_left (h u (abs_le.mp h')) (sweepBump_nonneg u)
      · rw [sweepBump_eq_zero h'.le, zero_mul, zero_mul])
  rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul] at hmono
  exact hmono

/-- **An upper bound on the window gives an upper bound on the `sweepBump`-average.** -/
lemma integral_needleFrac_le {lam δ τ c : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (h : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → needleFrac lam (τ - δ * u) ≤ c) :
    (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ * u)) ≤ c := by
  have hint := intervalIntegrable_bump_mul_needleFrac (δ := δ) (τ := τ) h0 h1
  have hconst : IntervalIntegrable (fun u : ℝ => sweepBump u * c) volume (-1) 1 :=
    (sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hint hconst
    (fun u hu => by
      rcases le_or_gt |u| 1 with h' | h'
      · exact mul_le_mul_of_nonneg_left (h u (abs_le.mp h')) (sweepBump_nonneg u)
      · rw [sweepBump_eq_zero h'.le, zero_mul, zero_mul])
  rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul] at hmono
  exact hmono

end Work.Drive
