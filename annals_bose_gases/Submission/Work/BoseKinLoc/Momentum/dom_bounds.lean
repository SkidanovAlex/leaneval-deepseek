import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseKinLoc.Momentum.cubFT_1d
import Submission.Work.BoseKinLoc.Momentum.div_sq_abs_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dominating functions `Fdom`, `Gdom` of the 1D cube-symbol factors

`Fdom t = min 1 (4/t²)` and `Gdom t = min (1/2) (4/t²)` dominate `(hFT t)²` and `(mFT t)²`
respectively (see `cubFT_1d`).  This module records their basic analytic properties:
integrability, the exact total mass `∫ Fdom = 8`, the bound `∫ Gdom ≤ 6`, and the exterior
bounds `∫_{|t| ≥ s} Fdom ≤ 8/s`, `∫_{|t| ≥ s} Gdom ≤ 8/s`.

The exterior bounds are immediate from `4/t² ≥ Fdom, Gdom` together with
`Work.BoseKinLoc.Momentum.div_sq_abs_ge` (`∫_{|t| ≥ s} 4/t² = 8/s`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

/-- `Fdom t = min 1 (4/t²) ≤ 4/t²`. -/
lemma Fdom_le_div_sq (t : ℝ) : Fdom t ≤ 4 / t ^ 2 := min_le_right _ _

/-- `Gdom t = min (1/2) (4/t²) ≤ 4/t²`. -/
lemma Gdom_le_div_sq (t : ℝ) : Gdom t ≤ 4 / t ^ 2 := min_le_right _ _

/-- `Gdom ≤ Fdom`, because `1/2 ≤ 1`. -/
lemma Gdom_le_Fdom (t : ℝ) : Gdom t ≤ Fdom t := min_le_min (by norm_num) le_rfl

/-- `Fdom t = min 1 (4/t²) ≤ 5/(1+t²)`: on `|t| ≤ 2` the bound is `1 ≤ 5/(1+t²)`, and for
`|t| ≥ 2` it is `4/t² ≤ 5/(1+t²)`, both elementary. -/
lemma Fdom_le_five (t : ℝ) : Fdom t ≤ 5 / (1 + t ^ 2) := by
  rw [Fdom]
  rcases lt_or_ge |t| 2 with h | h
  · have h1 : min 1 (4 / t ^ 2) ≤ 1 := min_le_left _ _
    have h2 : (1 : ℝ) ≤ 5 / (1 + t ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [abs_le.mp h.le]
    linarith
  · have ht2 : 4 ≤ t ^ 2 := by nlinarith [sq_abs t, h]
    have h1 : min 1 (4 / t ^ 2) ≤ 4 / t ^ 2 := min_le_right _ _
    have h3 : 4 / t ^ 2 ≤ 5 / (1 + t ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `t ↦ 5/(1+t²)` is integrable on `ℝ`. -/
lemma integrable_five : MeasureTheory.Integrable (fun t : ℝ => 5 / (1 + t ^ 2)) := by
  have h : (fun t : ℝ => 5 / (1 + t ^ 2)) = fun t => 5 * (1 + t ^ 2)⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [h]
  exact integrable_inv_one_add_sq.const_mul 5

lemma measurable_Fdom : Measurable Fdom := by unfold Fdom; measurability

lemma measurable_Gdom : Measurable Gdom := by unfold Gdom; measurability

/-- `Fdom` is integrable. -/
theorem integrable_Fdom : MeasureTheory.Integrable Fdom :=
  MeasureTheory.Integrable.mono' integrable_five measurable_Fdom.aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Fdom_nonneg t)]
      exact Fdom_le_five t)

/-- `Gdom ≤ Fdom`, so `Gdom` is integrable as well. -/
theorem integrable_Gdom : MeasureTheory.Integrable Gdom :=
  MeasureTheory.Integrable.mono' integrable_Fdom measurable_Gdom.aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Gdom_nonneg t)]
      exact Gdom_le_Fdom t)

/-- `∫_ℝ Fdom = 8`: on `[-2,2]` the integrand is `1` (except at the origin) and outside it
is `4/t²` whose exterior mass is `8/2 = 4`. -/
theorem integral_Fdom : ∫ t : ℝ, Fdom t = 8 := by
  have hmem : MeasurableSet {u : ℝ | |u| ≤ 2} := by measurability
  have hcompl : {u : ℝ | |u| ≤ 2}ᶜ = {u : ℝ | 2 < |u|} := by
    ext u; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  have hae : ∫ t in {u : ℝ | |u| ≤ 2}, Fdom t = ∫ t in {u : ℝ | |u| ≤ 2}, (1 : ℝ) := by
    refine MeasureTheory.setIntegral_congr_ae hmem ?_
    have hzero : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hzero] with t ht
    intro hts
    rw [Fdom]
    have h2 : t ^ 2 ≤ 4 := by nlinarith [abs_le.mp hts]
    have hpos : 0 < t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t, abs_pos.mpr ht]
    exact min_eq_left (by rw [le_div_iff₀ hpos]; nlinarith)
  have hval1 : ∫ t in {u : ℝ | |u| ≤ 2}, (1 : ℝ) = 4 := by
    have hset : {u : ℝ | |u| ≤ 2} = Set.Icc (-2) 2 := by ext u; simp [abs_le]
    rw [hset, setIntegral_const, Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 - -2)]
    norm_num
  have hval2 : ∫ t in {u : ℝ | 2 < |u|}, Fdom t = 4 := by
    obtain ⟨-, -, -, hval⟩ := div_sq_abs_ge 2 (by norm_num)
    have heq : ∫ t in {u : ℝ | 2 < |u|}, Fdom t = ∫ t in {u : ℝ | 2 < |u|}, 4 / t ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun (by measurability) (fun t ht => ?_)
      rw [Fdom]
      have ht' : (2 : ℝ) < |t| := ht
      have ht2 : 4 < t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t, ht']
      have hpos : 0 < t ^ 2 := by linarith
      exact min_eq_right (le_of_lt (by rw [div_lt_one hpos]; linarith))
    rw [heq, hval]
    norm_num
  rw [← MeasureTheory.integral_add_compl hmem integrable_Fdom, hcompl, hae, hval1, hval2]
  norm_num

/-- `∫_ℝ Gdom ≤ 6`: split at `|t| = 3`; there `Gdom ≤ 1/2` on `[-3,3]` (mass `6 · 1/2 = 3`)
and `Gdom ≤ 4/t²` outside it (mass `8/3`), total `17/3 ≤ 6`. -/
theorem integral_Gdom_le_six : ∫ t : ℝ, Gdom t ≤ 6 := by
  have hmem : MeasurableSet {u : ℝ | |u| ≤ 3} := by measurability
  have hcompl : {u : ℝ | |u| ≤ 3}ᶜ = {u : ℝ | 3 < |u|} := by
    ext u; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  have hvol : (volume {u : ℝ | |u| ≤ 3}) ≠ ⊤ := by
    have hset : {u : ℝ | |u| ≤ 3} = Set.Icc (-3) 3 := by ext u; simp [abs_le]
    rw [hset, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have h1 : ∫ t in {u : ℝ | |u| ≤ 3}, Gdom t ≤ 3 := by
    have hle : ∫ t in {u : ℝ | |u| ≤ 3}, Gdom t
        ≤ ∫ t in {u : ℝ | |u| ≤ 3}, (1 / 2 : ℝ) :=
      MeasureTheory.setIntegral_mono_on integrable_Gdom.integrableOn
        (integrableOn_const (C := (1 / 2 : ℝ)) hvol (by norm_num)) hmem
        (fun t _ => Gdom_le_half t)
    have hval : ∫ t in {u : ℝ | |u| ≤ 3}, (1 / 2 : ℝ) = 3 := by
      have hset : {u : ℝ | |u| ≤ 3} = Set.Icc (-3) 3 := by ext u; simp [abs_le]
      rw [hset, setIntegral_const, Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 - -3)]
      norm_num
    linarith
  have h2 : ∫ t in {u : ℝ | 3 < |u|}, Gdom t ≤ 8 / 3 := by
    obtain ⟨-, -, hint, hval⟩ := div_sq_abs_ge 3 (by norm_num)
    have hle : ∫ t in {u : ℝ | 3 < |u|}, Gdom t
        ≤ ∫ t in {u : ℝ | 3 < |u|}, 4 / t ^ 2 :=
      MeasureTheory.setIntegral_mono_on integrable_Gdom.integrableOn hint
        (by measurability) (fun t _ => Gdom_le_div_sq t)
    linarith
  rw [← MeasureTheory.integral_add_compl hmem integrable_Gdom, hcompl]
  linarith

/-- Exterior bound for `Fdom`: `∫_{|t| ≥ s} Fdom ≤ 8/s` for `s > 0`. -/
theorem Fdom_tail (s : ℝ) (hs : 0 < s) :
    ∫ t in {u : ℝ | s ≤ |u|}, Fdom t ≤ 8 / s := by
  obtain ⟨hint, hval, -, -⟩ := div_sq_abs_ge s hs
  have hmono := MeasureTheory.setIntegral_mono_on (integrable_Fdom.integrableOn) hint
    (by measurability : MeasurableSet {u : ℝ | s ≤ |u|}) (fun t _ => Fdom_le_div_sq t)
  linarith [hmono, hval]

/-- Exterior bound for `Gdom`: `∫_{|t| ≥ s} Gdom ≤ 8/s` for `s > 0`. -/
theorem Gdom_tail (s : ℝ) (hs : 0 < s) :
    ∫ t in {u : ℝ | s ≤ |u|}, Gdom t ≤ 8 / s := by
  obtain ⟨hint, hval, -, -⟩ := div_sq_abs_ge s hs
  have hmono := MeasureTheory.setIntegral_mono_on (integrable_Gdom.integrableOn) hint
    (by measurability : MeasurableSet {u : ℝ | s ≤ |u|}) (fun t _ => Gdom_le_div_sq t)
  linarith [hmono, hval]

theorem dom_bounds :
    MeasureTheory.Integrable Fdom ∧ (∫ t : ℝ, Fdom t = 8) ∧
    (∀ s : ℝ, 0 < s → ∫ t in {u : ℝ | s ≤ |u|}, Fdom t ≤ 8 / s) ∧
    MeasureTheory.Integrable Gdom ∧ (∫ t : ℝ, Gdom t ≤ 6) ∧
    (∀ s : ℝ, 0 < s → ∫ t in {u : ℝ | s ≤ |u|}, Gdom t ≤ 8 / s) :=
  ⟨integrable_Fdom, integral_Fdom, Fdom_tail, integrable_Gdom, integral_Gdom_le_six,
    Gdom_tail⟩

end Work.BoseKinLoc.Momentum
