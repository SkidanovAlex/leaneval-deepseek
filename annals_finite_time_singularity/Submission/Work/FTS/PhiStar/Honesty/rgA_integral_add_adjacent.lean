/-
# `Work.FTS.PhiStar.Honesty.rgA_integral_add_adjacent`

The forward primitive `rgA α m c z = ∫_0^z c t · t^{q-1} dt` (`q = rgQ α m = (2m+5)/α ≥ 28`)
splits at the unit point:

  `rgA α m c z = ∫_0^1 rgF1 + ∫_1^z rgF1`   for `z ≥ 1`.

`intervalIntegral.integral_add_adjacent_intervals` only applies when the integrand is interval
integrable on **both** pieces, so the real content is the integrability of `rgF1 α m c t =
c t · t^{q-1}` on `(0,1]` and on `(1,z]` — without it the Bochner integral of a non-integrable
function is `0` and the identity can genuinely fail.

* On `(0,1]`: `0 ≤ q - 1`, so `t^{q-1} ≤ 1` and `|rgF1 t| ≤ |c t| ≤ (c t)²/2 + 1/2`; the
  near-field hypothesis `∫_{(0,1)} (c t)²/t⁴ < ∞` gives `c² ∈ L¹(0,1)` because `t⁴ ≤ 1` there.
* On `(1,z]`: `t^{q-1} ≤ z^{q-1}` and `|rgF1 t| ≤ z^{q-1}·((c t)²/2 + 1/2)`; now the far-field
  hypothesis `∫_{(1,∞)} (c t)² < ∞` restricted to `(1,z]` supplies the `c²` piece (and the
  constant `z^{q-1}/2` is integrable on the bounded interval).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.rgHonest_aemeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- AM–GM in the form `|y| ≤ y²/2 + 1/2`. -/
private lemma abs_le_half_sq_add_half (y : ℝ) : |y| ≤ y ^ 2 / 2 + 1 / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- **`c² ∈ L¹(0,1)`.**  On `(0,1)` one has `t⁴ ≤ 1`, hence `(c t)² ≤ (c t)²/t⁴`, so the
near-field hypothesis dominates `c²` pointwise on `(0,1)`. -/
private lemma integrableOn_sq_near {c : ℝ → ℝ}
    (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1)) :
    IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioo 0 1) := by
  have hc2 : AEMeasurable (fun t : ℝ => (c t) ^ 2) volume := hc.pow_const 2
  refine Integrable.mono' hnear.norm
    (hc2.restrict (s := Ioo (0 : ℝ) 1)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have ht4pos : (0 : ℝ) < t ^ 4 := by positivity
  have ht4le : t ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1.le
  have hle : (c t) ^ 2 * t ^ 4 ≤ (c t) ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left ht4le (sq_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (c t)),
    abs_of_nonneg (div_nonneg (sq_nonneg (c t)) ht4pos.le)]
  rw [le_div_iff₀ ht4pos]
  simpa using hle

/-- **`rgF1` is interval integrable on `(0,1]`.**  The weight `t^{q-1}` is bounded by `1` on the
unit interval (`q ≥ 28`), so `rgF1` is dominated by `(c t)²/2 + 1/2`, whose two pieces are
integrable on `(0,1]` by `integrableOn_sq_near` and by the integrability of constants. -/
private lemma rgF1_integrableOn_Ioc_zero_one {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1)) :
    IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Ioc (0 : ℝ) 1) := by
  have hq : (0 : ℝ) ≤ Work.FTS.EllExist.rgQ α m - 1 := by
    have h := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have hpow_cont : Continuous (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) :=
    Real.continuous_rpow_const hq
  have hF_aem : AEMeasurable
      (fun t : ℝ => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume :=
    hc.mul hpow_cont.aemeasurable
  -- `c² ∈ L¹(0,1]`
  have hcsq : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioc (0 : ℝ) 1) :=
    (integrableOn_sq_near hc hnear).congr_set_ae
      (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1)).symm
  -- constants are integrable on the bounded interval
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) := by
    have h : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  have hmaj : IntegrableOn (fun t : ℝ => (c t) ^ 2 / 2 + 1 / 2) (Ioc (0 : ℝ) 1) :=
    (hcsq.div_const 2).add (hconst.div_const 2)
  refine Integrable.mono' hmaj
    (hF_aem.restrict (s := Ioc (0 : ℝ) 1)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hpt : t ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ 1 :=
    Real.rpow_le_one (le_of_lt ht0) ht1 hq
  rw [Work.FTS.EllExist.rgF1, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
  calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
      ≤ |c t| * 1 := mul_le_mul_of_nonneg_left hpt (abs_nonneg _)
    _ = |c t| := mul_one _
    _ ≤ (c t) ^ 2 / 2 + 1 / 2 := abs_le_half_sq_add_half _

/-- **`rgF1` is interval integrable on `(1,z]` for `z ≥ 1`.**  On `(1,z]` the weight `t^{q-1}` is
dominated by its value `z^{q-1}` at the right endpoint, so `rgF1` is dominated by
`z^{q-1}·((c t)²/2 + 1/2)`; `c²` is controlled by the far-field hypothesis and the constant is
integrable on the bounded interval. -/
private lemma rgF1_integrableOn_Ioc_one {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi 1)) (hz : 1 ≤ z) :
    IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Ioc (1 : ℝ) z) := by
  have hq : (0 : ℝ) ≤ Work.FTS.EllExist.rgQ α m - 1 := by
    have h := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have hpow_cont : Continuous (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) :=
    Real.continuous_rpow_const hq
  have hF_aem : AEMeasurable
      (fun t : ℝ => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume :=
    hc.mul hpow_cont.aemeasurable
  have hcsq : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioc (1 : ℝ) z) :=
    hfar.mono_set (Set.Ioc_subset_Ioi_self : Ioc (1 : ℝ) z ⊆ Ioi (1 : ℝ))
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (1 : ℝ) z) := by
    have h : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (1 : ℝ) z :=
      intervalIntegrable_const
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hz] at h
  have hmaj : IntegrableOn
      (fun t : ℝ => z ^ (Work.FTS.EllExist.rgQ α m - 1) * ((c t) ^ 2 / 2 + 1 / 2))
      (Ioc (1 : ℝ) z) :=
    ((hcsq.div_const 2).add (hconst.div_const 2)).const_mul _
  refine Integrable.mono' hmaj
    (hF_aem.restrict (s := Ioc (1 : ℝ) z)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht1, htz⟩ := ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hz0 : (0 : ℝ) ≤ z := by linarith
  have hpt : t ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
    Real.rpow_le_rpow ht0.le htz hq
  have hznn : (0 : ℝ) ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) := Real.rpow_nonneg hz0 _
  rw [Work.FTS.EllExist.rgF1, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
      ≤ |c t| * z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
        mul_le_mul_of_nonneg_left hpt (abs_nonneg _)
    _ = z ^ (Work.FTS.EllExist.rgQ α m - 1) * |c t| := by ring
    _ ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) * ((c t) ^ 2 / 2 + 1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_le_half_sq_add_half _) hznn

theorem rgA_integral_add_adjacent {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 ≤ z →
      Work.FTS.EllExist.rgA α m c z
        = (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t)
          + ∫ t in (1 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t := by
  intro z hz
  have h0 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (rgF1_integrableOn_Ioc_zero_one hα hα4 hm hc hnear)
  have h1 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (1 : ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz).mpr
      (rgF1_integrableOn_Ioc_one hα hα4 hm hc hfar hz)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0 h1
  show (∫ t in (0 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t)
      = (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t)
        + ∫ t in (1 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t
  exact hadd.symm

end Work.FTS.PhiStar.Honesty
