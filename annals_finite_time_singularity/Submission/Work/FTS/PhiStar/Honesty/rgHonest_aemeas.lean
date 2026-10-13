import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- AM–GM: `a·b ≤ (a² + b²)/2` for nonnegative `a`, `b`. -/
private lemma mul_le_half_sq_add_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    have h2 : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by
      nlinarith [sq_nonneg (|a| - |b|)]
    rw [abs_mul]
    linarith [h2, sq_abs a, sq_abs b]
  rwa [abs_of_nonneg (mul_nonneg ha hb)] at h

/-- AM–GM in the form `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- A.e. strong measurability of `t ↦ c t · t^r` on a set contained in `(0,∞)`, from
`AEMeasurable c`: the constant power is continuous there. -/
private lemma aestronglyMeasurable_mul_rpow {c : ℝ → ℝ} (hc : AEMeasurable c) {r : ℝ}
    {s : Set ℝ} (hs : s ⊆ Set.Ioi 0) :
    AEStronglyMeasurable (fun t : ℝ => c t * t ^ r) (volume.restrict s) := by
  have h1 : AEStronglyMeasurable c (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hc.aestronglyMeasurable.restrict
  have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ r) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt hx))).aestronglyMeasurable measurableSet_Ioi
  exact (h1.mul h2).mono_set hs

/-- `t ↦ t^r` is continuous on `[0,1]` for `0 ≤ r` (at `0` one uses the exponent). -/
private lemma continuousOn_rpow_Icc_zero {r : ℝ} (hr : 0 ≤ r) :
    ContinuousOn (fun t : ℝ => t ^ r) (Set.Icc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    exact (Real.continuousAt_rpow_const 0 r (Or.inr hr)).continuousWithinAt
  · exact (Real.continuousAt_rpow_const t r (Or.inl (ne_of_gt h))).continuousWithinAt

/-- Honestness of the two Green integrands of the radial Euler Green function
`Work.FTS.PhiStar.Radial.radGreen`, under the weak hypotheses of the corrected
`radGreen_mul_deriv_atTop_zero_meas`.  Here `q = rgQ α m = (2m+5)/α ≥ 28`, `p = rgP α m = 2m/α ≥ 8`,
`rgF1 α m c t = c t · t^{q-1}`, `rgF2 α m c t = c t · t^{-p-1}`.

Both are derived from `(c t)²/t⁴ ∈ L¹(0,1)` and `(c t)² ∈ L¹(1,∞)` together with `AEMeasurable c`
(this last is what supplies a.e. strong measurability; the AM–GM inequality
`|c t| · t^{r} ≤ ((c t)²/t⁴ + t^{2r+4})/2` does the domination, and all the surviving powers are
locally integrable). -/
theorem rgHonest_aemeas {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 0 1)
      ∧ (∀ z : ℝ, 1 ≤ z → IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 1 z))
      ∧ (∀ z : ℝ, 1 ≤ z → IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi z)) := by
  have hq : 28 ≤ Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_ge hα hα4 hm
  have hp : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have hq1 : 0 ≤ Work.FTS.EllExist.rgQ α m - 1 := by linarith
  have hp0 : 0 ≤ Work.FTS.EllExist.rgP α m := by linarith
  -- ### the pointwise AM–GM domination for `rgF1` on `(0,1)`
  have key1 : ∀ t : ℝ, 0 < t →
      ‖Work.FTS.EllExist.rgF1 α m c t‖
        ≤ ((c t) ^ 2 / t ^ 4 + t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4)) / 2 := by
    intro t ht
    have hpow : t ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)
        = t ^ (Work.FTS.EllExist.rgQ α m + 1) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
      congr 1
      ring
    have hmain : ‖Work.FTS.EllExist.rgF1 α m c t‖
        = (|c t| / t ^ 2) * t ^ (Work.FTS.EllExist.rgQ α m + 1) := by
      rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF1, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht.le _), ← hpow]
      field_simp
    rw [hmain]
    have hA := mul_le_half_sq_add_sq (by positivity : (0 : ℝ) ≤ |c t| / t ^ 2)
      (Real.rpow_nonneg ht.le (Work.FTS.EllExist.rgQ α m + 1))
    have hsq1 : (|c t| / t ^ 2) ^ 2 = (c t) ^ 2 / t ^ 4 := by
      rw [div_pow, sq_abs]
      ring
    have hsq2 : (t ^ (Work.FTS.EllExist.rgQ α m + 1)) ^ 2
        = t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1
      ring
    rw [hsq1, hsq2] at hA
    exact hA
  refine ⟨?_, ?_, ?_⟩
  · -- ### `rgF1` on `(0,1]`
    have hnearI : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc 0 1) :=
      hnear.congr_set_ae (Ioo_ae_eq_Ioc).symm
    have hrpowI : IntegrableOn (fun t : ℝ => t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4))
        (Set.Ioc 0 1) :=
      ((continuousOn_rpow_Icc_zero (by linarith)).integrableOn_Icc).mono_set
        Set.Ioc_subset_Icc_self
    have hmaj : Integrable
        (fun t : ℝ => ((c t) ^ 2 / t ^ 4 + t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4)) / 2)
        (volume.restrict (Set.Ioc 0 1)) := (hnearI.add hrpowI).div_const 2
    refine Integrable.mono' hmaj ?_ ?_
    · exact aestronglyMeasurable_mul_rpow hc (s := Set.Ioc 0 1) Set.Ioc_subset_Ioi_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact key1 t ht.1
  · -- ### `rgF1` on `(1,z]`
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have hfarI : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc 1 z) :=
      hfar.mono_set (fun t ht => ht.1)
    have hconstI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 1 z) :=
      continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hmaj : Integrable
        (fun t : ℝ => z ^ (Work.FTS.EllExist.rgQ α m - 1) * (((c t) ^ 2 + 1) / 2))
        (volume.restrict (Set.Ioc 1 z)) :=
      ((hfarI.add hconstI).div_const 2).const_mul (z ^ (Work.FTS.EllExist.rgQ α m - 1))
    refine Integrable.mono' hmaj ?_ ?_
    · exact aestronglyMeasurable_mul_rpow hc (s := Set.Ioc 1 z)
        (fun t ht => lt_trans zero_lt_one ht.1)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      have hbound : |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
          ≤ ((c t) ^ 2 + 1) / 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
        mul_le_mul (abs_le_sq_add_one_div_two (c t))
          (Real.rpow_le_rpow ht0.le ht.2 hq1)
          (Real.rpow_nonneg ht0.le _) (by positivity)
      rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF1, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
          ≤ ((c t) ^ 2 + 1) / 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1) := hbound
        _ = z ^ (Work.FTS.EllExist.rgQ α m - 1) * (((c t) ^ 2 + 1) / 2) := by ring
  · -- ### `rgF2` on `(z,∞)`
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have hmaj : Integrable
        (fun t : ℝ => ((c t) ^ 2 + t ^ (-(2 * Work.FTS.EllExist.rgP α m) - 2)) / 2)
        (volume.restrict (Set.Ioi z)) := by
      have h1 : Integrable (fun t : ℝ => (c t) ^ 2) (volume.restrict (Set.Ioi z)) :=
        hfar.mono_set (fun t ht => lt_of_le_of_lt hz1 ht)
      have h2 : Integrable (fun t : ℝ => t ^ (-(2 * Work.FTS.EllExist.rgP α m) - 2))
          (volume.restrict (Set.Ioi z)) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hz0
      exact (h1.add h2).div_const 2
    refine Integrable.mono' hmaj ?_ ?_
    · exact aestronglyMeasurable_mul_rpow hc (s := Set.Ioi z)
        (fun t ht => lt_trans hz0 ht)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans hz0 ht
      rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF2, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hA := mul_le_half_sq_add_sq (abs_nonneg (c t))
        (Real.rpow_nonneg ht0.le _ :
          (0 : ℝ) ≤ t ^ (-(Work.FTS.EllExist.rgP α m) - 1))
      have hsq : (t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) ^ 2
          = t ^ (-(2 * Work.FTS.EllExist.rgP α m) - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1
        ring
      rw [hsq, sq_abs] at hA
      exact hA

end Work.FTS.PhiStar.Honesty
