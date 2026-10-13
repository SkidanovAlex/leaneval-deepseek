import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllExist

namespace Work.FTS.PhiStar.Honesty.DiffGreen

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  rw [abs_mul]
  linarith [h, sq_abs a, sq_abs b]

/-- The pure power `t ↦ t^e` is a.e. strongly measurable against the restriction of Lebesgue
measure to any subset of `(0,∞)`. -/
private lemma aesm_rpow {s : Set ℝ} (hs : s ⊆ Set.Ioi 0) (e : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ e) (MeasureTheory.volume.restrict s) :=
  ((ContinuousOn.rpow_const continuousOn_id
      (fun _ hx => Or.inl (ne_of_gt hx))).aestronglyMeasurable measurableSet_Ioi).mono_measure
    (Measure.restrict_mono hs le_rfl)

/-- A product of an a.e. strongly measurable function (on `(0,∞)`) with a pure power is a.e.
strongly measurable against the restriction to a subset of `(0,∞)`. -/
private lemma aesm_mul_rpow {f : ℝ → ℝ} {s : Set ℝ} (hs : s ⊆ Set.Ioi 0) {e : ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => f t * t ^ e)
      (MeasureTheory.volume.restrict s) :=
  (hf.mono_measure (Measure.restrict_mono hs le_rfl)).mul (aesm_rpow hs e)

/-- The integrand `c t · t^{q-1}` of the forward primitive is integrable on `(0,z]` as soon as
`c²` is integrable on `(0,∞)` and `1 ≤ q` (so that `t^{q-1}` is bounded by `z^{q-1}` there). -/
private lemma rgF1_integrableOn_Ioc {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hq : 1 ≤ rgQ α m) (hz : 0 < z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (rgF1 α m c) (Set.Ioc 0 z) := by
  have he0 : 0 ≤ rgQ α m - 1 := by linarith
  have hC0 : 0 ≤ z ^ (rgQ α m - 1) := Real.rpow_nonneg hz.le _
  have hdom : Integrable (fun t : ℝ => ((c t) ^ 2 + (z ^ (rgQ α m - 1)) ^ 2) / 2)
      (MeasureTheory.volume.restrict (Set.Ioc 0 z)) := by
    have h1 : Integrable (fun t : ℝ => c t ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      hc2.mono_set Set.Ioc_subset_Ioi_self
    have h2 : Integrable (fun _ : ℝ => (z ^ (rgQ α m - 1)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    exact (h1.add h2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    (aesm_mul_rpow Set.Ioc_subset_Ioi_self hc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have hnorm : ‖rgF1 α m c t‖ = |c t| * t ^ (rgQ α m - 1) := by
    simp only [rgF1, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  rw [hnorm]
  have hle : t ^ (rgQ α m - 1) ≤ z ^ (rgQ α m - 1) :=
    Real.rpow_le_rpow ht0.le ht.2 he0
  calc |c t| * t ^ (rgQ α m - 1) ≤ |c t| * z ^ (rgQ α m - 1) :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ ≤ ((c t) ^ 2 + (z ^ (rgQ α m - 1)) ^ 2) / 2 := by
        have h := abs_mul_le_half_sq_add_sq (c t) (z ^ (rgQ α m - 1))
        rwa [abs_mul, abs_of_nonneg hC0] at h

/-- The integrand `c t · t^{-p-1}` of the tail primitive is integrable on `(z,∞)` for `z > 0`
as soon as `c²` is integrable on `(0,∞)` and `0 ≤ p`: AM–GM against `(c² + t^{-2p-2})/2`, whose
two pieces are integrable there (the pure power because `-2p-2 < -1`). -/
private lemma rgF2_integrableOn_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hp : 0 ≤ rgP α m) (hz : 0 < z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi z) := by
  have hdom : Integrable (fun t : ℝ => ((c t) ^ 2 + t ^ (-(2 * rgP α m) - 2)) / 2)
      (MeasureTheory.volume.restrict (Set.Ioi z)) := by
    have h1 : Integrable (fun t : ℝ => c t ^ 2) (MeasureTheory.volume.restrict (Set.Ioi z)) :=
      hc2.mono_set (Set.Ioi_subset_Ioi hz.le)
    have h2 : Integrable (fun t : ℝ => t ^ (-(2 * rgP α m) - 2))
        (MeasureTheory.volume.restrict (Set.Ioi z)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hz
    exact (h1.add h2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    (aesm_mul_rpow (Set.Ioi_subset_Ioi hz.le) hc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans hz ht
  have hnorm : ‖rgF2 α m c t‖ = |c t| * t ^ (-(rgP α m) - 1) := by
    simp only [rgF2, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  rw [hnorm]
  have hsq : (t ^ (-(rgP α m) - 1)) ^ 2 = t ^ (-(2 * rgP α m) - 2) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht0.le]
    congr 1
    ring
  calc |c t| * t ^ (-(rgP α m) - 1)
      = |c t * t ^ (-(rgP α m) - 1)| := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    _ ≤ ((c t) ^ 2 + (t ^ (-(rgP α m) - 1)) ^ 2) / 2 := abs_mul_le_half_sq_add_sq _ _
    _ = ((c t) ^ 2 + t ^ (-(2 * rgP α m) - 2)) / 2 := by rw [hsq]

/-- **Additivity of `radGreen` in the source.**  For `0 < α ≤ 1/4`, `m : ℕ`, `z > 0` and two
a.e.-strongly-measurable `L²((0,∞))` sources `c`, `c'`,

  `radGreen α m (c' - c) z = radGreen α m c' z - radGreen α m c z`.

Both Green integrals are honest under these hypotheses: on `(0,z)` the integrand
`t ↦ c t · t^{q-1}` (`q = (2m+5)/α ≥ 20`) is dominated by `(c t² + t^{2q-2})/2` with
`2q-2 > -1`, and on `(z,∞)` the integrand `t ↦ c t · t^{-p-1}` (`p = 2m/α ≥ 0`) is dominated by
`(c t² + t^{-2p-2})/2` with `2p+2 > 1`; `L²` controls `∫ c²` on both pieces by AM–GM, so the
interval/set integrals are additive in the source.  The named pieces `rgK`, `rgQ`, `rgP`, `rgA`,
`rgB`, `rgF1`, `rgF2` of `Work.FTS.EllExist.RadGreenDefs` and the identity
`Work.FTS.EllExist.radGreen_eq` are available. -/
theorem radGreen_sub {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c c' : ℝ → ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc' : MeasureTheory.AEStronglyMeasurable c' (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0))
    (hc'2 : MeasureTheory.IntegrableOn (fun t : ℝ => c' t ^ 2) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun t => c' t - c t) z
      = Work.FTS.PhiStar.Radial.radGreen α m c' z
        - Work.FTS.PhiStar.Radial.radGreen α m c z := by
  have hq1 : 1 ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, le_div_iff₀ hα]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hp0 : 0 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  -- the difference of the sources is again a.e. strongly measurable with integrable square
  have hsub_aesm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c' t - c t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hc'.sub hc
  have hsub2 : MeasureTheory.IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2) (Set.Ioi 0) := by
    have hdom : Integrable (fun t : ℝ => 2 * ((c' t) ^ 2 + (c t) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := (hc'2.add hc2).const_mul 2
    refine MeasureTheory.Integrable.mono' hdom (hsub_aesm.pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (c' t + c t)]
  -- the two integrands are additive in the source
  have hF1 : ∀ t : ℝ,
      Work.FTS.EllExist.rgF1 α m (fun s => c' s - c s) t
        = Work.FTS.EllExist.rgF1 α m c' t - Work.FTS.EllExist.rgF1 α m c t := by
    intro t
    simp only [Work.FTS.EllExist.rgF1]
    ring
  have hF2 : ∀ t : ℝ,
      Work.FTS.EllExist.rgF2 α m (fun s => c' s - c s) t
        = Work.FTS.EllExist.rgF2 α m c' t - Work.FTS.EllExist.rgF2 α m c t := by
    intro t
    simp only [Work.FTS.EllExist.rgF2]
    ring
  -- additivity of the forward interval integral
  have hA : Work.FTS.EllExist.rgA α m (fun t => c' t - c t) z
      = Work.FTS.EllExist.rgA α m c' z - Work.FTS.EllExist.rgA α m c z := by
    have hInt1 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c') volume 0 z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
      exact rgF1_integrableOn_Ioc hq1 hz hc' hc'2
    have hInt2 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume 0 z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
      exact rgF1_integrableOn_Ioc hq1 hz hc hc2
    simp only [Work.FTS.EllExist.rgA, hF1]
    exact intervalIntegral.integral_sub hInt1 hInt2
  -- additivity of the tail set integral
  have hB : Work.FTS.EllExist.rgB α m (fun t => c' t - c t) z
      = Work.FTS.EllExist.rgB α m c' z - Work.FTS.EllExist.rgB α m c z := by
    simp only [Work.FTS.EllExist.rgB, hF2]
    rw [MeasureTheory.integral_sub (rgF2_integrableOn_Ioi hp0 hz hc' hc'2)
      (rgF2_integrableOn_Ioi hp0 hz hc hc2)]
  rw [Work.FTS.EllExist.radGreen_eq, Work.FTS.EllExist.radGreen_eq,
    Work.FTS.EllExist.radGreen_eq, hA, hB]
  ring

end Work.FTS.PhiStar.Honesty.DiffGreen
