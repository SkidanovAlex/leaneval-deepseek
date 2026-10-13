import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.remov.coerc.weak_poincare_second

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Interval

namespace Work.FTS.EllipticEst.Honest.PthCore

/-- **Fundamental theorem of calculus between two interior points.**  If `g` has derivative `g'`
on the open interval `(a,b)`, and `g'` is integrable on `[a,b]`, then for any two interior points
`p, q ∈ (a,b)` the increment of `g` is the interval integral of `g'` — note that no endpoint
regularity of `g` (or of `g'`) is assumed. -/
lemma sub_eq_intervalIntegral_Ioo {a b : ℝ} {g g' : ℝ → ℝ}
    (hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hg' : IntegrableOn g' (Set.Icc a b) volume)
    {p q : ℝ} (hp : p ∈ Set.Ioo a b) (hq : q ∈ Set.Ioo a b) :
    g q - g p = ∫ t in p..q, g' t := by
  have hmem : ∀ t ∈ Set.uIcc p q, t ∈ Set.Ioo a b := by
    intro t ht
    rcases le_total p q with hpq | hqp
    · rw [Set.uIcc_of_le hpq] at ht
      exact ⟨lt_of_lt_of_le hp.1 ht.1, lt_of_le_of_lt ht.2 hq.2⟩
    · rw [Set.uIcc_of_ge hqp] at ht
      exact ⟨lt_of_lt_of_le hq.1 ht.1, lt_of_le_of_lt ht.2 hp.2⟩
  have hint : IntervalIntegrable g' volume p q := by
    rcases le_total p q with hpq | hqp
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mpr
        (hg'.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hp.1.le hq.2.le)))
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hqp).mpr
        (hg'.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hq.1.le hp.2.le)))).symm
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hdiff t (hmem t ht)) hint).symm

/-- **Zero-mean sup bound.**  If `f` has derivative `f'` on the open interval `(a,b)`, both `f`
and `f'` are integrable on `[a,b]`, and `f` has vanishing mean, then every interior value of `f`
is bounded by `∫_a^b |f'|`.  This is the elementary "mean-zero Poincaré" sup estimate obtained
from `f x = (b-a)⁻¹ ∫_a^b (f x - f y) dy` and the interior fundamental theorem of calculus. -/
lemma mean_zero_sup_bound {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f volume a b)
    (hi' : IntervalIntegrable f' volume a b)
    (hmean : (∫ x in a..b, f x) = 0) :
    ∀ x ∈ Set.Ioo a b, |f x| ≤ ∫ t in a..b, |f' t| := by
  intro x hx
  set K : ℝ := ∫ t in a..b, |f' t| with hK
  have hfIcc : IntegrableOn f (Set.Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hi
  have hf'Icc : IntegrableOn f' (Set.Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hi'
  have hfIoo : Integrable f (volume.restrict (Set.Ioo a b)) :=
    hfIcc.mono_set Set.Ioo_subset_Icc_self
  have hIoo_zero : (∫ y in Set.Ioo a b, f y) = 0 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    exact hmean
  have hconst_int : Integrable (fun _ : ℝ => f x) (volume.restrict (Set.Ioo a b)) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo a b) (μ := volume) (C := f x)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hsplit : (∫ y in Set.Ioo a b, (f x - f y))
      = (∫ y in Set.Ioo a b, f x) - ∫ y in Set.Ioo a b, f y :=
    integral_sub hconst_int hfIoo
  have hcval : (∫ y in Set.Ioo a b, f x) = volume.real (Set.Ioo a b) * f x := by
    rw [setIntegral_const, smul_eq_mul]
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hkey : (b - a) * f x = ∫ y in Set.Ioo a b, (f x - f y) := by
    rw [hsplit, hcval, hIoo_zero, sub_zero, Real.volume_real_Ioo_of_le hab.le]
  have habs_g' : IntegrableOn (fun t => |f' t|) (Set.Icc a b) volume := hf'Icc.abs
  have hint0 : IntervalIntegrable (fun t => |f' t|) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
      (habs_g'.mono_set Set.Ioc_subset_Icc_self)
  have hpt : ∀ y ∈ Set.Ioo a b, |f x - f y| ≤ K := by
    intro y hy
    rcases le_total y x with hyx | hxy
    · have hsub : f x - f y = ∫ t in y..x, f' t := sub_eq_intervalIntegral_Ioo hd hf'Icc hy hx
      have habs : |∫ t in y..x, f' t| ≤ ∫ t in y..x, |f' t| :=
        intervalIntegral.abs_integral_le_integral_abs (f := fun t => f' t) hyx
      have hmono : (∫ t in y..x, |f' t|) ≤ K := by
        rw [hK]
        exact intervalIntegral.integral_mono_interval hy.1.le hyx hx.2.le
          (Filter.Eventually.of_forall (fun t => abs_nonneg (f' t))) hint0
      calc |f x - f y| = |∫ t in y..x, f' t| := by rw [hsub]
        _ ≤ ∫ t in y..x, |f' t| := habs
        _ ≤ K := hmono
    · have hsub : f y - f x = ∫ t in x..y, f' t := sub_eq_intervalIntegral_Ioo hd hf'Icc hx hy
      have habs : |∫ t in x..y, f' t| ≤ ∫ t in x..y, |f' t| :=
        intervalIntegral.abs_integral_le_integral_abs (f := fun t => f' t) hxy
      have hmono : (∫ t in x..y, |f' t|) ≤ K := by
        rw [hK]
        exact intervalIntegral.integral_mono_interval hx.1.le hxy hy.2.le
          (Filter.Eventually.of_forall (fun t => abs_nonneg (f' t))) hint0
      calc |f x - f y| = |f y - f x| := abs_sub_comm _ _
        _ = |∫ t in x..y, f' t| := by rw [hsub]
        _ ≤ ∫ t in x..y, |f' t| := habs
        _ ≤ K := hmono
  have hae : ∀ᵐ y ∂(volume.restrict (Set.Ioo a b)), |f x - f y| ≤ K :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall (fun y hy => hpt y hy))
  have hgcont : ContinuousOn (fun y => f y) (Set.Ioo a b) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hAESM : AEStronglyMeasurable (fun y => |f x - f y|)
      (volume.restrict (Set.Ioo a b)) :=
    ((continuousOn_const.sub hgcont).abs).aestronglyMeasurable measurableSet_Ioo
  have hInt : Integrable (fun _ : ℝ => K) (volume.restrict (Set.Ioo a b)) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo a b) (μ := volume) (C := K)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hbd : ∀ᵐ y ∂(volume.restrict (Set.Ioo a b)), ‖|f x - f y|‖ ≤ K :=
    hae.mono (fun y hy => by rw [Real.norm_eq_abs, abs_abs]; exact hy)
  have hIntf : Integrable (fun y => |f x - f y|) (volume.restrict (Set.Ioo a b)) :=
    Integrable.mono' hInt hAESM hbd
  have hintegrable := MeasureTheory.integral_mono_ae hIntf hInt hae
  have hval : (∫ y in Set.Ioo a b, K) = volume.real (Set.Ioo a b) * K := by
    rw [setIntegral_const, smul_eq_mul]
  have hfin : (∫ y in Set.Ioo a b, |f x - f y|) ≤ (b - a) * K := by
    rw [hval, Real.volume_real_Ioo_of_le hab.le] at hintegrable
    linarith
  have hnorm : |∫ y in Set.Ioo a b, (f x - f y)| ≤ ∫ y in Set.Ioo a b, |f x - f y| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioo a b)) (fun y : ℝ => f x - f y))
  have hLabs : (b - a) * |f x| = |(b - a) * f x| := by
    rw [abs_mul, abs_of_pos hpos]
  have hchain : (b - a) * |f x| ≤ (b - a) * K := by
    rw [hLabs, hkey]
    exact hnorm.trans hfin
  have hfin2 : |f x| ≤ K := le_of_mul_le_mul_left hchain hpos
  have hgoal : |f x| ≤ ∫ t in a..b, |f' t| := by
    rw [← hK]
    exact hfin2
  exact hgoal

/-- **Sup-to-integral step.**  If `f²` is interval integrable on `(a,b)` and `|f| ≤ K` on the
open interval, then `∫_a^b f² ≤ (b-a) K²`. -/
lemma integral_sq_le_of_abs_le {f : ℝ → ℝ} {a b K : ℝ} (hab : a < b)
    (hi2 : IntervalIntegrable (fun x => (f x) ^ 2) volume a b)
    (h : ∀ x ∈ Set.Ioo a b, |f x| ≤ K) :
    (∫ x in a..b, (f x) ^ 2) ≤ (b - a) * K ^ 2 := by
  have hKnn : 0 ≤ K := by
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    exact le_trans (abs_nonneg _) (h _ hmid)
  have hpoint : ∀ x ∈ Set.Ioo a b, (f x) ^ 2 ≤ K ^ 2 := by
    intro x hx
    calc (f x) ^ 2 = |f x| ^ 2 := (sq_abs (f x)).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h x hx) 2
  have hconst : IntervalIntegrable (fun _ : ℝ => K ^ 2) volume a b := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hab.le hi2 hconst hpoint
  have hval : (∫ x in a..b, K ^ 2) = (b - a) * K ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rwa [hval] at hmono

theorem mean_zero_poincare {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f MeasureTheory.volume a b)
    (hi2 : IntervalIntegrable (fun x => (f x) ^ 2) MeasureTheory.volume a b)
    (hi' : IntervalIntegrable f' MeasureTheory.volume a b)
    (hi'2 : IntervalIntegrable (fun x => (f' x) ^ 2) MeasureTheory.volume a b)
    (hmean : (∫ x in a..b, f x) = 0) :
    (∫ x in a..b, (f x) ^ 2) ≤ (b - a) ^ 2 * (∫ x in a..b, (f' x) ^ 2) := by
  have hsup : ∀ x ∈ Set.Ioo a b, |f x| ≤ ∫ t in a..b, |f' t| :=
    mean_zero_sup_bound hab hd hi hi' hmean
  have hstep1 : (∫ x in a..b, (f x) ^ 2) ≤ (b - a) * (∫ t in a..b, |f' t|) ^ 2 :=
    integral_sq_le_of_abs_le hab hi2 hsup
  have h1 : IntervalIntegrable (fun t => |f' t|) volume a b := hi'.abs
  have h2 : IntervalIntegrable (fun t => (|f' t|) ^ 2) volume a b := by
    have e : (fun t => (|f' t|) ^ 2) = (fun t => (f' t) ^ 2) := by
      funext t
      rw [sq_abs]
    rw [e]
    exact hi'2
  have hcs := Work.FTS.EllipticEst.remov.coerc.sq_intervalIntegral_le hab.le h1 h2
  have hcs' : (∫ t in a..b, |f' t|) ^ 2 ≤ (b - a) * (∫ t in a..b, (f' t) ^ 2) := by
    have e : (∫ t in a..b, (|f' t|) ^ 2) = ∫ t in a..b, (f' t) ^ 2 :=
      intervalIntegral.integral_congr (fun t _ => sq_abs (f' t))
    rwa [e] at hcs
  have hbpos : (0 : ℝ) ≤ b - a := le_of_lt (sub_pos.mpr hab)
  calc (∫ x in a..b, (f x) ^ 2)
      ≤ (b - a) * (∫ t in a..b, |f' t|) ^ 2 := hstep1
    _ ≤ (b - a) * ((b - a) * (∫ t in a..b, (f' t) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs' hbpos
    _ = (b - a) ^ 2 * (∫ t in a..b, (f' t) ^ 2) := by ring

end Work.FTS.EllipticEst.Honest.PthCore
