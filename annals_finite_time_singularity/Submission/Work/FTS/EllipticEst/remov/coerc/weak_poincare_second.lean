import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Interval

namespace Work.FTS.EllipticEst.remov.coerc

/-! ## Cauchy–Schwarz for interval integrals -/

lemma sq_intervalIntegral_le {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume p q)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume p q) :
    (∫ t in p..q, f t) ^ 2 ≤ (q - p) * (∫ t in p..q, (f t) ^ 2) := by
  have hm : Integrable f (volume.restrict (Set.Ioc p q)) := hf.1
  have hm2 : Integrable (fun t => (f t) ^ 2) (volume.restrict (Set.Ioc p q)) := hf2.1
  have hmem : MemLp f 2 (volume.restrict (Set.Ioc p q)) :=
    (memLp_two_iff_integrable_sq hm.1).2 hm2
  have hm1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc p q)) :=
    (intervalIntegrable_const (μ := volume) (a := p) (b := q) (c := (1 : ℝ))).1
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc p q)) :=
    (memLp_two_iff_integrable_sq
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.Ioc p q)))).2 (by simpa only [one_pow] using hm1)
  have hcs := Work.Spaces.cs_integral hmem hmem1
  have hfun : (fun x : ℝ => f x * 1) = f := by
    funext x
    rw [mul_one]
  have h1 : (∫ x in Set.Ioc p q, f x * 1) = ∫ x in p..q, f x := by
    rw [hfun]
    exact (intervalIntegral.integral_of_le hpq).symm
  have h2 : (∫ x in Set.Ioc p q, f x ^ 2) = ∫ x in p..q, (f x) ^ 2 :=
    (intervalIntegral.integral_of_le hpq).symm
  have h3 : (∫ x in Set.Ioc p q, (1 : ℝ) ^ 2) = q - p := by
    rw [show (fun x : ℝ => (1 : ℝ) ^ 2) = (fun _ => (1 : ℝ)) by funext x; norm_num]
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc_of_le hpq]
  rw [h1, h2, h3] at hcs
  exact hcs.trans (le_of_eq (mul_comm (∫ x in p..q, (f x) ^ 2) (q - p)))

/-! ## Integrability of a function with integrable square -/

lemma integrableOn_of_integrableOn_sq {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 L))
    (hg2 : MeasureTheory.IntegrableOn (fun x => (g x) ^ 2) (Set.Icc 0 L)) :
    MeasureTheory.IntegrableOn g (Set.Icc 0 L) := by
  have hAESM : AEStronglyMeasurable g (volume.restrict (Set.Icc 0 L)) := by
    rw [← Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := L) (μ := volume))]
    exact hg.aestronglyMeasurable measurableSet_Ioo
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Icc 0 L)) :=
    MeasureTheory.integrableOn_const
      (s := Set.Icc (0 : ℝ) L) (μ := volume) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have h2 : Integrable (fun x => 1 + (g x) ^ 2) (volume.restrict (Set.Icc 0 L)) :=
    hconst.add hg2
  refine Integrable.mono' h2 hAESM ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|g x| - 1), sq_abs (g x), abs_nonneg (g x)]

/-! ## The fundamental theorem of calculus up to the singular endpoint `0` -/

lemma intervalIntegrable_deriv_of_sq {L : ℝ} (hL : 0 < L) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ 2 w (Set.Ioo 0 L))
    (hw1 : MeasureTheory.IntegrableOn (fun θ => (deriv w θ) ^ 2) (Set.Icc 0 L)) :
    IntervalIntegrable (deriv w) volume 0 L := by
  have hcw : ContinuousOn (deriv w) (Set.Ioo 0 L) :=
    hw.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hgw : MeasureTheory.IntegrableOn (deriv w) (Set.Icc 0 L) :=
    integrableOn_of_integrableOn_sq hL hcw hw1
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mpr hgw

lemma ftc_left_deriv {L : ℝ} (hL : 0 < L) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ 2 w (Set.Ioo 0 L))
    (hw1 : MeasureTheory.IntegrableOn (fun θ => (deriv w θ) ^ 2) (Set.Icc 0 L))
    (h0 : Filter.Tendsto w (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ x ∈ Set.Ioo 0 L, w x = ∫ θ in (0 : ℝ)..x, deriv w θ := by
  intro x hx
  have hx0 : 0 < x := hx.1
  have hxL : x < L := hx.2
  have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) L := Set.Icc_subset_Icc le_rfl hxL.le
  have hsubI : Set.Ioo (0 : ℝ) x ⊆ Set.Ioo (0 : ℝ) L := Set.Ioo_subset_Ioo le_rfl hxL.le
  have hcw : ContinuousOn (deriv w) (Set.Ioo 0 x) :=
    (hw.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsubI
  have hint : IntervalIntegrable (deriv w) volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx0.le).mpr
      (integrableOn_of_integrableOn_sq hx0 hcw (hw1.mono_set hsub))
  have hd : DifferentiableOn ℝ w (Set.Ioo 0 L) := hw.differentiableOn (by norm_num)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) x, HasDerivAt w (deriv w t) t :=
    fun t ht => (hd.differentiableAt (isOpen_Ioo.mem_nhds (hsubI ht))).hasDerivAt
  have hux : Tendsto w (nhdsWithin x (Set.Iio x)) (nhds (w x)) :=
    ((hd.differentiableAt (isOpen_Ioo.mem_nhds hx)).continuousAt).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx0 hderiv hint h0 hux
  linarith [h]

lemma deriv_integral_eq_zero {L : ℝ} (hL : 0 < L) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ 2 w (Set.Ioo 0 L))
    (hw1 : MeasureTheory.IntegrableOn (fun θ => (deriv w θ) ^ 2) (Set.Icc 0 L))
    (h0 : Filter.Tendsto w (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hL0 : Filter.Tendsto w (nhdsWithin L (Set.Iio L)) (nhds 0)) :
    ∫ θ in (0 : ℝ)..L, deriv w θ = 0 := by
  have hint : IntervalIntegrable (deriv w) volume 0 L :=
    intervalIntegrable_deriv_of_sq hL hw hw1
  have hd : DifferentiableOn ℝ w (Set.Ioo 0 L) := hw.differentiableOn (by norm_num)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) L, HasDerivAt w (deriv w t) t :=
    fun t ht => (hd.differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hL hderiv hint h0 hL0
  simpa using h

/-! ## FTC between two interior points -/

lemma sub_eq_intervalIntegral {L : ℝ} {g g' : ℝ → ℝ}
    (hdiff : ∀ x ∈ Set.Ioo 0 L, HasDerivAt g (g' x) x)
    (hg' : MeasureTheory.IntegrableOn g' (Set.Icc 0 L))
    {p q : ℝ} (hp : p ∈ Set.Ioo 0 L) (hq : q ∈ Set.Ioo 0 L) :
    g q - g p = ∫ t in p..q, g' t := by
  have hmem : ∀ t ∈ Set.uIcc p q, t ∈ Set.Ioo 0 L := by
    intro t ht
    rcases le_total p q with hpq | hqp
    · rw [Set.uIcc_of_le hpq] at ht
      exact ⟨lt_of_lt_of_le hp.1 ht.1, lt_of_le_of_lt ht.2 hq.2⟩
    · rw [Set.uIcc_of_ge hqp] at ht
      exact ⟨lt_of_lt_of_le hq.1 ht.1, lt_of_le_of_lt ht.2 hp.2⟩
  have hint : IntervalIntegrable g' volume p q := by
    rcases le_total p q with hpq | hqp
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mpr
        (hg'.mono_set (Set.Ioc_subset_Icc_self.trans
          (Set.Icc_subset_Icc hp.1.le hq.2.le)))
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hqp).mpr
        (hg'.mono_set (Set.Ioc_subset_Icc_self.trans
          (Set.Icc_subset_Icc hq.1.le hp.2.le)))).symm
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hdiff t (hmem t ht)) hint).symm

/-! ## Mean-zero Poincaré bound (sup form) -/

lemma abs_le_integral_abs_deriv_of_mean_zero {L : ℝ} (hL : 0 < L) {g g' : ℝ → ℝ}
    (hdiff : ∀ x ∈ Set.Ioo 0 L, HasDerivAt g (g' x) x)
    (hg : MeasureTheory.IntegrableOn g (Set.Icc 0 L))
    (hg' : MeasureTheory.IntegrableOn g' (Set.Icc 0 L))
    (hmean : ∫ x in (0 : ℝ)..L, g x = 0) :
    ∀ x ∈ Set.Ioo 0 L, |g x| ≤ ∫ x in (0 : ℝ)..L, |g' x| := by
  intro x hx
  set K : ℝ := ∫ t in (0 : ℝ)..L, |g' t| with hK
  have hgIoo : Integrable (fun y => g y) (volume.restrict (Set.Ioo 0 L)) :=
    hg.mono_set (Set.Ioo_subset_Icc_self)
  have hIoo_zero : (∫ y in Set.Ioo 0 L, g y) = 0 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL.le]
    exact hmean
  have hconst_int : Integrable (fun _ : ℝ => g x) (volume.restrict (Set.Ioo 0 L)) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) L) (μ := volume) (C := g x)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hsplit : (∫ y in Set.Ioo 0 L, (g x - g y))
      = (∫ y in Set.Ioo 0 L, g x) - ∫ y in Set.Ioo 0 L, g y :=
    integral_sub hconst_int hgIoo
  have hcval : (∫ y in Set.Ioo 0 L, g x) = volume.real (Set.Ioo 0 L) * g x := by
    rw [setIntegral_const, smul_eq_mul]
  have hkey : L * g x = ∫ y in Set.Ioo 0 L, (g x - g y) := by
    rw [hsplit, hcval, hIoo_zero, sub_zero, Real.volume_real_Ioo_of_le hL.le]
    ring
  have habs_g' : MeasureTheory.IntegrableOn (fun t => |g' t|) (Set.Icc 0 L) := hg'.abs
  have hint0 : IntervalIntegrable (fun t => |g' t|) volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).mpr
      (habs_g'.mono_set Set.Ioc_subset_Icc_self)
  have hpt : ∀ y ∈ Set.Ioo (0 : ℝ) L, |g x - g y| ≤ K := by
    intro y hy
    rcases le_total y x with hyx | hxy
    · have hsub : g x - g y = ∫ t in y..x, g' t := sub_eq_intervalIntegral hdiff hg' hy hx
      have habs : |∫ t in y..x, g' t| ≤ ∫ t in y..x, |g' t| :=
        intervalIntegral.abs_integral_le_integral_abs (f := fun t => g' t) hyx
      have hmono : (∫ t in y..x, |g' t|) ≤ K := by
        rw [hK]
        exact intervalIntegral.integral_mono_interval hy.1.le hyx hx.2.le
          (Filter.Eventually.of_forall (fun t => abs_nonneg (g' t))) hint0
      calc |g x - g y| = |∫ t in y..x, g' t| := by rw [hsub]
        _ ≤ ∫ t in y..x, |g' t| := habs
        _ ≤ K := hmono
    · have hsub : g y - g x = ∫ t in x..y, g' t := sub_eq_intervalIntegral hdiff hg' hx hy
      have habs : |∫ t in x..y, g' t| ≤ ∫ t in x..y, |g' t| :=
        intervalIntegral.abs_integral_le_integral_abs (f := fun t => g' t) hxy
      have hmono : (∫ t in x..y, |g' t|) ≤ K := by
        rw [hK]
        exact intervalIntegral.integral_mono_interval hx.1.le hxy hy.2.le
          (Filter.Eventually.of_forall (fun t => abs_nonneg (g' t))) hint0
      calc |g x - g y| = |g y - g x| := abs_sub_comm _ _
        _ = |∫ t in x..y, g' t| := by rw [hsub]
        _ ≤ ∫ t in x..y, |g' t| := habs
        _ ≤ K := hmono
  have hae : ∀ᵐ y ∂(volume.restrict (Set.Ioo (0 : ℝ) L)), |g x - g y| ≤ K :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall (fun y hy => hpt y hy))
  have hgcont : ContinuousOn (fun y => g y) (Set.Ioo 0 L) :=
    fun y hy => (hdiff y hy).continuousAt.continuousWithinAt
  have hAESM : AEStronglyMeasurable (fun y => |g x - g y|)
      (volume.restrict (Set.Ioo 0 L)) :=
    ((continuousOn_const.sub hgcont).abs).aestronglyMeasurable measurableSet_Ioo
  have hInt : Integrable (fun _ : ℝ => K) (volume.restrict (Set.Ioo 0 L)) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) L) (μ := volume) (C := K)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hbd : ∀ᵐ y ∂(volume.restrict (Set.Ioo (0 : ℝ) L)), ‖|g x - g y|‖ ≤ K :=
    hae.mono (fun y hy => by rw [Real.norm_eq_abs, abs_abs]; exact hy)
  have hIntf : Integrable (fun y => |g x - g y|) (volume.restrict (Set.Ioo 0 L)) :=
    Integrable.mono' hInt hAESM hbd
  have hintegrable := MeasureTheory.integral_mono_ae hIntf hInt hae
  have hval : (∫ y in Set.Ioo 0 L, K) = volume.real (Set.Ioo 0 L) * K := by
    rw [setIntegral_const, smul_eq_mul]
  have hfin : (∫ y in Set.Ioo 0 L, |g x - g y|) ≤ L * K := by
    rw [hval, Real.volume_real_Ioo_of_le hL.le] at hintegrable
    linarith
  have hnorm : |∫ y in Set.Ioo 0 L, (g x - g y)| ≤ ∫ y in Set.Ioo 0 L, |g x - g y| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioo (0 : ℝ) L)) (fun y : ℝ => g x - g y))
  have hLabs : L * |g x| = |L * g x| := by rw [abs_mul, abs_of_pos hL]
  have hchain : L * |g x| ≤ L * K := by
    rw [hLabs, hkey]
    exact hnorm.trans hfin
  have hfin2 : |g x| ≤ K := le_of_mul_le_mul_left hchain hL
  rwa [hK] at hfin2

/-! ## The Poincaré inequality -/

theorem weak_poincare_second {w : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hw : ContDiffOn ℝ 2 w (Set.Ioo 0 L))
    (hw1 : MeasureTheory.IntegrableOn (fun θ => (deriv w θ) ^ 2) (Set.Icc 0 L))
    (hw2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv w t) θ) ^ 2) (Set.Icc 0 L))
    (h0 : Filter.Tendsto w (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hL0 : Filter.Tendsto w (nhdsWithin L (Set.Iio L)) (nhds 0)) :
    (∫ θ in Set.Icc 0 L, (w θ) ^ 2) + (∫ θ in Set.Icc 0 L, (deriv w θ) ^ 2)
      ≤ (L ^ 2 + L ^ 4) * (∫ θ in Set.Icc 0 L, (deriv (fun t => deriv w t) θ) ^ 2) := by
  set B : ℝ := ∫ θ in Set.Icc 0 L, (deriv w θ) ^ 2 with hB
  set C : ℝ := ∫ θ in Set.Icc 0 L, (deriv (fun t => deriv w t) θ) ^ 2 with hC
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact MeasureTheory.integral_nonneg (f := fun θ => (deriv w θ) ^ 2) (fun _ => sq_nonneg _)
  have hIccIoo : ∀ f : ℝ → ℝ, (∫ θ in Set.Icc 0 L, f θ) = ∫ θ in Set.Ioo 0 L, f θ := by
    intro f
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hBiv : B = ∫ θ in (0 : ℝ)..L, (deriv w θ) ^ 2 := by
    rw [hB, hIccIoo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hL.le]
  have hCiv : C = ∫ θ in (0 : ℝ)..L, (deriv (fun t => deriv w t) θ) ^ 2 := by
    rw [hC, hIccIoo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hL.le]
  have hcw : ContinuousOn (deriv w) (Set.Ioo 0 L) :=
    hw.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcw2 : ContinuousOn (deriv (fun t => deriv w t)) (Set.Ioo 0 L) := by
    have h1 : ContDiffOn ℝ 1 (deriv w) (Set.Ioo 0 L) :=
      hw.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hgw : MeasureTheory.IntegrableOn (deriv w) (Set.Icc 0 L) :=
    integrableOn_of_integrableOn_sq hL hcw hw1
  have hgw2 : MeasureTheory.IntegrableOn (deriv (fun t => deriv w t)) (Set.Icc 0 L) :=
    integrableOn_of_integrableOn_sq hL hcw2 hw2
  -- first estimate: `∫ w² ≤ L * ∫ (w')²`
  have hftc := ftc_left_deriv hL hw hw1 h0
  have hint2full : IntervalIntegrable (fun θ => (deriv w θ) ^ 2) volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mpr hw1
  have hptA : ∀ x ∈ Set.Ioo (0 : ℝ) L, (w x) ^ 2 ≤ L * B := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxL : x < L := hx.2
    have hsubIcc : Set.Icc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) L := Set.Icc_subset_Icc le_rfl hxL.le
    have hint1 : IntervalIntegrable (deriv w) volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx0.le).mpr (hgw.mono_set hsubIcc)
    have hint2 : IntervalIntegrable (fun θ => (deriv w θ) ^ 2) volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx0.le).mpr (hw1.mono_set hsubIcc)
    have hcs := sq_intervalIntegral_le hx0.le hint1 hint2
    have hmono : (∫ θ in (0 : ℝ)..x, (deriv w θ) ^ 2) ≤ B := by
      rw [hBiv]
      exact intervalIntegral.integral_mono_interval le_rfl hx0.le hxL.le
        (Filter.Eventually.of_forall (fun θ => sq_nonneg (deriv w θ))) hint2full
    have hwx : w x = ∫ θ in (0 : ℝ)..x, deriv w θ := hftc x hx
    have h1 : (w x) ^ 2 ≤ x * (∫ θ in (0 : ℝ)..x, (deriv w θ) ^ 2) := by
      rw [hwx]
      simpa using hcs
    have h2 : x * (∫ θ in (0 : ℝ)..x, (deriv w θ) ^ 2) ≤ x * B :=
      mul_le_mul_of_nonneg_left hmono hx0.le
    have h3 : x * B ≤ L * B := mul_le_mul_of_nonneg_right hxL.le hBnn
    linarith
  have hA : (∫ θ in Set.Icc 0 L, (w θ) ^ 2) ≤ L ^ 2 * B := by
    rw [hIccIoo]
    have hAESM : AEStronglyMeasurable (fun x => (w x) ^ 2)
        (volume.restrict (Set.Ioo 0 L)) :=
      (hw.continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioo
    have hInt : Integrable (fun _ : ℝ => L * B) (volume.restrict (Set.Ioo 0 L)) :=
      MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) L) (μ := volume) (C := L * B)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hae : (fun x => (w x) ^ 2) ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) L)]
        (fun _ : ℝ => L * B) :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
        (Filter.Eventually.of_forall (fun x hx => hptA x hx))
    have hbd : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) L)), ‖(w x) ^ 2‖ ≤ L * B :=
      hae.mono (fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w x))]
        exact hx)
    have hIntf : Integrable (fun x => (w x) ^ 2) (volume.restrict (Set.Ioo 0 L)) :=
      Integrable.mono' hInt hAESM hbd
    have hmono := MeasureTheory.integral_mono_ae hIntf hInt hae
    have hval : (∫ y in Set.Ioo 0 L, (L * B)) = volume.real (Set.Ioo 0 L) * (L * B) := by
      rw [setIntegral_const, smul_eq_mul]
    calc (∫ y in Set.Ioo 0 L, (w y) ^ 2)
        ≤ ∫ y in Set.Ioo 0 L, (L * B) := hmono
      _ = volume.real (Set.Ioo 0 L) * (L * B) := hval
      _ = L * (L * B) := by rw [Real.volume_real_Ioo_of_le hL.le]; ring
      _ = L ^ 2 * B := by ring
  -- second estimate: `∫ (w')² ≤ L * ∫ (w'')²`
  have habs_int : MeasureTheory.IntegrableOn
      (fun y => |deriv (fun t => deriv w t) y|) (Set.Icc 0 L) := hgw2.abs
  have habs_sq : MeasureTheory.IntegrableOn
      (fun y => (|deriv (fun t => deriv w t) y|) ^ 2) (Set.Icc 0 L) := by
    have e : (fun y => (|deriv (fun t => deriv w t) y|) ^ 2)
        = (fun y => (deriv (fun t => deriv w t) y) ^ 2) := by
      funext y
      rw [sq_abs]
    rw [e]
    exact hw2
  have hptB : ∀ x ∈ Set.Ioo (0 : ℝ) L, (deriv w x) ^ 2 ≤ L * C := by
    intro x hx
    have hdiff : ∀ y ∈ Set.Ioo (0 : ℝ) L,
        HasDerivAt (deriv w) (deriv (fun t => deriv w t) y) y := by
      intro y hy
      have h2 : ContDiffOn ℝ 1 (deriv w) (Set.Ioo 0 L) :=
        hw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact ((h2.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hy)).hasDerivAt
    have hmean : ∫ y in (0 : ℝ)..L, deriv w y = 0 := deriv_integral_eq_zero hL hw hw1 h0 hL0
    have h1 : |deriv w x| ≤ ∫ y in (0 : ℝ)..L, |deriv (fun t => deriv w t) y| :=
      abs_le_integral_abs_deriv_of_mean_zero hL hdiff hgw hgw2 hmean x hx
    have hint1 : IntervalIntegrable (fun y => |deriv (fun t => deriv w t) y|) volume 0 L :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mpr habs_int
    have hint2 : IntervalIntegrable
        (fun y => (|deriv (fun t => deriv w t) y|) ^ 2) volume 0 L :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mpr habs_sq
    have hcs := sq_intervalIntegral_le hL.le hint1 hint2
    have hcs2 : (∫ y in (0 : ℝ)..L, (|deriv (fun t => deriv w t) y|) ^ 2)
        = ∫ y in (0 : ℝ)..L, (deriv (fun t => deriv w t) y) ^ 2 := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      rw [sq_abs]
    have h2 : (∫ y in (0 : ℝ)..L, |deriv (fun t => deriv w t) y|) ^ 2 ≤ L * C := by
      have h := hcs
      rw [hcs2, ← hCiv] at h
      simpa using h
    have h3 : (deriv w x) ^ 2
        ≤ (∫ y in (0 : ℝ)..L, |deriv (fun t => deriv w t) y|) ^ 2 := by
      rw [← sq_abs (deriv w x)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    linarith
  have hBle : B ≤ L ^ 2 * C := by
    have hBIoo : B = ∫ θ in Set.Ioo 0 L, (deriv w θ) ^ 2 := by rw [hB, hIccIoo]
    rw [hBIoo]
    have hAESM : AEStronglyMeasurable (fun x => (deriv w x) ^ 2)
        (volume.restrict (Set.Ioo 0 L)) :=
      (hcw.pow 2).aestronglyMeasurable measurableSet_Ioo
    have hInt : Integrable (fun _ : ℝ => L * C) (volume.restrict (Set.Ioo 0 L)) :=
      MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) L) (μ := volume) (C := L * C)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hae : (fun x => (deriv w x) ^ 2) ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) L)]
        (fun _ : ℝ => L * C) :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
        (Filter.Eventually.of_forall (fun x hx => hptB x hx))
    have hbd : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) L)), ‖(deriv w x) ^ 2‖ ≤ L * C :=
      hae.mono (fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (deriv w x))]
        exact hx)
    have hIntf : Integrable (fun x => (deriv w x) ^ 2) (volume.restrict (Set.Ioo 0 L)) :=
      Integrable.mono' hInt hAESM hbd
    have hmono := MeasureTheory.integral_mono_ae hIntf hInt hae
    have hval : (∫ y in Set.Ioo 0 L, (L * C)) = volume.real (Set.Ioo 0 L) * (L * C) := by
      rw [setIntegral_const, smul_eq_mul]
    calc (∫ y in Set.Ioo 0 L, (deriv w y) ^ 2)
        ≤ ∫ y in Set.Ioo 0 L, (L * C) := hmono
      _ = volume.real (Set.Ioo 0 L) * (L * C) := hval
      _ = L * (L * C) := by rw [Real.volume_real_Ioo_of_le hL.le]; ring
      _ = L ^ 2 * C := by ring
  -- assembly
  rw [hB, hC]
  calc (∫ θ in Set.Icc 0 L, (w θ) ^ 2) + B
      ≤ L ^ 2 * B + B := by linarith
    _ = (L ^ 2 + 1) * B := by ring
    _ ≤ (L ^ 2 + 1) * (L ^ 2 * C) :=
        mul_le_mul_of_nonneg_left hBle (by positivity)
    _ = (L ^ 2 + L ^ 4) * C := by ring

end Work.FTS.EllipticEst.remov.coerc
