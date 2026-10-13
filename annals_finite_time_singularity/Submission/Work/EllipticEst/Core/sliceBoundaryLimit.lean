import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.weightedCS
import Submission.Work.EllipticEst.Core.thEtaFacts
import Submission.Work.EllipticEst.Core.thEtaInvIntegralBounds
import Submission.Work.EllipticEst.Core.tendstoSqBoundLeft
import Submission.Work.EllipticEst.Core.tendstoSqBoundRight
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

-- ===== my helpers =====

/-- FTC on the open interval for a function of class `C¹` there. -/
private lemma sbl_deriv_ftc {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hb : b ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ x in a..b, deriv f x = f b - f a := by
  refine intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hf.mono ?_)
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_lt_of_le ha.1 h1, lt_of_le_of_lt h2 hb.2⟩
  · exact ⟨lt_of_lt_of_le hb.1 h1, lt_of_le_of_lt h2 ha.2⟩

/-- Set integral over `Ioo a b` equals the interval integral, for `a ≤ b`. -/
private lemma sbl_setIntegral_Ioo_eq_intervalIntegral {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Ioo a b, F t) = ∫ t in a..b, F t := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- A set and a superset differing by a finite set are a.e. equal. -/
private lemma sbl_ae_eq_set_of_sdiff_finite {s t : Set ℝ} (h : s ⊆ t) (hfin : (t \ s).Finite) :
    s =ᵐ[MeasureTheory.volume] t := by
  have h0 : MeasureTheory.volume (t \ s) = 0 := Set.Finite.measure_zero hfin MeasureTheory.volume
  have hmem : ∀ᵐ x : ℝ, x ∉ (t \ s) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using h0
  filter_upwards [hmem] with x hx
  exact propext ⟨fun hxs => h hxs, fun hxt => by
    by_contra hxs
    exact hx ⟨hxt, hxs⟩⟩

private lemma sbl_integrableOn_of_ae_eq_set {F : ℝ → ℝ} {s t : Set ℝ}
    (h : s =ᵐ[MeasureTheory.volume] t) (hF : MeasureTheory.IntegrableOn F s) :
    MeasureTheory.IntegrableOn F t := by
  rw [MeasureTheory.IntegrableOn] at hF ⊢
  exact MeasureTheory.Measure.restrict_congr_set h ▸ hF

/-- `IntegrableOn F (Ioo a b)` implies `IntegrableOn F (Ioc a b)`. -/
private lemma sbl_integrableOn_Ioc_of_Ioo {F : ℝ → ℝ} {a b : ℝ}
    (h : MeasureTheory.IntegrableOn F (Set.Ioo a b)) :
    MeasureTheory.IntegrableOn F (Set.Ioc a b) :=
  sbl_integrableOn_of_ae_eq_set
    (sbl_ae_eq_set_of_sdiff_finite (fun x hx => ⟨hx.1, le_of_lt hx.2⟩) (by
      refine Set.Finite.subset (Set.finite_singleton b) ?_
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_singleton_iff]
      by_contra hxb
      exact hx2 ⟨hx1.1, lt_of_le_of_ne hx1.2 hxb⟩)) h

/-- Interval integrability from integrability on the open interval, for `a ≤ b`. -/
private lemma sbl_intervalIntegrable_of_integrableOn_Ioo {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : MeasureTheory.IntegrableOn F (Set.Ioo a b)) : IntervalIntegrable F volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact sbl_integrableOn_Ioc_of_Ioo h

private lemma sbl_setIntegral_nonneg_Ioo {F : ℝ → ℝ} {a b : ℝ}
    (h : ∀ t ∈ Set.Ioo a b, 0 ≤ F t) : 0 ≤ ∫ t in Set.Ioo a b, F t :=
  MeasureTheory.setIntegral_nonneg measurableSet_Ioo h

/-- The angular energy `∫_{(0,θ)} (f')² thEta` is monotone in `θ`. -/
private lemma sbl_energy_mono {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
  refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  · filter_upwards with t ht
    exact ⟨ht.1, lt_trans ht.2 hθ.2⟩

private lemma sbl_energy_mono_right {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
  refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  · filter_upwards with t ht
    exact ⟨lt_trans hθ.1 ht.1, ht.2⟩

theorem sliceBoundaryLimit : ∃ K : ℝ, 0 < K ∧
  ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi/2)) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi/2)) →
    (∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi/2), (f θ - c)^2 ≤ K * θ^(1 + Work.Spaces.eta) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo 0 θ))
          (fun θ' : ℝ => (deriv f θ')^2 * Work.FTS.EllipticEst.thEta θ'))
    ∧ (∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi/2), (f θ - c)^2 ≤ K * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi/2)))
          (fun θ' : ℝ => (deriv f θ')^2 * Work.FTS.EllipticEst.thEta θ')) := by
  refine ⟨2, by norm_num, ?_⟩
  intro f hf hint
  obtain ⟨hth_pos, hth_one, hth_inv, hth_cont⟩ := thEtaFacts
  obtain ⟨hwiL, hbL, hwiR, hbR⟩ := thEtaInvIntegralBounds
  obtain ⟨hsqInt, habsInt, hderivInt⟩ := derivIntegrableOfEnergy f hf hint
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)
  have hpi4 : (Real.pi / 4) ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hInt : ∀ {a b : ℝ}, Set.Ioo a b ⊆ Set.Ioo 0 (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t => deriv f t) (Set.Ioo a b) := by
    intro a b hsub
    refine MeasureTheory.Integrable.mono' (habsInt.mono_set hsub) ?_ ?_
    · exact (hderiv_cont.mono hsub).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards with t using le_of_eq (Real.norm_eq_abs (deriv f t))
  have hII : ∀ {a b : ℝ}, a ≤ b → Set.Ioo a b ⊆ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun t => deriv f t) volume a b :=
    fun hab hsub => sbl_intervalIntegrable_of_integrableOn_Ioo hab (hInt hsub)
  have hA0 : 0 ≤ ∫ t in Set.Ioo 0 (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    sbl_setIntegral_nonneg_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  -- ### Left endpoint
  have hleft : ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (f θ - c)^2 ≤ 2 * θ^(1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
    have hI0 : IntervalIntegrable (fun t => deriv f t) volume (0:ℝ) (Real.pi/4) :=
      hII (by linarith [Real.pi_pos])
        (fun t ht => ⟨ht.1, lt_trans ht.2 (by linarith [Real.pi_pos])⟩)
    set c : ℝ := f (Real.pi/4) - ∫ x in (0:ℝ)..(Real.pi/4), deriv f x with hc
    have hkeyI : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = ∫ x in (0:ℝ)..θ, deriv f x := by
      intro θ hθ
      have h1 : f θ - c
          = (f θ - f (Real.pi/4)) + ∫ x in (0:ℝ)..(Real.pi/4), deriv f x := by
        rw [hc]; ring
      have hftc : f θ - f (Real.pi/4) = ∫ x in (Real.pi/4)..θ, deriv f x :=
        (sbl_deriv_ftc hf hpi4 hθ).symm
      rcases le_total θ (Real.pi/4) with hle | hge
      · have hIθ4 : IntervalIntegrable (fun t => deriv f t) volume θ (Real.pi/4) :=
          hII hle (fun t ht => ⟨lt_trans hθ.1 ht.1, lt_trans ht.2 hpi4.2⟩)
        have hI0θ : IntervalIntegrable (fun t => deriv f t) volume (0:ℝ) θ :=
          hII (le_of_lt hθ.1) (fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩)
        have hsym : (∫ x in (Real.pi/4)..θ, deriv f x) = -(∫ x in θ..(Real.pi/4), deriv f x) :=
          intervalIntegral.integral_symm θ (Real.pi/4)
        have hadd : (∫ x in (0:ℝ)..θ, deriv f x) + (∫ x in θ..(Real.pi/4), deriv f x)
            = ∫ x in (0:ℝ)..(Real.pi/4), deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hI0θ hIθ4
        rw [h1, hftc, hsym]
        linarith
      · have hI4θ : IntervalIntegrable (fun t => deriv f t) volume (Real.pi/4) θ :=
          hII hge (fun t ht => ⟨lt_trans hpi4.1 ht.1, lt_trans ht.2 hθ.2⟩)
        have hadd : (∫ x in (0:ℝ)..(Real.pi/4), deriv f x) + (∫ x in (Real.pi/4)..θ, deriv f x)
            = ∫ x in (0:ℝ)..θ, deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hI0 hI4θ
        rw [h1, hftc]
        linarith
    have hkey : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = ∫ t in Set.Ioo 0 θ, deriv f t := by
      intro θ hθ
      rw [sbl_setIntegral_Ioo_eq_intervalIntegral (le_of_lt hθ.1)]
      exact hkeyI θ hθ
    have hbound : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        (f θ - c)^2 ≤ 2 * θ^(1 + Work.Spaces.eta) *
          ∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
      intro θ hθ
      have hsub : Set.Ioo 0 θ ⊆ Set.Ioo 0 (Real.pi/2) := fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩
      have hcs := weightedCS (s := Set.Ioo 0 θ) measurableSet_Ioo
        (w := Work.FTS.EllipticEst.thEta) (g := fun t => deriv f t)
        (fun t ht => hth_pos t (hsub ht))
        (hth_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hwiL θ hθ)
      have hA : 0 ≤ ∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        sbl_setIntegral_nonneg_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg
            ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
      rw [hkey θ hθ]
      calc (∫ t in Set.Ioo 0 θ, deriv f t)^2
          ≤ (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (2 * θ^(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left (hbL θ hθ) hA
        _ = 2 * θ^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by ring
    refine ⟨c, ?_, hbound⟩
    refine tendstoSqBoundLeft (M := 2 * (∫ t in Set.Ioo 0 (Real.pi/2),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)) ?_ ?_
    · exact mul_nonneg (by norm_num) hA0
    · intro θ hθ
      calc (f θ - c)^2
          ≤ 2 * θ^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            hbound θ hθ
        _ ≤ 2 * θ^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            mul_le_mul_of_nonneg_left (sbl_energy_mono hint hθ)
              (mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hθ.1 _)))
        _ = (2 * (∫ t in Set.Ioo 0 (Real.pi/2),
                (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * θ^(1 + Work.Spaces.eta) := by ring
  -- ### Right endpoint
  have hright : ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (f θ - c)^2
        ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) *
          ∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
    have hI42 : IntervalIntegrable (fun t => deriv f t) volume (Real.pi/4) (Real.pi/2) :=
      hII (by linarith [Real.pi_pos]) (fun t ht => ⟨lt_trans hpi4.1 ht.1, ht.2⟩)
    set c : ℝ := f (Real.pi/4) + ∫ x in (Real.pi/4)..(Real.pi/2), deriv f x with hc
    have hkeyI : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = -∫ x in θ..(Real.pi/2), deriv f x := by
      intro θ hθ
      have h1 : f θ - c
          = (f θ - f (Real.pi/4)) - ∫ x in (Real.pi/4)..(Real.pi/2), deriv f x := by
        rw [hc]; ring
      have hftc : f θ - f (Real.pi/4) = ∫ x in (Real.pi/4)..θ, deriv f x :=
        (sbl_deriv_ftc hf hpi4 hθ).symm
      rcases le_total θ (Real.pi/4) with hle | hge
      · have hIθ4 : IntervalIntegrable (fun t => deriv f t) volume θ (Real.pi/4) :=
          hII hle (fun t ht => ⟨lt_trans hθ.1 ht.1, lt_trans ht.2 hpi4.2⟩)
        have hsym : (∫ x in (Real.pi/4)..θ, deriv f x) = -(∫ x in θ..(Real.pi/4), deriv f x) :=
          intervalIntegral.integral_symm θ (Real.pi/4)
        have hadd : (∫ x in θ..(Real.pi/4), deriv f x)
              + (∫ x in (Real.pi/4)..(Real.pi/2), deriv f x)
            = ∫ x in θ..(Real.pi/2), deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hIθ4 hI42
        rw [h1, hftc, hsym]
        linarith
      · have hI4θ : IntervalIntegrable (fun t => deriv f t) volume (Real.pi/4) θ :=
          hII hge (fun t ht => ⟨lt_trans hpi4.1 ht.1, lt_trans ht.2 hθ.2⟩)
        have hIθ2 : IntervalIntegrable (fun t => deriv f t) volume θ (Real.pi/2) :=
          hII (le_of_lt hθ.2) (fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩)
        have hadd : (∫ x in (Real.pi/4)..θ, deriv f x)
              + (∫ x in θ..(Real.pi/2), deriv f x)
            = ∫ x in (Real.pi/4)..(Real.pi/2), deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hI4θ hIθ2
        rw [h1, hftc]
        linarith
    have hkey : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = -∫ t in Set.Ioo θ (Real.pi/2), deriv f t := by
      intro θ hθ
      rw [hkeyI θ hθ, sbl_setIntegral_Ioo_eq_intervalIntegral (le_of_lt hθ.2)]
    have hbound : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (f θ - c)^2
        ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) *
          ∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
      intro θ hθ
      have hsub : Set.Ioo θ (Real.pi/2) ⊆ Set.Ioo 0 (Real.pi/2) :=
        fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩
      have hcs := weightedCS (s := Set.Ioo θ (Real.pi/2)) measurableSet_Ioo
        (w := Work.FTS.EllipticEst.thEta) (g := fun t => deriv f t)
        (fun t ht => hth_pos t (hsub ht))
        (hth_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hwiR θ hθ)
      have hA : 0 ≤ ∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        sbl_setIntegral_nonneg_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg
            ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
      have hsq : (f θ - c)^2 = (∫ t in Set.Ioo θ (Real.pi/2), deriv f t)^2 := by
        rw [hkey θ hθ]; ring
      rw [hsq]
      calc (∫ t in Set.Ioo θ (Real.pi/2), deriv f t)^2
          ≤ (∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (∫ t in Set.Ioo θ (Real.pi/2), (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left (hbR θ hθ) hA
        _ = 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo θ (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by ring
    refine ⟨c, ?_, hbound⟩
    refine tendstoSqBoundRight (M := 2 * (∫ t in Set.Ioo 0 (Real.pi/2),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)) ?_ ?_
    · exact mul_nonneg (by norm_num) hA0
    · intro θ hθ
      calc (f θ - c)^2
          ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo θ (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            hbound θ hθ
        _ ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            mul_le_mul_of_nonneg_left (sbl_energy_mono_right hint hθ)
              (mul_nonneg (by norm_num)
                (le_of_lt (Real.rpow_pos_of_pos (by linarith [hθ.2, Real.pi_pos]) _)))
        _ = (2 * (∫ t in Set.Ioo 0 (Real.pi/2),
                (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) := by ring
  exact ⟨hleft, hright⟩

end Work.EllipticEst.Core
