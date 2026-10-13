import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.Degen

/-- The weight `w(z)/sin(2θ)^{η/2}` multiplying `D_z^0 h = h` in the `ℋ^k`-integrand. -/
private def HWt (z θ : ℝ) : ℝ :=
  Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

private lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The product `h · HWt` is continuous on the open quadrant: both factors are (the weight is the
honest continuous weight `w(z)·sin(2θ)^{-η/2}` there). -/
private lemma continuousOn_mul_HWt {h : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen h) :
    ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2 * HWt p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsm.continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => HWt p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hw := Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
    simpa only [HWt, Work.FTS.EllipticEst.Q0] using hw
  exact h1.mul h2

/-- **`L²`-membership of the `D_z^0`-slot.**  The square of `h · HWt` is dominated pointwise by
the `ℋ^k`-integrand, whose angular slices and slice-integral are integrable by `HkMem`; the
a.e.-strong measurability comes from continuity on the open quadrant, and the single slice
`z = 0` is handled separately (there the weight `w` vanishes). -/
private lemma L2Mem_mul_HWt {α : ℝ} {k : ℕ} {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) :
    Work.Spaces.L2Mem (fun z θ => h z θ * HWt z θ) := by
  have hcont := continuousOn_mul_HWt hsm
  constructor
  · intro z hz
    have h := Work.FTS.EllipticEst.integrableOn_zSummand α k hsm hm 0 (Nat.zero_le k) hz
    simpa only [HWt, Work.Spaces.DzIter_zero] using h
  · have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => (h p.1 p.2 * HWt p.1 p.2) ^ 2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (hcont.pow 2)
    refine Integrable.mono' hm.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _) (hm.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => by
          simpa only [HWt, Work.Spaces.DzIter_zero] using
            Work.Spaces.sq_le_HkIntegrand_z α k h z θ 0 (Nat.zero_le k)))

/-- The Lebesgue measure of a real interval `[a,b]`. -/
private lemma volume_Icc_real {a b : ℝ} (h : a ≤ b) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).real (Set.Icc a b) = b - a := by
  have h1 : (MeasureTheory.volume : MeasureTheory.Measure ℝ).real (Set.Icc a b)
      = ((MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc a b)).toReal := rfl
  rw [h1, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- **A nonnegative continuous function on the open quadrant with vanishing `L²`-integral
vanishes on the open quadrant.**  This is the open-quadrant form of
`Work.FTS.EllipticEst.eq_zero_of_L2Sq_eq_zero`: the box used in the contradiction is taken so
small that it stays strictly inside the quadrant, where continuity is available. -/
theorem eq_zero_of_L2Sq_eq_zero_open {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.L2Mem g)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : Work.Spaces.L2Sq g = 0) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → g z θ = 0 := by
  intro z0 θ0 hz0 hθ0 hθ0π
  by_contra hne
  -- continuity of `g` at `(z0,θ0)`, which is interior to the open quadrant
  have hct : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (z0, θ0) :=
    hcont.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz0, hθ0, hθ0π⟩)
  have hε2 : 0 < |g z0 θ0| / 2 := by have := abs_pos.mpr hne; linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hct (|g z0 θ0| / 2) hε2
  -- a box of half-width `ε/2`, small enough to stay inside the quadrant and the `δ`-ball
  set ε : ℝ := min δ (min (z0 / 2) (min (θ0 / 2) ((Real.pi / 2 - θ0) / 2))) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact lt_min hδpos (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hεδ : ε ≤ δ := by rw [hε]; exact min_le_left _ _
  have hεz : ε ≤ z0 / 2 := by
    rw [hε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεθ : ε ≤ θ0 / 2 := by
    rw [hε]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεπ : ε ≤ (Real.pi / 2 - θ0) / 2 := by
    rw [hε]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set zlo : ℝ := z0 - ε / 2 with hzlo
  set zhi : ℝ := z0 + ε / 2 with hzhi
  set tlo : ℝ := θ0 - ε / 2 with htlo
  set thi : ℝ := θ0 + ε / 2 with hthi
  have hzlo0 : 0 ≤ zlo := by rw [hzlo]; linarith
  have htlo0 : 0 ≤ tlo := by rw [htlo]; linarith
  have hthi_pi : thi ≤ Real.pi / 2 := by rw [hthi]; linarith
  have hzbox : Set.Icc zlo zhi ⊆ Work.Spaces.Iz := fun z hz => le_trans hzlo0 hz.1
  have htbox : Set.Icc tlo thi ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_trans htlo0 hθ.1, le_trans hθ.2 hthi_pi⟩
  have hzlo_lt : zlo < zhi := by rw [hzlo, hzhi]; linarith
  have htlo_lt : tlo < thi := by rw [htlo, hthi]; linarith
  -- on the box, `|g| ≥ |g z0 θ0| / 2`
  have hpoint : ∀ z ∈ Set.Icc zlo zhi, ∀ θ ∈ Set.Icc tlo thi,
      (|g z0 θ0| / 2) ^ 2 ≤ (g z θ) ^ 2 := by
    intro z hz θ hθ
    have hz1 : z0 - ε / 2 ≤ z := by rw [hzlo] at hz; exact hz.1
    have hz2 : z ≤ z0 + ε / 2 := by rw [hzhi] at hz; exact hz.2
    have ht1 : θ0 - ε / 2 ≤ θ := by rw [htlo] at hθ; exact hθ.1
    have ht2 : θ ≤ θ0 + ε / 2 := by rw [hthi] at hθ; exact hθ.2
    have hdist : dist (z, θ) (z0, θ0) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ?_⟩ <;> · rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hd : dist (g z θ) (g z0 θ0) < |g z0 θ0| / 2 := hδ hdist
    have h2 : |g z θ - g z0 θ0| < |g z0 θ0| / 2 := by
      simpa [Real.dist_eq] using hd
    have h3 : |g z0 θ0| ≤ |g z0 θ0 - g z θ| + |g z θ| := by
      calc |g z0 θ0| = |(g z0 θ0 - g z θ) + g z θ| := by ring_nf
        _ ≤ |g z0 θ0 - g z θ| + |g z θ| := abs_add_le _ _
    rw [abs_sub_comm] at h3
    have h4 : |g z0 θ0| / 2 < |g z θ| := by linarith
    have h5 : (|g z0 θ0| / 2) ^ 2 ≤ |g z θ| ^ 2 := by
      have h6 : |g z0 θ0| / 2 ≤ |g z θ| := le_of_lt h4
      nlinarith [abs_nonneg (g z0 θ0), abs_nonneg (g z θ)]
    rwa [sq_abs] at h5
  -- the box bound on the iterated integral
  have hstep1 : ∫ z in Set.Icc zlo zhi, (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
      ≤ Work.Spaces.L2Sq g := by
    rw [Work.Spaces.L2Sq]
    exact MeasureTheory.setIntegral_mono_set hmem.2
      (Filter.Eventually.of_forall (fun z => integral_nonneg (fun θ => sq_nonneg _)))
      (Filter.Eventually.of_forall fun z hz => hzbox hz)
  have hstep2 : ∫ z in Set.Icc zlo zhi, ((|g z0 θ0| / 2) ^ 2 * (thi - tlo))
      ≤ ∫ z in Set.Icc zlo zhi, (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
        (by linarith [htlo_lt])) (hmem.2.mono_set hzbox) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun z hz => ?_
    have h1 : (∫ θ in Set.Icc tlo thi, (|g z0 θ0| / 2) ^ 2)
        ≤ ∫ θ in Set.Icc tlo thi, (g z θ) ^ 2 :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
        ((hmem.1 z (hzbox hz)).mono_set (fun θ hθ => htbox hθ))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hpoint z hz θ hθ))
    have h2 : (∫ θ in Set.Icc tlo thi, (g z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 :=
      MeasureTheory.setIntegral_mono_set (hmem.1 z (hzbox hz))
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
        (Filter.Eventually.of_forall fun θ hθ => htbox hθ)
    have h3 : (|g z0 θ0| / 2) ^ 2 * (thi - tlo)
        = ∫ θ in Set.Icc tlo thi, (|g z0 θ0| / 2) ^ 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul,
        volume_Icc_real (le_of_lt htlo_lt)]
      ring
    rw [h3]
    exact le_trans h1 h2
  have hchain : (|g z0 θ0| / 2) ^ 2 * (thi - tlo) * (zhi - zlo) ≤ Work.Spaces.L2Sq g := by
    have h3 := hstep2
    rw [MeasureTheory.setIntegral_const, smul_eq_mul,
      volume_Icc_real (le_of_lt hzlo_lt)] at h3
    linarith [hstep1]
  have hpos : 0 < (|g z0 θ0| / 2) ^ 2 * (thi - tlo) * (zhi - zlo) := by
    have h1 : 0 < (|g z0 θ0| / 2) ^ 2 := by
      have := abs_pos.mpr hne
      positivity
    have h2 : 0 < thi - tlo := by linarith [htlo_lt]
    have h3 : 0 < zhi - zlo := by linarith [hzlo_lt]
    exact mul_pos (mul_pos h1 h2) h3
  rw [hzero] at hchain
  linarith

/-- **The vanishing of the `ℋ^k`-norm forces the profile to vanish on the open quadrant.**

`HkIntegrand` is a sum of squares whose `i = 0` summand in the pure `D_z`-sum is exactly
`(h z θ · w(z)/sin(2θ)^{η/2})²`, because `D_z^0 h = h`; hence `HkSq α k h = 0` gives the honest
vanishing of the iterated `L²`-integral of that summand (`L2Sq_DzIter_le_HkSq` at `i = 0`,
`HkMem` supplies the honesty).  The weight `w(z)/sin(2θ)^{η/2}` never vanishes on the open
quadrant, so the summand vanishes there by the box argument of
`eq_zero_of_L2Sq_eq_zero_open` (continuity on the open quadrant comes from `SmoothOpen`). -/
theorem HkSqZeroOnQuad {α : ℝ} {k : ℕ} {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h)
    (h0 : Work.Spaces.HkSq α k h = 0) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → h z θ = 0 := by
  -- the `D_z^0`-slot of the `ℋ^k`-integrand
  have hL2 : Work.Spaces.L2Sq (fun z θ => h z θ * HWt z θ) = 0 := by
    have hle := Work.Spaces.L2Sq_DzIter_le_HkSq α k h hm 0 (Nat.zero_le k)
    rw [h0] at hle
    have hle' : Work.Spaces.L2Sq (fun z θ => h z θ * HWt z θ) ≤ 0 := by
      simpa only [HWt, Work.Spaces.DzIter_zero] using hle
    have hnn : 0 ≤ Work.Spaces.L2Sq (fun z θ => h z θ * HWt z θ) := by
      rw [Work.Spaces.L2Sq]
      exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
    linarith
  have hmem' : Work.Spaces.L2Mem (fun z θ => h z θ * HWt z θ) := L2Mem_mul_HWt hsm hm
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2 * HWt p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_mul_HWt hsm
  have hzero := eq_zero_of_L2Sq_eq_zero_open hmem' hcont' hL2
  intro z θ hz hθ hθπ
  have hWne : HWt z θ ≠ 0 := by
    rw [HWt]
    refine div_ne_zero ?_
      (ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo ⟨hθ, hθπ⟩) _))
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  exact (mul_eq_zero.mp (hzero z θ hz hθ hθπ)).resolve_right hWne

end Work.FTS.StrongPersist.Degen
