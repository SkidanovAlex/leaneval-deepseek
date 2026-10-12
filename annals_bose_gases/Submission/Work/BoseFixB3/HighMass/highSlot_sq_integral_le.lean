import Mathlib
import Submission.Work.BoseFixB3.HighMass.abox_succ_lintegral_slice
import Submission.Work.BoseFixB3.HighMass.lowMult_sq_le_ae_of_nonpos
import Submission.Work.BoseFixB3.HighMass.measurable_highSlot
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.highSlot_sq_integral_le`

`Q̄_{L,j} = (1 − f_L)(√−Δ)` is an `L²`-contraction on the box:

`∫_{abox n ℓ} (highSlot fc κ ℓ j Φ)² ≤ ∫_{abox n ℓ} Φ²`.

The proof splits the `n`-particle integral along the slot `j` (measure-preserving
`piFinSuccAbove` split) and applies the one-slot inequality
`∫_{acube ℓ} (ψ − lowMult fc κ ℓ ψ)² ≤ ∫_{acube ℓ} ψ²` fibre-wise.
-/

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.HighMass

open Submission.BoseGases Work.BoseBoxFix

/-- The symbol `p ↦ f(‖p‖/κ)` of the complementary multiplier `1 − f_L`. -/
def gsym (fc : LowCut) (κ : ℝ) (p : ℝ³) : ℝ := fc.f (‖p‖ / κ)

/-- The complex Fourier multiplier with symbol `gsym fc κ`, attached to the low-momentum
cut-off of `LowCut`.  Its real part is `lowMult fc κ ℓ` (`lowMult_eq_re_kinMult`). -/
def kinMult (fc : LowCut) (κ : ℝ) (v : ℝ³ → ℂ) (x : ℝ³) : ℂ :=
  ((((2 * π) ^ 3)⁻¹ : ℝ) * ∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT v p)

/-- `lowMult` is the real part of `kinMult` applied to the `0`-extension of the profile. -/
lemma lowMult_eq_re_kinMult (fc : LowCut) (κ ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) :
    lowMult fc κ ℓ ψ x
      = (kinMult fc κ (fun z => ((((acube ℓ).indicator ψ z : ℝ)) : ℂ)) x).re := rfl

lemma gsym_nonneg (fc : LowCut) (κ : ℝ) (p : ℝ³) : 0 ≤ gsym fc κ p := by
  rcases lt_or_ge (1 : ℝ) (‖p‖ / κ) with h | h
  · rcases lt_or_ge (2 : ℝ) (‖p‖ / κ) with h2 | h2
    · simp [gsym, fc.zero _ h2.le]
    · have h1 : fc.f 1 = 1 := fc.one 1 le_rfl
      have hf1 : fc.f (‖p‖ / κ) ≤ fc.f 1 := fc.anti h.le
      rw [h1] at hf1
      have h0 : 0 ≤ fc.f (‖p‖ / κ) := by
        have : fc.f 2 = 0 := fc.zero 2 le_rfl
        have hf2 : fc.f 2 ≤ fc.f (‖p‖ / κ) := fc.anti h2
        rw [this] at hf2; exact hf2
      exact h0
  · simp [gsym, fc.one _ h]

lemma gsym_le_one (fc : LowCut) (κ : ℝ) (p : ℝ³) : gsym fc κ p ≤ 1 := by
  rcases lt_or_ge (1 : ℝ) (‖p‖ / κ) with h | h
  · have h1 : fc.f 1 = 1 := fc.one 1 le_rfl
    have hf1 : fc.f (‖p‖ / κ) ≤ fc.f 1 := fc.anti h.le
    simpa [gsym, h1] using hf1
  · simp [gsym, fc.one _ h]

lemma gsym_continuous (fc : LowCut) (κ : ℝ) : Continuous (gsym fc κ) :=
  fc.smooth.continuous.comp (continuous_norm.div_const κ)

lemma gsym_abs_le_one (fc : LowCut) (κ : ℝ) (p : ℝ³) : |gsym fc κ p| ≤ 1 :=
  abs_le.mpr ⟨by linarith [gsym_nonneg fc κ p], gsym_le_one fc κ p⟩

lemma gsym_zero_of_two_mul_le {fc : LowCut} {κ : ℝ} (hκ : 0 < κ) {p : ℝ³}
    (hp : 2 * κ ≤ ‖p‖) : gsym fc κ p = 0 := by
  rw [gsym, fc.zero _ ?_]
  rw [le_div_iff₀ hκ]
  linarith

/-- For `κ > 0` the momentum cutoff symbol is `L¹`: it is bounded by `1` and supported in
the ball of radius `2κ`. -/
lemma integrable_gsym {fc : LowCut} {κ : ℝ} (hκ : 0 < κ) : Integrable (gsym fc κ) := by
  have hg : Integrable (fun p : ℝ³ => (Metric.closedBall (0 : ℝ³) (2 * κ)).indicator
      (fun _ => (1 : ℝ)) p) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
    refine MeasureTheory.IntegrableOn.of_bound
      (isCompact_closedBall (0 : ℝ³) (2 * κ)).measure_lt_top aestronglyMeasurable_const 1 ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg zero_le_one]
  refine hg.mono' ((gsym_continuous fc κ).aestronglyMeasurable) ?_
  filter_upwards with p
  by_cases hp : p ∈ Metric.closedBall (0 : ℝ³) (2 * κ)
  · rw [Set.indicator_of_mem hp, Real.norm_eq_abs]
    exact gsym_abs_le_one fc κ p
  · rw [Set.indicator_of_notMem hp]
    have hp' : 2 * κ ≤ ‖p‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      exact (not_le.mp hp).le
    rw [gsym_zero_of_two_mul_le hκ hp']
    simp

/-- The product of the symbol with any bounded strongly measurable momentum profile is `L¹`
(for `κ > 0`). -/
lemma integrable_gsym_mul {fc : LowCut} {κ : ℝ} (hκ : 0 < κ) {v : ℝ³ → ℂ}
    (hv : StronglyMeasurable v) (hb : ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖v p‖ ≤ B) :
    Integrable (fun p => ((gsym fc κ p : ℝ) : ℂ) * v p) := by
  obtain ⟨B, hB0, hB⟩ := hb
  have hg : Integrable (fun p : ℝ³ => (Metric.closedBall (0 : ℝ³) (2 * κ)).indicator
      (fun _ => B) p) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
    refine MeasureTheory.IntegrableOn.of_bound
      (isCompact_closedBall (0 : ℝ³) (2 * κ)).measure_lt_top aestronglyMeasurable_const B ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg hB0]
  refine hg.mono' (((Complex.continuous_ofReal.measurable.comp
      (gsym_continuous fc κ).measurable)).stronglyMeasurable.mul hv).aestronglyMeasurable ?_
  filter_upwards with p
  by_cases hp : p ∈ Metric.closedBall (0 : ℝ³) (2 * κ)
  · rw [Set.indicator_of_mem hp, norm_mul]
    have h1 : ‖(((gsym fc κ p : ℝ)) : ℂ)‖ ≤ 1 := by
      simpa using gsym_abs_le_one fc κ p
    exact le_trans (mul_le_mul h1 (hB p) (norm_nonneg _) zero_le_one) (le_of_eq (one_mul B))
  · rw [Set.indicator_of_notMem hp]
    have hp' : 2 * κ ≤ ‖p‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      exact (not_le.mp hp).le
    rw [gsym_zero_of_two_mul_le hκ hp', Complex.ofReal_zero, zero_mul, norm_zero]

/-- **Boundedness of the multiplier for `κ > 0`**: the multiplier whose momentum coefficient
`p ↦ gsym(p)·kinFT v p` is `L¹` is bounded (uniformly in `x`) by `(2π)⁻³` times the `L¹`-norm
of that coefficient. -/
lemma kinMult_norm_le {fc : LowCut} {κ : ℝ} {v : ℝ³ → ℂ}
    (hc : Integrable (fun p => ((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT v p))
    (x : ℝ³) :
    ‖kinMult fc κ v x‖ ≤ ((2 * π) ^ 3)⁻¹ *
      ∫ p, ‖((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT v p‖ := by
  have h0 : 0 ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  have hZ : (∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT v p)
      = ∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT v p) := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hval : kinMult fc κ v x = ((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) *
      (∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT v p)) := by
    rw [kinMult, hZ]
  rw [hval, norm_mul]
  have h1 : ‖((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ)‖ = ((2 * π) ^ 3)⁻¹ := by
    rw [show ‖((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ)‖ = |((2 * π) ^ 3)⁻¹| from by simp,
      abs_of_nonneg h0]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg (Eventually.of_forall (fun p => norm_nonneg _)) hc.norm ?_
  filter_upwards with p
  have hexp : ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ))‖ = 1 := by
    rw [mul_comm Complex.I ((inner ℝ p x : ℂ))]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, hexp, one_mul]

/-! ## The Fubini pairing identity for the inverse Fourier integral -/

/-- `conj` commutes with the Bochner integral. -/
lemma conj_integral {f : ℝ³ → ℂ} (hf : Integrable f) :
    ∫ x, (starRingEnd ℂ) (f x) = (starRingEnd ℂ) (∫ x, f x) :=
  ContinuousLinearMap.integral_comp_comm Complex.conjCLE.toContinuousLinearMap hf

/-- The `p`-convention Fourier transform of an a.e. strongly measurable function is strongly
measurable (no integrability needed: the Bochner integral is total). -/
lemma stronglyMeasurable_kinFT {u : ℝ³ → ℂ} (hu : AEStronglyMeasurable u volume) :
    StronglyMeasurable (Submission.BoseGases.kinFT u) := by
  have hfun : Submission.BoseGases.kinFT u = Submission.BoseGases.kinFT (hu.mk u) := by
    funext p
    apply integral_congr_ae
    filter_upwards [hu.ae_eq_mk] with z hz
    rw [hz]
  rw [hfun]
  have hjoint : StronglyMeasurable (fun w : ℝ³ × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ w.1 w.2 : ℂ))) * hu.mk u w.2) := by
    refine ((Complex.continuous_exp.comp ?_).measurable.stronglyMeasurable).mul ?_
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_inner)).neg
    · exact hu.stronglyMeasurable_mk.comp_measurable measurable_snd
  have h := StronglyMeasurable.integral_prod_right
    (ν := (volume : Measure ℝ³))
    (f := fun p z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * hu.mk u z) hjoint
  rwa [show Submission.BoseGases.kinFT (hu.mk u)
      = fun p : ℝ³ => ∫ z, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * hu.mk u z
      from rfl]

/-- The inverse-transform integral `x ↦ ∫_p c p e^{i⟪p,x⟫}dp` is the Fourier transform of `c`
at `-x`, hence strongly measurable. -/
lemma stronglyMeasurable_invFT {c : ℝ³ → ℂ} (hc : AEStronglyMeasurable c volume) :
    StronglyMeasurable (fun x : ℝ³ =>
      ∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))) := by
  have h1 : (fun x : ℝ³ => ∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
      = fun x : ℝ³ => Submission.BoseGases.kinFT c (-x) := by
    funext x
    rw [Submission.BoseGases.kinFT]
    apply integral_congr_ae
    filter_upwards with p
    rw [mul_comm (c p)]
    congr 1
    congr 1
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring
  rw [h1]
  exact (stronglyMeasurable_kinFT hc).comp_measurable continuous_neg.measurable

/-- `∫_x u x · e^{i⟪p,x⟫}dx = conj(kinFT u p)` for real `u`. -/
lemma integral_ofReal_mul_exp {u : ℝ³ → ℝ} (hu : Integrable u) (p : ℝ³) :
    ∫ x, (u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ))
      = (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) := by
  have hC : Integrable (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (u z : ℂ)) := by
    refine hu.norm.mono' ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ (hu.ofReal).aestronglyMeasurable
      exact (by fun_prop : Continuous (fun z : ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_mul, Complex.norm_exp]
      have hz : (-(Complex.I * (inner ℝ p z : ℂ))).re = 0 := by simp
      rw [hz, Real.exp_zero, one_mul]
      simp
  rw [show (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p)
      = ∫ z, (starRingEnd ℂ)
          (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (u z : ℂ)) from by
    rw [conj_integral hC]
    rfl]
  apply integral_congr_ae
  filter_upwards with z
  have h1 : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))
      = Complex.exp (Complex.I * (inner ℝ p z : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [map_mul, h1, Complex.conj_ofReal, mul_comm]

/-- **Fubini pairing for the inverse Fourier integral.**  For `u ∈ L¹(ℝ³)` real and
`c ∈ L¹(ℝ³,ℂ)`,

`∫_x u x · (∫_p c p e^{i⟪p,x⟫}dp)^ℜ dx = ∫_p (conj(kinFT u p)·c p)^ℜ dp`.

Both sides are the `𝓕⁻¹` pairing `⟨u, 𝓕⁻¹c⟩` written in position and momentum space; the
identity is Fubini plus `∫_x u x e^{i⟪p,x⟫}dx = conj(kinFT u p)`. -/
theorem kinPair {u : ℝ³ → ℝ} (hu : Integrable u) {c : ℝ³ → ℂ} (hc : Integrable c) :
    ∫ x, u x * (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re
      = ∫ p : ℝ³,
          ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) * c p).re := by
  have huC : Integrable (fun z : ℝ³ => (u z : ℂ)) := hu.ofReal
  -- joint integrability of the double integrand
  have hFint : Integrable (fun w : ℝ³ × ℝ³ =>
      (u w.1 : ℂ) * (c w.2 * Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))))
      (volume.prod volume) := by
    have hb : Integrable (fun w : ℝ³ × ℝ³ => ‖u w.1‖ * ‖c w.2‖) (volume.prod volume) :=
      hu.norm.mul_prod hc.norm
    refine hb.mono' ?_ ?_
    · have hexp : AEStronglyMeasurable (fun w : ℝ³ × ℝ³ =>
          Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) (volume.prod volume) :=
        (by fun_prop : Continuous (fun w : ℝ³ × ℝ³ =>
          Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ)))).aestronglyMeasurable
      have h1 : AEStronglyMeasurable (fun w : ℝ³ × ℝ³ =>
          ((u w.1 : ℂ) * c w.2) *
            Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) (volume.prod volume) :=
        AEStronglyMeasurable.mul ((huC.mul_prod hc).aestronglyMeasurable) hexp
      simpa only [mul_assoc] using h1
    · filter_upwards with w
      have hre : (Complex.I * (inner ℝ w.2 w.1 : ℂ)).re = 0 := by simp
      rw [norm_mul, norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      simp
  have hswap : ∫ x, ∫ p : ℝ³, (u x : ℂ) * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
      = ∫ p : ℝ³, ∫ x, (u x : ℂ) * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))) :=
    MeasureTheory.integral_integral_swap hFint
  -- the complex form of the identity
  have hcomplex : ∫ x, (u x : ℂ) *
        (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
      = ∫ p : ℝ³, c p * (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) := by
    have h1 : ∫ x, (u x : ℂ) *
          (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
        = ∫ x, ∫ p : ℝ³,
            (u x : ℂ) * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))) := by
      apply integral_congr_ae
      filter_upwards with x
      exact (MeasureTheory.integral_const_mul (u x : ℂ)
        (fun p : ℝ³ => c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).symm
    have h3 : ∫ p : ℝ³, ∫ x, (u x : ℂ) * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
        = ∫ p : ℝ³, c p * (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [show (∫ x, (u x : ℂ) * (c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))))
          = ∫ x, c p * ((u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ))) from by
        apply integral_congr_ae
        filter_upwards with x
        ring]
      rw [MeasureTheory.integral_const_mul, integral_ofReal_mul_exp hu p]
    exact h1.trans (hswap.trans h3)
  -- integrability of the two sides
  have hLI : Integrable (fun x : ℝ³ => (u x : ℂ) *
      (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))) := by
    have hb : Integrable (fun x : ℝ³ => ‖u x‖ * (∫ p : ℝ³, ‖c p‖)) :=
      hu.norm.mul_const _
    refine hb.mono' ?_ ?_
    · refine AEStronglyMeasurable.mul huC.aestronglyMeasurable ?_
      exact (stronglyMeasurable_invFT hc.aestronglyMeasurable).aestronglyMeasurable
    · filter_upwards with x
      have hbnd : ‖∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))‖
          ≤ ∫ p : ℝ³, ‖c p‖ := by
        refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
        apply integral_congr_ae
        filter_upwards with p
        rw [norm_mul, Complex.norm_exp]
        have hre : (Complex.I * (inner ℝ p x : ℂ)).re = 0 := by simp
        rw [hre, Real.exp_zero, mul_one]
      have h1 : ‖(u x : ℂ)‖ = ‖u x‖ := by simp
      rw [norm_mul, h1]
      exact mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
  have hRI : Integrable (fun p : ℝ³ =>
      (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) * c p) := by
    have hbnd : ∀ p : ℝ³, ‖(starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p)‖
        ≤ ∫ z, ‖u z‖ := by
      intro p
      have h1 : (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p)
          = ∫ x, (u x : ℂ) * Complex.exp (Complex.I * (inner ℝ p x : ℂ)) :=
        (integral_ofReal_mul_exp hu p).symm
      rw [h1]
      refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul, Complex.norm_exp]
      have hre : (Complex.I * (inner ℝ p x : ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
      simp
    have hb : Integrable (fun p : ℝ³ => (∫ z, ‖u z‖) * ‖c p‖) := hc.norm.const_mul _
    refine hb.mono' ?_ ?_
    · refine AEStronglyMeasurable.mul
        (((stronglyMeasurable_kinFT huC.aestronglyMeasurable).star).aestronglyMeasurable)
        hc.aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbnd p) (norm_nonneg _)
  -- take real parts
  have hL : ∫ x, u x * (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re
      = (∫ x, (u x : ℂ) *
          (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re := by
    have h1 : (∫ x, u x * (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
        = ∫ x, ((u x : ℂ) *
            (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re := by
      apply integral_congr_ae
      filter_upwards with x
      exact (Complex.re_ofReal_mul (u x) _).symm
    have h2 : (∫ x, ((u x : ℂ) *
          (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re)
        = (∫ x, (u x : ℂ) *
            (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re := by
      simpa [Complex.reCLM_apply] using
        (ContinuousLinearMap.integral_comp_comm Complex.reCLM hLI)
    exact h1.trans h2
  have hR : ∫ p : ℝ³,
        ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) * c p).re
      = (∫ p : ℝ³,
          (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) * c p).re := by
    simpa [Complex.reCLM_apply] using
      (ContinuousLinearMap.integral_comp_comm Complex.reCLM hRI)
  rw [hL, hR]
  rw [show (∫ p : ℝ³, (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) * c p)
      = ∫ p : ℝ³, c p * (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p) from by
    apply integral_congr_ae
    filter_upwards with p
    ring]
  rw [← hcomplex]

/-! ## The one-slot inequality -/

/-- The multiplier integral `x ↦ ∫_p c p e^{i⟪p,x⟫}dp` equals `(2π)³` times the real
multiplier `kinMult` at the coefficient `p ↦ gsym(p)·kinFT v p`. -/
lemma kinMult_eq_invFT (fc : LowCut) (κ : ℝ) (v : ℝ³ → ℂ) (x : ℝ³) :
    kinMult fc κ v x = ((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) *
      (∫ p : ℝ³,
        (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT v p) *
          Complex.exp (Complex.I * (inner ℝ p x : ℂ))) := by
  rw [kinMult]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  ring

lemma gsym_abs_mul_le (fc : LowCut) (κ : ℝ) (p : ℝ³) (r : ℝ) :
    |gsym fc κ p * r| ≤ |r| := by
  rw [abs_mul, abs_of_nonneg (gsym_nonneg fc κ p)]
  exact mul_le_of_le_one_left (abs_nonneg _) (gsym_le_one fc κ p)

/-- **The one-slot inequality for `κ > 0`**:
`∫_{acube ℓ} (ψ − lowMult fc κ ℓ ψ)² ≤ ∫_{acube ℓ} ψ²` for continuous `ψ`.

The proof is the standard `P(I−M)P` contraction argument, written without ever computing
the Fourier transform of `lowMult ψ`: with `T := (kinMult fc κ H)^ℜ`, `H = 1_{acube ℓ}·ψ`,
the Fubini pairing `kinPair` gives
`∫_{acube ℓ} ψ T = (2π)⁻³∫_p gsym(p)‖kinFT H p‖²` and
`∫_{acube ℓ} T² = (2π)⁻³∫_p gsym(p)·ℜ(conj(kinFT U p)·kinFT H p)`, `U = 1_{acube ℓ}·T`;
Cauchy–Schwarz together with Plancherel then gives `∫_{acube ℓ} T² ≤ ∫_{acube ℓ} ψ T`. -/
theorem oneSlot_sq_integral_le_pos {fc : LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    ∫ b in acube ℓ, (ψ b - lowMult fc κ ℓ ψ b) ^ 2 ≤ ∫ b in acube ℓ, (ψ b) ^ 2 := by
  classical
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  have hα : ((2 * π) ^ 3 : ℝ) ≠ 0 := by positivity
  set Ψ : ℝ³ → ℝ := (acube ℓ).indicator ψ with hΨ
  set H : ℝ³ → ℂ := fun z => (Ψ z : ℂ) with hH
  have hHind : H = fun z => ((((acube ℓ).indicator ψ z : ℝ)) : ℂ) := by rw [hH, hΨ]
  set c : ℝ³ → ℂ := fun p => ((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT H p with hcdef
  set T : ℝ³ → ℝ := fun x => (kinMult fc κ H x).re with hTdef
  set U : ℝ³ → ℝ := (acube ℓ).indicator T with hUdef
  obtain ⟨Cψ, hCψ⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hψ.norm.continuousOn
  have hΨmeas : Measurable Ψ := by
    rw [hΨ]; exact hψ.measurable.indicator (acube_measurable ℓ)
  have hΨint : Integrable Ψ volume := by
    rw [hΨ, integrable_indicator_iff (acube_measurable ℓ)]
    exact ContinuousOn.integrableOn_compact (acube_compact hℓ) hψ.continuousOn
  have hHint : Integrable H volume := hΨint.ofReal
  have hFh_bound : ∀ p : ℝ³, ‖Submission.BoseGases.kinFT H p‖ ≤ ∫ z, ‖H z‖ := by
    intro p
    rw [show Submission.BoseGases.kinFT H p
        = ∫ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * H z from rfl]
    refine le_trans (norm_integral_le_integral_norm
      (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * H z)) (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with z
    rw [norm_mul, Complex.norm_exp]
    have hz : (-(Complex.I * (inner ℝ p z : ℂ))).re = 0 := by simp
    rw [hz, Real.exp_zero, one_mul]
  have hc : Integrable c volume := by
    rw [hcdef]
    exact integrable_gsym_mul (fc := fc) (κ := κ) hκ
      (v := Submission.BoseGases.kinFT H)
      (stronglyMeasurable_kinFT hHint.aestronglyMeasurable)
      ⟨∫ z, ‖H z‖, integral_nonneg (fun z => norm_nonneg _), hFh_bound⟩
  have hlow : ∀ x : ℝ³, lowMult fc κ ℓ ψ x = T x := fun x => by
    rw [lowMult_eq_re_kinMult, ← hHind, hTdef]
  -- the inverse-transform identity
  have hZ : ∀ x : ℝ³, (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
      = (((2 * π) ^ 3 : ℝ) : ℂ) * kinMult fc κ H x := by
    intro x
    have h := kinMult_eq_invFT fc κ H x
    rw [show (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
        = ∫ p : ℝ³, (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT H p) *
            Complex.exp (Complex.I * (inner ℝ p x : ℂ)) from by
      apply integral_congr_ae
      filter_upwards with p
      rw [hcdef]]
    have hcc : ((2 * π) ^ 3 : ℝ) * ((2 * π) ^ 3)⁻¹ = (1 : ℝ) := mul_inv_cancel₀ hα
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, hcc, Complex.ofReal_one, one_mul]
  have hZT : ∀ x : ℝ³, (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re
      = ((2 * π) ^ 3) * T x := fun x => by rw [hZ x, Complex.re_ofReal_mul, hTdef]
  have hTmeas : Measurable T := by
    have h1 : (fun x : ℝ³ => (kinMult fc κ H x).re)
        = fun x : ℝ³ => (((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) *
            (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re := by
      funext x
      rw [hZ x]
      congr 1
      have hcc : ((2 * π) ^ 3)⁻¹ * ((2 * π) ^ 3) = (1 : ℝ) := inv_mul_cancel₀ hα
      rw [← mul_assoc, ← Complex.ofReal_mul, hcc, Complex.ofReal_one, one_mul]
    rw [hTdef, h1]
    exact Complex.continuous_re.measurable.comp (measurable_const.mul
      (stronglyMeasurable_invFT hc.aestronglyMeasurable).measurable)
  have hTcont : Continuous (Submission.BoseGases.kinFT H) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hHint
  have hTn : ∀ x : ℝ³, ‖kinMult fc κ H x‖ ≤ ((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖ := by
    intro x; rw [hcdef]; exact kinMult_norm_le hc x
  have hTb : ∀ x : ℝ³, |T x| ≤ ((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖ := fun x =>
    le_trans (Complex.abs_re_le_norm _) (hTn x)
  have hCnonneg : 0 ≤ ((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖ :=
    mul_nonneg (by positivity) (integral_nonneg fun p => norm_nonneg _)
  have hUint : Integrable U volume := by
    rw [hUdef, integrable_indicator_iff (acube_measurable ℓ)]
    exact IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) hTmeas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hTb)
  have hUmemLp : MemLp (fun z : ℝ³ => (U z : ℂ)) 2 volume := by
    have hind : (fun z : ℝ³ => (((acube ℓ).indicator T) z : ℂ))
        = (acube ℓ).indicator (fun z : ℝ³ => (T z : ℂ)) := by
      funext z
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hz : z ∈ acube ℓ <;> simp [hz]
    rw [hUdef, hind]
    refine (memLp_indicator_iff_restrict (acube_measurable ℓ)).mpr ?_
    refine MemLp.of_bound
      ((Complex.continuous_ofReal.measurable.comp hTmeas).stronglyMeasurable.aestronglyMeasurable)
      (((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖) (Filter.Eventually.of_forall fun z => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hTb z
  have hUc_int : Integrable (fun z : ℝ³ => (U z : ℂ)) volume := hUint.ofReal
  have hUc_sm : StronglyMeasurable (Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ))) :=
    stronglyMeasurable_kinFT hUc_int.aestronglyMeasurable
  have hUc_cont : Continuous (Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ))) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hUc_int
  -- Plancherel for `U`
  have hUplan : ∫ p : ℝ³, ‖Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p‖ ^ 2
      = (2 * π) ^ 3 * ∫ x in acube ℓ, T x ^ 2 := by
    rw [Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hUc_int hUmemLp]
    congr 1
    rw [show (∫ x : ℝ³, ‖(fun z : ℝ³ => (U z : ℂ)) x‖ ^ 2)
        = ∫ x : ℝ³, (acube ℓ).indicator (fun y : ℝ³ => T y ^ 2) x from by
      apply integral_congr_ae
      filter_upwards with x
      rw [hUdef, Set.indicator_apply]
      by_cases hx : x ∈ acube ℓ <;> simp [hx]]
    rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]
  -- the two pairing identities
  have hp1 := kinPair (c := c) hΨint hc
  have hp2 := kinPair (c := c) hUint hc
  have hBid : (2 * π) ^ 3 * ∫ b in acube ℓ, ψ b * T b
      = ∫ p : ℝ³, (gsym fc κ p) * ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
    have h1 : (∫ x : ℝ³, Ψ x *
          (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
        = (2 * π) ^ 3 * ∫ x : ℝ³, Ψ x * T x := by
      rw [show (∫ x : ℝ³, Ψ x *
            (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
          = ∫ x : ℝ³, Ψ x * (((2 * π) ^ 3) * T x) from by
        apply integral_congr_ae; filter_upwards with x; rw [hZT x]]
      rw [show (∫ x : ℝ³, Ψ x * (((2 * π) ^ 3) * T x))
          = ∫ x : ℝ³, ((2 * π) ^ 3) * (Ψ x * T x) from by
        apply integral_congr_ae; filter_upwards with x; ring]
      rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ x : ℝ³, Ψ x * T x) = ∫ x in acube ℓ, ψ x * T x := by
      rw [hΨ, ← MeasureTheory.integral_indicator (acube_measurable ℓ)
        (f := fun x => ψ x * T x)]
      apply integral_congr_ae; filter_upwards with x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ acube ℓ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, pow_two]
    have h3 : (∫ p : ℝ³, ((starRingEnd ℂ)
            (Submission.BoseGases.kinFT (fun z => (Ψ z : ℂ)) p) * c p).re)
        = ∫ p : ℝ³, (gsym fc κ p) * ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with p
      rw [show (Submission.BoseGases.kinFT (fun z => (Ψ z : ℂ)) p)
          = Submission.BoseGases.kinFT H p from by rw [hH]]
      rw [hcdef]
      rw [show ((starRingEnd ℂ) (Submission.BoseGases.kinFT H p) *
            (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT H p)).re
          = (gsym fc κ p) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT H p) *
              Submission.BoseGases.kinFT H p).re from by
        rw [show (starRingEnd ℂ) (Submission.BoseGases.kinFT H p) *
              (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT H p)
            = (((gsym fc κ p : ℝ) : ℂ)) *
              ((starRingEnd ℂ) (Submission.BoseGases.kinFT H p) *
                Submission.BoseGases.kinFT H p) from by ring,
          Complex.re_ofReal_mul]]
      rw [show ((starRingEnd ℂ) (Submission.BoseGases.kinFT H p) *
              Submission.BoseGases.kinFT H p).re = ‖Submission.BoseGases.kinFT H p‖ ^ 2 from by
        rw [show (starRingEnd ℂ) (Submission.BoseGases.kinFT H p) *
              Submission.BoseGases.kinFT H p
            = (((‖Submission.BoseGases.kinFT H p‖ ^ 2 : ℝ)) : ℂ) from by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq],
          Complex.ofReal_re]]
    rw [h1, h2, h3] at hp1
    exact hp1
  have hAid : (2 * π) ^ 3 * ∫ b in acube ℓ, T b ^ 2
      = ∫ p : ℝ³, (gsym fc κ p) * ((starRingEnd ℂ)
          (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) *
            Submission.BoseGases.kinFT H p).re := by
    have h1 : (∫ x : ℝ³, U x *
          (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
        = (2 * π) ^ 3 * ∫ x : ℝ³, U x * T x := by
      rw [show (∫ x : ℝ³, U x *
            (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
          = ∫ x : ℝ³, U x * (((2 * π) ^ 3) * T x) from by
        apply integral_congr_ae; filter_upwards with x; rw [hZT x]]
      rw [show (∫ x : ℝ³, U x * (((2 * π) ^ 3) * T x))
          = ∫ x : ℝ³, ((2 * π) ^ 3) * (U x * T x) from by
        apply integral_congr_ae; filter_upwards with x; ring]
      rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ x : ℝ³, U x * T x) = ∫ x in acube ℓ, T x ^ 2 := by
      rw [hUdef, ← MeasureTheory.integral_indicator (acube_measurable ℓ)
        (f := fun x => T x ^ 2)]
      apply integral_congr_ae; filter_upwards with x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ acube ℓ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, pow_two]
    have h3 : (∫ p : ℝ³, ((starRingEnd ℂ)
            (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) * c p).re)
        = ∫ p : ℝ³, (gsym fc κ p) * ((starRingEnd ℂ)
            (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) *
              Submission.BoseGases.kinFT H p).re := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hcdef]
      rw [show ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) *
            (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT H p)).re
          = (gsym fc κ p) * ((starRingEnd ℂ)
              (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) *
              Submission.BoseGases.kinFT H p).re from by
        rw [show (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) *
              (((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT H p)
            = (((gsym fc κ p : ℝ) : ℂ)) * ((starRingEnd ℂ)
                (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) *
                Submission.BoseGases.kinFT H p) from by ring,
          Complex.re_ofReal_mul]]
    rw [h1, h2, h3] at hp2
    exact hp2
  -- integrability of the momentum-space integrands
  have hHmemLp : MemLp H 2 volume := by
    have hind : H = (acube ℓ).indicator (fun z : ℝ³ => (ψ z : ℂ)) := by
      funext z
      rw [hHind]
      by_cases hz : z ∈ acube ℓ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    rw [hind]
    refine (memLp_indicator_iff_restrict (acube_measurable ℓ)).mpr ?_
    obtain ⟨C, hC⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hψ.norm.continuousOn
    refine MemLp.of_bound
      ((Complex.continuous_ofReal.measurable.comp hψ.measurable).stronglyMeasurable.aestronglyMeasurable)
      (max C 0) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (acube_measurable ℓ)] with z hz
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (by simpa using hC z hz) (le_max_left C 0)
  have hFhmem : MemLp (Submission.BoseGases.kinFT H) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hHint hHmemLp
  have hFUmem : MemLp (Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ))) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hUc_int hUmemLp
  have hH2int : Integrable (fun p : ℝ³ => ‖Submission.BoseGases.kinFT H p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq hFhmem.aestronglyMeasurable.norm).mp hFhmem.norm
  have hU2int : Integrable (fun p : ℝ³ =>
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq hFUmem.aestronglyMeasurable.norm).mp hFUmem.norm
  have hProdint : Integrable (fun p : ℝ³ =>
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
        ‖Submission.BoseGases.kinFT H p‖) := by
    refine (hU2int.add hH2int).mono' ?_ ?_
    · exact ((hUc_cont.norm.measurable.mul hTcont.norm.measurable)).stronglyMeasurable.aestronglyMeasurable
    · filter_upwards with p
      simp only [Pi.add_apply]
      have h2 : 2 * (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
          ‖Submission.BoseGases.kinFT H p‖)
          ≤ ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ ^ 2 +
            ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
        nlinarith [sq_nonneg (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ -
          ‖Submission.BoseGases.kinFT H p‖)]
      have hab : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
          ‖Submission.BoseGases.kinFT H p‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [Real.norm_of_nonneg hab]
      linarith
  -- the AM–GM chain
  have hGL : Integrable (fun p : ℝ³ => (gsym fc κ p) *
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ ^ 2) := by
    refine hU2int.mono' ?_ ?_
    · exact ((gsym_continuous fc κ).measurable.mul
        (hUc_cont.norm.measurable.pow_const 2)).stronglyMeasurable.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      exact le_trans (gsym_abs_mul_le fc κ p _) (le_of_eq (abs_of_nonneg (sq_nonneg _)))
  have hGR : Integrable (fun p : ℝ³ => (gsym fc κ p) *
      ‖Submission.BoseGases.kinFT H p‖ ^ 2) := by
    refine hH2int.mono' ?_ ?_
    · exact ((gsym_continuous fc κ).measurable.mul
        (hTcont.norm.measurable.pow_const 2)).stronglyMeasurable.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      exact le_trans (gsym_abs_mul_le fc κ p _) (le_of_eq (abs_of_nonneg (sq_nonneg _)))
  have hAB : ∫ x in acube ℓ, T x ^ 2 ≤ ∫ x in acube ℓ, ψ x * T x := by
    have hHl : ∀ p : ℝ³, |((starRingEnd ℂ)
          (Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p) *
          Submission.BoseGases.kinFT H p).re|
        ≤ ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
          ‖Submission.BoseGases.kinFT H p‖ :=
      fun p => le_trans (Complex.abs_re_le_norm _) (le_of_eq (by rw [norm_mul, Complex.norm_conj]))
    have hRe : ∫ p : ℝ³, (gsym fc κ p) * ((starRingEnd ℂ)
          (Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p) *
            Submission.BoseGases.kinFT H p).re
        ≤ ∫ p : ℝ³, (gsym fc κ p) *
            (‖Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p‖ *
              ‖Submission.BoseGases.kinFT H p‖) := by
      refine integral_mono ?_ ?_ (fun p => ?_)
      · refine hProdint.mono' ?_ ?_
        · refine AEStronglyMeasurable.mul (gsym_continuous fc κ).aestronglyMeasurable ?_
          exact (Complex.continuous_re.measurable.comp
            ((Complex.continuous_conj.comp hUc_cont).mul hTcont).measurable).aestronglyMeasurable
        · filter_upwards with p
          calc ‖(gsym fc κ p) * ((starRingEnd ℂ)
                (Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p) *
                Submission.BoseGases.kinFT H p).re‖
              = |gsym fc κ p * ((starRingEnd ℂ)
                  (Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p) *
                  Submission.BoseGases.kinFT H p).re| := Real.norm_eq_abs _
            _ ≤ |((starRingEnd ℂ)
                  (Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p) *
                  Submission.BoseGases.kinFT H p).re| := gsym_abs_mul_le fc κ p _
            _ ≤ _ := hHl p
      · refine hProdint.mono' ?_ ?_
        · refine AEStronglyMeasurable.mul (gsym_continuous fc κ).aestronglyMeasurable ?_
          exact (hUc_cont.norm.measurable.mul hTcont.norm.measurable).aestronglyMeasurable
        · filter_upwards with p
          calc ‖gsym fc κ p * (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
                ‖Submission.BoseGases.kinFT H p‖)‖
              = |gsym fc κ p * (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
                  ‖Submission.BoseGases.kinFT H p‖)| := Real.norm_eq_abs _
            _ ≤ |‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
                  ‖Submission.BoseGases.kinFT H p‖| := gsym_abs_mul_le fc κ p _
            _ = _ := abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hHl p)) (gsym_nonneg fc κ p)
    have hAMGM : ∫ p : ℝ³, (gsym fc κ p) *
          (‖Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p‖ *
            ‖Submission.BoseGases.kinFT H p‖)
        ≤ (1 / 2) * ((∫ p : ℝ³, (gsym fc κ p) *
              ‖Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p‖ ^ 2) +
            (∫ p : ℝ³, (gsym fc κ p) * ‖Submission.BoseGases.kinFT H p‖ ^ 2)) := by
      have h1 : ∫ p : ℝ³, (gsym fc κ p) *
            (‖Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p‖ *
              ‖Submission.BoseGases.kinFT H p‖)
          ≤ ∫ p : ℝ³, (1 / 2) * ((gsym fc κ p) *
                ‖Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p‖ ^ 2 +
              (gsym fc κ p) * ‖Submission.BoseGases.kinFT H p‖ ^ 2) := by
        refine integral_mono ?_ ?_ (fun p => ?_)
        · refine hProdint.mono' ?_ ?_
          · refine AEStronglyMeasurable.mul (gsym_continuous fc κ).aestronglyMeasurable ?_
            exact (hUc_cont.norm.measurable.mul hTcont.norm.measurable).aestronglyMeasurable
          · filter_upwards with p
            calc ‖gsym fc κ p * (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
                  ‖Submission.BoseGases.kinFT H p‖)‖
                = |gsym fc κ p * (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
                    ‖Submission.BoseGases.kinFT H p‖)| := Real.norm_eq_abs _
              _ ≤ |‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
                    ‖Submission.BoseGases.kinFT H p‖| := gsym_abs_mul_le fc κ p _
              _ = _ := abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · exact (hGL.add hGR).const_mul _
        · have h2 : 2 * (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ *
              ‖Submission.BoseGases.kinFT H p‖)
              ≤ ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ ^ 2 +
                ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
            nlinarith [sq_nonneg (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (U z : ℂ)) p‖ -
              ‖Submission.BoseGases.kinFT H p‖)]
          have hgl := gsym_nonneg fc κ p
          nlinarith [mul_le_mul_of_nonneg_left h2 hgl]
      simpa only [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hGL hGR] using h1
    have hUsq_le : (∫ p : ℝ³, (gsym fc κ p) *
          ‖Submission.BoseGases.kinFT (fun z => (U z : ℂ)) p‖ ^ 2)
        ≤ (2 * π) ^ 3 * (∫ x in acube ℓ, T x ^ 2) := by
      refine le_trans ?_ (le_of_eq hUplan)
      exact integral_mono hGL hU2int
        (fun p => mul_le_of_le_one_left (sq_nonneg _) (gsym_le_one fc κ p))
    have hmain : (2 * π) ^ 3 * (∫ x in acube ℓ, T x ^ 2)
        ≤ (2 * π) ^ 3 * (∫ x in acube ℓ, ψ x * T x) := by
      rw [hAid]
      linarith [hRe, hAMGM, hUsq_le, hBid]
    exact le_of_mul_le_mul_left hmain (by positivity)
  -- final algebra
  have hψT_int : IntegrableOn (fun x : ℝ³ => ψ x * T x) (acube ℓ) := by
    refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) ?_
      (max Cψ 0 * (((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖)) ?_
    · exact (hψ.measurable.mul hTmeas).stronglyMeasurable.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (acube_measurable ℓ)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |ψ x| ≤ max Cψ 0 := le_trans (by simpa using hCψ x hx) (le_max_left _ _)
      exact mul_le_mul h1 (hTb x) (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  have hψsq_int : IntegrableOn (fun x : ℝ³ => ψ x ^ 2) (acube ℓ) :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ) (hψ.pow 2).continuousOn
  have hTsq_int : IntegrableOn (fun x : ℝ³ => T x ^ 2) (acube ℓ) := by
    refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) ?_
      ((((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖) ^ 2) (Filter.Eventually.of_forall fun x => ?_)
    · exact (hTmeas.pow_const 2).stronglyMeasurable.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (T x), sq_abs (T x), hTb x, hCnonneg]
  have hsplit : ∫ x in acube ℓ, (ψ x - T x) ^ 2
      = (∫ x in acube ℓ, ψ x ^ 2) - 2 * (∫ x in acube ℓ, ψ x * T x)
        + (∫ x in acube ℓ, T x ^ 2) := by
    have hsub_int : IntegrableOn (fun x : ℝ³ => ψ x ^ 2 - 2 * (ψ x * T x)) (acube ℓ) := by
      convert hψsq_int.sub (hψT_int.const_mul 2) using 1
      try ext x; rfl
    have h1 : (∫ x in acube ℓ, (ψ x - T x) ^ 2)
        = (∫ x in acube ℓ, (ψ x ^ 2 - 2 * (ψ x * T x))) + (∫ x in acube ℓ, T x ^ 2) := by
      have h := MeasureTheory.integral_add hsub_int hTsq_int
      rw [← h]
      apply integral_congr_ae
      filter_upwards with x
      ring
    have h2 : (∫ x in acube ℓ, (ψ x ^ 2 - 2 * (ψ x * T x)))
        = (∫ x in acube ℓ, ψ x ^ 2) - 2 * (∫ x in acube ℓ, ψ x * T x) := by
      have h := MeasureTheory.integral_sub hψsq_int (hψT_int.const_mul 2)
      rw [MeasureTheory.integral_const_mul] at h
      exact h
    rw [h1, h2]
  have hgoal : ∫ x in acube ℓ, (ψ x - T x) ^ 2 ≤ ∫ x in acube ℓ, ψ x ^ 2 := by
    have hBnn : 0 ≤ ∫ x in acube ℓ, ψ x * T x := by
      have h3 : 0 ≤ (2 * π) ^ 3 * (∫ x in acube ℓ, ψ x * T x) := by
        rw [hBid]
        exact integral_nonneg fun p => mul_nonneg (gsym_nonneg fc κ p) (sq_nonneg _)
      by_contra hlt
      push_neg at hlt
      nlinarith [h3, hlt, show (0 : ℝ) < (2 * π) ^ 3 by positivity]
    rw [hsplit]; linarith
  calc ∫ b in acube ℓ, (ψ b - lowMult fc κ ℓ ψ b) ^ 2
      = ∫ b in acube ℓ, (ψ b - T b) ^ 2 := by
        apply integral_congr_ae; filter_upwards with b; rw [hlow b]
    _ ≤ ∫ b in acube ℓ, (ψ b) ^ 2 := hgoal

/-! ## Assembly: the `n`-particle contraction -/

/-- `‖kinFT u p‖ ≤ ∫_z ‖u z‖` (`kinFT` is the Fourier integral, of modulus `1`). -/
lemma kinFT_norm_le (u : ℝ³ → ℂ) (p : ℝ³) :
    ‖Submission.BoseGases.kinFT u p‖ ≤ ∫ z, ‖u z‖ := by
  rw [show Submission.BoseGases.kinFT u p
      = ∫ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * u z from rfl]
  refine le_trans (norm_integral_le_integral_norm
    (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * u z)) (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with z
  rw [norm_mul, Complex.norm_exp]
  have hz : (-(Complex.I * (inner ℝ p z : ℂ))).re = 0 := by simp
  rw [hz, Real.exp_zero, one_mul]

/-- `b ↦ lowMult fc κ ℓ ψ b` is measurable for continuous `ψ` (any `κ`). -/
lemma measurable_lowMult (fc : LowCut) (κ ℓ : ℝ) {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    Measurable (fun b : ℝ³ => lowMult fc κ ℓ ψ b) := by
  set H : ℝ³ → ℂ := fun z => ((((acube ℓ).indicator ψ z : ℝ)) : ℂ) with hH
  set c : ℝ³ → ℂ := fun p => ((gsym fc κ p : ℝ) : ℂ) * Submission.BoseGases.kinFT H p
    with hcdef
  have hHsm : AEStronglyMeasurable H volume :=
    ((Complex.continuous_ofReal.measurable.comp
      (hψ.measurable.indicator (acube_measurable ℓ)))).stronglyMeasurable.aestronglyMeasurable
  have hcsm : AEStronglyMeasurable c volume :=
    ((Complex.continuous_ofReal.measurable.comp
      (gsym_continuous fc κ).measurable).stronglyMeasurable.aestronglyMeasurable).mul
      (stronglyMeasurable_kinFT hHsm).aestronglyMeasurable
  have h1 : (fun b : ℝ³ => lowMult fc κ ℓ ψ b)
      = fun b : ℝ³ => (((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) *
          (∫ p : ℝ³, c p * Complex.exp (Complex.I * (inner ℝ p b : ℂ)))).re := by
    funext b
    rw [lowMult_eq_re_kinMult, ← hH, hcdef, kinMult_eq_invFT]
  rw [h1]
  exact Complex.continuous_re.measurable.comp
    (measurable_const.mul (stronglyMeasurable_invFT hcsm).measurable)

/-- **Boundedness of `lowMult` for `κ > 0`** (uniformly in the position variable). -/
lemma lowMult_abs_le_of_pos {fc : LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ³, |lowMult fc κ ℓ ψ b| ≤ C := by
  set H : ℝ³ → ℂ := fun z => ((((acube ℓ).indicator ψ z : ℝ)) : ℂ) with hH
  have hHsm : AEStronglyMeasurable H volume :=
    ((Complex.continuous_ofReal.measurable.comp
      (hψ.measurable.indicator (acube_measurable ℓ)))).stronglyMeasurable.aestronglyMeasurable
  have hc : Integrable (fun p : ℝ³ => ((gsym fc κ p : ℝ) : ℂ) *
      Submission.BoseGases.kinFT H p) volume :=
    integrable_gsym_mul (fc := fc) (κ := κ) hκ
      (v := Submission.BoseGases.kinFT H)
      (stronglyMeasurable_kinFT hHsm)
      ⟨∫ z, ‖H z‖, integral_nonneg (fun z => norm_nonneg _), fun p => kinFT_norm_le H p⟩
  refine ⟨((2 * π) ^ 3)⁻¹ * ∫ p, ‖((gsym fc κ p : ℝ) : ℂ) *
    Submission.BoseGases.kinFT H p‖, ?_, fun b => ?_⟩
  · exact mul_nonneg (by positivity) (integral_nonneg fun p => norm_nonneg _)
  · have h1 : lowMult fc κ ℓ ψ b = (kinMult fc κ H b).re := by
      rw [lowMult_eq_re_kinMult, hH]
    rw [h1]
    exact le_trans (Complex.abs_re_le_norm _)
      (kinMult_norm_le (fc := fc) (κ := κ) (v := H) hc b)

/-- The integral inequality `∫_x f x ≤ L.toReal` from `∫⁻ x, ofReal (f x) ≤ L`, for
nonnegative `f`.  No measurability or integrability of `f` is needed: if `f` is not
integrable both sides are consistent. -/
lemma integral_le_toReal_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : 0 ≤ f) :
    ∫ x, f x ∂μ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
  by_cases hint : Integrable f μ
  · have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hf)
    rw [← h, ENNReal.toReal_ofReal (integral_nonneg hf)]
  · rw [MeasureTheory.integral_undef hint]
    exact ENNReal.toReal_nonneg

/-- **The one-slot inequality in `∫⁻` form**, for every `κ`. -/
lemma oneSlot_lintegral_le {fc : LowCut} {κ ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : Continuous ψ) :
    ∫⁻ b in acube ℓ, ENNReal.ofReal ((ψ b - lowMult fc κ ℓ ψ b) ^ 2)
      ≤ ∫⁻ b in acube ℓ, ENNReal.ofReal ((ψ b) ^ 2) := by
  by_cases hκ : 0 < κ
  · obtain ⟨C, hC0, hC⟩ := lowMult_abs_le_of_pos (fc := fc) hκ hℓ hψ
    obtain ⟨Cψ, hCψ⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hψ.norm.continuousOn
    have hFint : IntegrableOn (fun b : ℝ³ => (ψ b - lowMult fc κ ℓ ψ b) ^ 2) (acube ℓ) := by
      refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) ?_
        ((max Cψ 0 + C) ^ 2) ?_
      · exact ((hψ.measurable.sub (measurable_lowMult fc κ ℓ hψ)).pow_const
          2).stronglyMeasurable.aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem (acube_measurable ℓ)] with b hb
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : |ψ b| ≤ max Cψ 0 := le_trans (by simpa using hCψ b hb) (le_max_left _ _)
        have h2 : |ψ b - lowMult fc κ ℓ ψ b| ≤ max Cψ 0 + C := by
          have h3 : |ψ b - lowMult fc κ ℓ ψ b| ≤ |ψ b| + |lowMult fc κ ℓ ψ b| := by
            simpa using abs_sub_le (ψ b) 0 (lowMult fc κ ℓ ψ b)
          linarith [h3, h1, hC b]
        have h3 : 0 ≤ max Cψ 0 + C := by
          have := le_max_right Cψ 0; linarith
        nlinarith [h2, h3, abs_nonneg (ψ b - lowMult fc κ ℓ ψ b),
          sq_abs (ψ b - lowMult fc κ ℓ ψ b)]
    have hGint : IntegrableOn (fun b : ℝ³ => (ψ b) ^ 2) (acube ℓ) :=
      ContinuousOn.integrableOn_compact (acube_compact hℓ) (hψ.pow 2).continuousOn
    have hreal := oneSlot_sq_integral_le_pos (fc := fc) hκ hℓ hψ
    have e1 := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall fun b => sq_nonneg _)
    have e2 := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint
      (Filter.Eventually.of_forall fun b => sq_nonneg _)
    rw [← e1, ← e2]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hae := lowMult_sq_le_ae_of_nonpos (fc := fc) (not_lt.mp hκ) hℓ hψ
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with b hb
    exact ENNReal.ofReal_le_ofReal hb

theorem highSlot_sq_integral_le {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseFixB3.highSlot fc κ ℓ j Φ x) ^ 2
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  rcases n with _ | m
  · exact (Fin.elim0 j)
  · set e : Submission.BoseGases.X (m + 1) ≃ᵐ
        (ℝ³ × Submission.BoseGases.X m) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ³) j with he
    -- the box integral of `Φ²` is integrable (continuity on the compact box)
    have hΦ2int : Integrable (fun x : Submission.BoseGases.X (m + 1) => (Φ x) ^ 2)
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ)) :=
      ContinuousOn.integrableOn_compact
        (Work.UBBInputs9.B.abox_isCompact (m + 1) ℓ) (hΦc.pow 2).continuousOn
    -- the pointwise identification of the slot-`j` split
    have hesymm : ∀ (b : ℝ³) (a : Submission.BoseGases.X m),
        e.symm (b, a) = j.insertNth b a := by
      intro b a
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    have hpt : ∀ (b : ℝ³) (a : Submission.BoseGases.X m),
        Work.BoseFixB3.highSlot fc κ ℓ j Φ (e.symm (b, a))
          = (fun z : ℝ³ => Φ (e.symm (z, a))) b
            - lowMult fc κ ℓ (fun z : ℝ³ => Φ (e.symm (z, a))) b := by
      intro b a
      have hupd : ∀ z : ℝ³, Function.update (e.symm (b, a)) j z = e.symm (z, a) := by
        intro z
        rw [hesymm b a, hesymm z a]
        ext k
        rw [Function.update_apply]
        by_cases hk : k = j
        · subst hk
          rw [if_pos rfl, Fin.insertNth_apply_same]
        · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
          rw [if_neg (Fin.succAbove_ne _ _), Fin.insertNth_apply_succAbove,
            Fin.insertNth_apply_succAbove]
      have hxj : (e.symm (b, a)) j = b := by
        rw [hesymm b a, Fin.insertNth_apply_same]
      simp only [Work.BoseFixB3.highSlot, Work.BoseBoxFix.lowSlot, hxj]
      rw [show (fun z : ℝ³ => Φ (Function.update (e.symm (b, a)) j z))
          = fun z : ℝ³ => Φ (e.symm (z, a)) from funext fun z => by rw [hupd z]]
    -- the `∫⁻` slicing
    have hslice (F : Submission.BoseGases.X (m + 1) → ENNReal)
        (hF : AEMeasurable F ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ))) :
        ∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ, F x
          = ∫⁻ a in Submission.BoseGases.abox m ℓ, ∫⁻ b in Submission.BoseGases.acube ℓ,
              F (e.symm (b, a)) :=
      Work.BoseFixB3.HighMass.abox_succ_lintegral_slice j F hF
    have hL := hslice (fun x => ENNReal.ofReal ((Work.BoseFixB3.highSlot fc κ ℓ j Φ x) ^ 2))
      (ENNReal.measurable_ofReal.comp
        (((Work.BoseFixB3.HighMass.measurable_highSlot j hΦc).pow_const 2))).aemeasurable
    have hR := hslice (fun x => ENNReal.ofReal ((Φ x) ^ 2))
      (ENNReal.measurable_ofReal.comp ((hΦc.measurable.pow_const 2))).aemeasurable
    have hmain : ∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ,
          ENNReal.ofReal ((Work.BoseFixB3.highSlot fc κ ℓ j Φ x) ^ 2)
        ≤ ∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ, ENNReal.ofReal ((Φ x) ^ 2) := by
      rw [hL, hR]
      refine lintegral_mono fun a => ?_
      have hecont : Continuous (fun z : ℝ³ => e.symm (z, a)) := by
        rw [continuous_pi_iff]
        intro k
        rw [he]
        by_cases hk : k = j
        · subst hk
          simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
            Fin.insertNth_apply_same]
          exact continuous_id
        · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
          simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
            Fin.insertNth_apply_succAbove]
          exact continuous_const
      have hcont : Continuous (fun z : ℝ³ => Φ (e.symm (z, a))) := hΦc.comp hecont
      have := oneSlot_lintegral_le (fc := fc) (κ := κ) hℓ hcont
      refine le_trans (le_of_eq ?_) this
      apply lintegral_congr
      intro b
      rw [hpt b a]
    -- convert back to Bochner integrals
    have hfin : (∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ,
        ENNReal.ofReal ((Φ x) ^ 2))
        = ENNReal.ofReal (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Φ x) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΦ2int
        (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
    have hle : ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          (Work.BoseFixB3.highSlot fc κ ℓ j Φ x) ^ 2
        ≤ (∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ,
            ENNReal.ofReal ((Work.BoseFixB3.highSlot fc κ ℓ j Φ x) ^ 2)).toReal :=
      integral_le_toReal_lintegral_ofReal (fun x => sq_nonneg _)
    calc ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          (Work.BoseFixB3.highSlot fc κ ℓ j Φ x) ^ 2
        ≤ (∫⁻ x in Submission.BoseGases.abox (m + 1) ℓ,
            ENNReal.ofReal ((Work.BoseFixB3.highSlot fc κ ℓ j Φ x) ^ 2)).toReal := hle
      _ ≤ (ENNReal.ofReal (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Φ x) ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hfin ▸ hmain)
      _ = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Φ x) ^ 2 :=
          ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)

end Work.BoseFixB3.HighMass
