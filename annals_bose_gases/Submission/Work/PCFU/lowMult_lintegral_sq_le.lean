import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB3.HighMass.highSlot_sq_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.lowMult_lintegral_sq_le`

FS's low-momentum localisation `Q_L = P_Λ · m(√−Δ) · E_Λ` is an `L²`-contraction: the whole-space
multiplier `m(√−Δ)` (`m(p) = f(‖p‖/κ)`, `0 ≤ m ≤ 1`) is a contraction of `L²(ℝ³)`, and
`E_Λ ψ = 1_Λ ψ` has the same `L²`-norm as `ψ` on the box `Λ = acube ℓ`.  Writing
`H = 1_Λ ψ` and `c(p) = m(p)·kinFT H p`, the inverse-transform identity
(`kinMult_eq_invFT`) gives, pointwise in `x`,

    lowMult fc κ ℓ ψ x = ((2π)³)⁻¹ · Re(kinFT c (−x)) ,

so that, with `ℜ² ≤ ‖·‖²`,

    ∫_x (lowMult fc κ ℓ ψ x)² ≤ ((2π)³)⁻² ∫_x ‖kinFT c (−x)‖²
      = ((2π)³)⁻² · (2π)³ ∫_p ‖c p‖²            (Plancherel)
      ≤ ((2π)³)⁻² · (2π)³ ∫_p ‖kinFT H p‖²
      = ((2π)³)⁻² · (2π)³ · (2π)³ ∫_x ‖H x‖² = ∫_x (H x)² .

The statement is in `∫⁻`-form, so the two sides are compared through
`ofReal_integral_eq_lintegral_ofReal`; the case `H² ∉ L¹` is immediate because the right-hand
side is then `⊤` (`MeasureTheory.lintegral_ofReal_ne_top_iff_integrable`), the left-hand side
being always finite (the momentum integrand `c` is compactly supported and bounded).

The auxiliary two lemmas at the top of the file (`lowMult_eq_invFT_aux` and
`lowMult_sq_le_aux`) carry the whole analytic content; the final theorem is the bookkeeping.
-/

noncomputable section

namespace Work.PCFU

open MeasureTheory Filter
open scoped Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The inverse-transform form of `lowMult`.**  With `H = 1_{acube ℓ}·ψ` and
`c p = f(‖p‖/κ)·kinFT H p`, the multiplier `lowMult` equals `((2π)³)⁻¹` times the real part of
the inverse transform `x ↦ ∫_p c p e^{i⟪p,x⟫}dp = kinFT c (−x)`.

Only the identity `kinMult_eq_invFT` and the elementary `∫_p c p e^{i⟪p,x⟫}dp = kinFT c (−x)`
are used; no integrability assumption is needed (`kinFT` is a Bochner integral, junk-valued
when the integrand is not integrable, and both sides are junk consistently). -/
private lemma lowMult_eq_invFT_aux {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} {ψ : E3 → ℝ}
    {H : E3 → ℝ} (hH : H = (Submission.BoseGases.acube ℓ).indicator ψ) (x : E3) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ x
      = ((2 * π) ^ 3)⁻¹ *
        (Submission.BoseGases.kinFT
          (fun p : E3 => ((Work.BoseFixB3.HighMass.gsym fc κ p : ℝ) : ℂ) *
            Submission.BoseGases.kinFT (fun z : E3 => (H z : ℂ)) p) (-x)).re := by
  have hfun : (fun z : E3 => ((((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ)) : ℂ))
      = (fun z : E3 => (H z : ℂ)) := by funext z; rw [hH]
  rw [Work.BoseFixB3.HighMass.lowMult_eq_re_kinMult, hfun,
    Work.BoseFixB3.HighMass.kinMult_eq_invFT, Complex.re_ofReal_mul]
  simp only [Submission.BoseGases.kinFT]
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [show (-(Complex.I * (inner ℝ (-x) p : ℂ))) = Complex.I * (inner ℝ p x : ℂ) from by
    rw [inner_neg_left, real_inner_comm]; push_cast; ring]
  ring

/-- **Pointwise square bound.**  With `H = 1_{acube ℓ}·ψ` and `v p = f(‖p‖/κ)·kinFT H p`,
`(lowMult fc κ ℓ ψ x)² ≤ (((2π)³)⁻¹ ‖kinFT v (−x)‖)²`. -/
private lemma lowMult_sq_le_aux {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} {ψ : E3 → ℝ}
    {H : E3 → ℝ} (hH : H = (Submission.BoseGases.acube ℓ).indicator ψ) {v : E3 → ℂ}
    (hv : v = fun p : E3 => ((Work.BoseFixB3.HighMass.gsym fc κ p : ℝ) : ℂ) *
      Submission.BoseGases.kinFT (fun z : E3 => (H z : ℂ)) p) (x : E3) :
    (Work.BoseBoxFix.lowMult fc κ ℓ ψ x) ^ 2
      ≤ (((2 * π) ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT v (-x)‖) ^ 2 := by
  rw [lowMult_eq_invFT_aux (fc := fc) (κ := κ) (ℓ := ℓ) (ψ := ψ) (H := H) hH x, hv]
  set w : ℂ := Submission.BoseGases.kinFT
    (fun p : E3 => ((Work.BoseFixB3.HighMass.gsym fc κ p : ℝ) : ℂ) *
      Submission.BoseGases.kinFT (fun z : E3 => (H z : ℂ)) p) (-x) with hw
  have h2 : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg w)]
    exact Complex.abs_re_le_norm w
  calc (((2 * π) ^ 3)⁻¹ * w.re) ^ 2 = ((2 * π) ^ 3)⁻¹ ^ 2 * w.re ^ 2 := by ring
    _ ≤ ((2 * π) ^ 3)⁻¹ ^ 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (((2 * π) ^ 3)⁻¹ * ‖w‖) ^ 2 := by ring

theorem lowMult_lintegral_sq_le {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.acube ℓ).indicator ψ u)) :
    (∫⁻ z : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal ((Work.BoseBoxFix.lowMult fc κ ℓ ψ z) ^ 2))
      ≤ ∫⁻ u : EuclideanSpace ℝ (Fin 3),
          ENNReal.ofReal (((Submission.BoseGases.acube ℓ).indicator ψ u) ^ 2) := by
  classical
  set H : E3 → ℝ := (Submission.BoseGases.acube ℓ).indicator ψ with hH
  set Hc : E3 → ℂ := fun z : E3 => (H z : ℂ) with hHc
  set c : E3 → ℂ := fun p : E3 => ((Work.BoseFixB3.HighMass.gsym fc κ p : ℝ) : ℂ) *
    Submission.BoseGases.kinFT Hc p with hc
  have hψH : MeasureTheory.Integrable H := by simpa using hψ
  -- step 1: pointwise comparison of the integrands
  have hstep1 : (∫⁻ z : E3, ENNReal.ofReal ((Work.BoseBoxFix.lowMult fc κ ℓ ψ z) ^ 2))
      ≤ ∫⁻ x : E3,
          ENNReal.ofReal ((((2 * π) ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT c (-x)‖) ^ 2) := by
    apply lintegral_mono
    intro x
    exact ENNReal.ofReal_le_ofReal (lowMult_sq_le_aux (κ := κ) (ℓ := ℓ) (ψ := ψ) hH (v := c) hc x)
  by_cases hH2 : MeasureTheory.Integrable (fun u : E3 => H u ^ 2)
  · -- step 2: the `c ∈ L¹ ∩ L²` layer
    have hHmeas : AEStronglyMeasurable H volume := hψH.aestronglyMeasurable
    have hHmemLp : MemLp H 2 volume := (memLp_two_iff_integrable_sq hHmeas).mpr hH2
    have hHcint : MeasureTheory.Integrable Hc := hψH.ofReal
    have hHcmemLp : MemLp Hc 2 volume := hHmemLp.ofReal
    have hkinSm : StronglyMeasurable (Submission.BoseGases.kinFT Hc) :=
      Work.BoseFixB3.HighMass.stronglyMeasurable_kinFT hHcint.aestronglyMeasurable
    have hkinBd : ∀ p : E3, ‖Submission.BoseGases.kinFT Hc p‖ ≤ ∫ z : E3, ‖Hc z‖ := by
      intro p
      rw [show Submission.BoseGases.kinFT Hc p
          = ∫ z : E3, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * Hc z from rfl]
      refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with z
      rw [norm_mul, Complex.norm_exp]
      have hz : (-(Complex.I * (inner ℝ p z : ℂ))).re = 0 := by simp
      rw [hz, Real.exp_zero, one_mul]
    have hcint : MeasureTheory.Integrable c := by
      rw [hc]
      exact Work.BoseFixB3.HighMass.integrable_gsym_mul hκ hkinSm
        ⟨_, integral_nonneg (fun z => norm_nonneg _), hkinBd⟩
    have hkinH_memLp : MemLp (Submission.BoseGases.kinFT Hc) 2 volume :=
      Work.BoseKinLoc.Momentum.memLp_kinFT hHcint hHcmemLp
    have hc_memLp : MemLp c 2 volume := by
      rw [hc]
      refine MemLp.mono' hkinH_memLp.norm ?_ ?_
      · exact ((Complex.continuous_ofReal.measurable.comp
          (Work.BoseFixB3.HighMass.gsym_continuous fc κ).measurable).stronglyMeasurable.mul
            hkinSm).aestronglyMeasurable
      · filter_upwards with p
        show ‖((Work.BoseFixB3.HighMass.gsym fc κ p : ℝ) : ℂ) *
            Submission.BoseGases.kinFT Hc p‖ ≤ ‖Submission.BoseGases.kinFT Hc p‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (Work.BoseFixB3.HighMass.gsym_abs_le_one fc κ p)
    have hck_memLp : MemLp (Submission.BoseGases.kinFT c) 2 volume :=
      Work.BoseKinLoc.Momentum.memLp_kinFT hcint hc_memLp
    have hc2_int : MeasureTheory.Integrable (fun p : E3 => ‖c p‖ ^ 2) :=
      (memLp_two_iff_integrable_sq hc_memLp.aestronglyMeasurable.norm).mp hc_memLp.norm
    have hck2_int : MeasureTheory.Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT c p‖ ^ 2) :=
      (memLp_two_iff_integrable_sq hck_memLp.aestronglyMeasurable.norm).mp hck_memLp.norm
    have hkinH2_int : MeasureTheory.Integrable
        (fun p : E3 => ‖Submission.BoseGases.kinFT Hc p‖ ^ 2) :=
      (memLp_two_iff_integrable_sq hkinH_memLp.aestronglyMeasurable.norm).mp hkinH_memLp.norm
    -- step 3: the `L²`-contraction `‖c‖₂ ≤ ‖kinFT H‖₂` on the momentum side
    have hle_c : (∫ p : E3, ‖c p‖ ^ 2)
        ≤ ∫ p : E3, ‖Submission.BoseGases.kinFT Hc p‖ ^ 2 := by
      apply MeasureTheory.integral_mono hc2_int hkinH2_int
      intro p
      have h1 : ‖c p‖ ≤ ‖Submission.BoseGases.kinFT Hc p‖ := by
        rw [hc]
        show ‖((Work.BoseFixB3.HighMass.gsym fc κ p : ℝ) : ℂ) *
            Submission.BoseGases.kinFT Hc p‖ ≤ ‖Submission.BoseGases.kinFT Hc p‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (Work.BoseFixB3.HighMass.gsym_abs_le_one fc κ p)
      nlinarith [h1, norm_nonneg (c p), norm_nonneg (Submission.BoseGases.kinFT Hc p)]
    have hHnorm : (∫ z : E3, ‖Hc z‖ ^ 2) = ∫ u : E3, H u ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      show ‖(H z : ℂ)‖ ^ 2 = H z ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    -- step 4: the whole-space value bound
    have hval : (∫ x : E3, (((2 * π) ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT c (-x)‖) ^ 2)
        ≤ ∫ u : E3, H u ^ 2 := by
      have h1 : (∫ x : E3, (((2 * π) ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT c (-x)‖) ^ 2)
          = ((2 * π) ^ 3)⁻¹ ^ 2 * ∫ x : E3, ‖Submission.BoseGases.kinFT c (-x)‖ ^ 2 := by
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [mul_pow]
      rw [h1, MeasureTheory.integral_neg_eq_self (fun x : E3 => ‖Submission.BoseGases.kinFT c x‖ ^ 2)
          volume, Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hcint hc_memLp]
      rw [← mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left hle_c (by positivity)) ?_
      rw [Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hHcint hHcmemLp, hHnorm]
      set X : ℝ := ∫ u : E3, H u ^ 2 with hXdef
      refine le_of_eq ?_
      have hP2 : ((2 * π) ^ 3)⁻¹ ^ 2 * (2 * π) ^ 3 * (2 * π) ^ 3 = 1 := by
        have h : (0 : ℝ) < (2 * π) ^ 3 := by positivity
        have h2 : ((2 * π) ^ 3)⁻¹ ^ 2 * ((2 * π) ^ 3) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ h.ne', one_pow]
        calc ((2 * π) ^ 3)⁻¹ ^ 2 * (2 * π) ^ 3 * (2 * π) ^ 3
            = ((2 * π) ^ 3)⁻¹ ^ 2 * ((2 * π) ^ 3) ^ 2 := by ring
          _ = 1 := h2
      calc ((2 * π) ^ 3)⁻¹ ^ 2 * (2 * π) ^ 3 * ((2 * π) ^ 3 * X)
          = (((2 * π) ^ 3)⁻¹ ^ 2 * (2 * π) ^ 3 * (2 * π) ^ 3) * X := by ring
        _ = 1 * X := by rw [hP2]
        _ = X := one_mul X
    -- step 5: assemble
    have hInt : MeasureTheory.Integrable
        (fun x : E3 => (((2 * π) ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT c (-x)‖) ^ 2) := by
      have h2 : MeasureTheory.Integrable (fun x : E3 => ‖Submission.BoseGases.kinFT c (-x)‖ ^ 2) :=
        hck2_int.comp_neg
      refine (h2.const_mul (((2 * π) ^ 3)⁻¹ ^ 2)).congr ?_
      filter_upwards with x
      ring
    have hfin := hstep1
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Eventually.of_forall (fun x => sq_nonneg _))] at hfin
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hH2
      (Eventually.of_forall (fun u => sq_nonneg _))]
    exact le_trans hfin (ENNReal.ofReal_le_ofReal hval)
  · -- the right-hand side is `⊤`
    have hmeas2 : AEStronglyMeasurable (fun u : E3 => H u ^ 2) volume :=
      hψH.aestronglyMeasurable.pow 2
    have htop : (∫⁻ u : E3, ENNReal.ofReal (H u ^ 2)) = ⊤ := by
      have hiff := MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas2
        (Eventually.of_forall (fun u => sq_nonneg _))
      exact not_not.mp (fun hc' => hH2 (hiff.mp hc'))
    rw [htop]
    exact le_top

end Work.PCFU
