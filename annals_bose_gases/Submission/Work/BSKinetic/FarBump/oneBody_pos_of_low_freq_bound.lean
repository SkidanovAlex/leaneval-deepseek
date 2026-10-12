import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BSKinetic.plancherel_pconv
import Submission.Work.SmallBoxTBWord.integrable_kinFT_energy_cspt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.FarBump.oneBody_pos_of_low_freq_bound`

The positive-mass bound for the `fsKinCoeff`-weighted kinetic energy: if the low-frequency part
`‖p‖ ≤ R` of the Fourier transform of a smooth compactly supported real `φ` carries strictly less
than the *total* Plancherel mass `(2π)³∫φ²`, then the `[‖p‖−c]₊²`-weighted kinetic integral is
strictly positive, provided `c < R`.

## Proof

Write `F p = ‖kinFT φ p‖²` and `A = (2π)³`.  Plancherel (`plancherel_pconv`) reads
`A⁻¹∫_p F p = ∫_x φ(x)²`, so the hypothesis `∫_{‖p‖<R} F < A∫φ² = ∫_p F` says exactly that the
*far* frequencies `‖p‖ ≥ R` carry positive `F`-mass:

    `0 < ∫_{‖p‖ ≥ R} F p = ∫_p F p − ∫_{‖p‖<R} F p`   (`integral_add_compl`).

On that region `‖p‖ ≥ R > c`, and `c ↦ [r−c]₊²` is monotone in `r` above `c`
(`fsKinCoeff_mono`), so `[R−c]₊² = (R−c)² ≤ [‖p‖−c]₊²` there.  Hence

    `(R−c)² · ∫_{‖p‖ ≥ R} F ≤ ∫_{‖p‖ ≥ R} [‖p‖−c]₊² F ≤ ∫_p [‖p‖−c]₊² F`,

the last step because the integrand is nonnegative, and the left side is a product of two strictly
positive numbers.  Multiplying by the positive constant `A⁻¹` finishes.

The only integrability input is `fsKinCoeff c ‖p‖ ≤ 2‖p‖² + 2c²`, which dominates the weighted
integrand by `2‖p‖²F p + 2c²F p` — integrable by
`integrable_kinFT_energy_cspt` together with `integrable_kinFT_sq`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real ENNReal

namespace Work.BSKinetic.FarBump

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `[r−c]₊²` coefficient is dominated by `2r² + 2c²`: indeed
`max (r−c) 0 ≤ |r−c| ≤ |r| + |c|` so `[r−c]₊² ≤ (|r|+|c|)² ≤ 2r² + 2c²`. -/
private lemma fsKinCoeff_le_two_sq_add (c r : ℝ) :
    Submission.BoseGases.fsKinCoeff c r ≤ 2 * r ^ 2 + 2 * c ^ 2 := by
  have hmax : max (r - c) 0 ≤ |r| + |c| := by
    refine max_le (by linarith [le_abs_self r, neg_le_abs c]) (by positivity)
  have h3 : (0 : ℝ) ≤ max (r - c) 0 := le_max_right _ _
  calc Submission.BoseGases.fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
    _ ≤ (|r| + |c|) ^ 2 := pow_le_pow_left₀ h3 hmax 2
    _ ≤ 2 * r ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (|r| - |c|), sq_abs r, sq_abs c]

/-- `r ↦ [r−c]₊²` is continuous. -/
private lemma continuous_fsKinCoeff (c : ℝ) :
    Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
  simp only [Submission.BoseGases.fsKinCoeff]
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

theorem oneBody_pos_of_low_freq_bound {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφs : ContDiff ℝ (⊤ : ENat) φ) (hφc : HasCompactSupport φ) {c R : ℝ}
    (hRc : c < R) (hR0 : 0 ≤ R)
    (hlow : (∫ p in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (φ z : ℂ)) p‖ ^ 2)
        < (2 * Real.pi) ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), (φ x) ^ 2) :
    0 < ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (φ z : ℂ)) p‖ ^ 2 := by
  set F : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun p => ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (φ z : ℂ)) p‖ ^ 2
    with hFdef
  set s : Set (EuclideanSpace ℝ (Fin 3)) := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R
    with hsdef
  have hs_meas : MeasurableSet s := Metric.isOpen_ball.measurableSet
  -- the hypothesis, in terms of `F` and `s`
  have hlow_s : (∫ p in s, F p)
      < (2 * Real.pi) ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), (φ x) ^ 2 := hlow
  have hF_int : Integrable F := Work.BSKinetic.integrable_kinFT_sq φ hφs hφc
  have hplan : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), F p
      = ∫ x : EuclideanSpace ℝ (Fin 3), (φ x) ^ 2 :=
    Work.BSKinetic.plancherel_pconv φ hφs hφc
  have hApos : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  -- Plancherel, solved for the total `F`-mass
  have hInt_eq : (2 * Real.pi) ^ 3 * (∫ x : EuclideanSpace ℝ (Fin 3), (φ x) ^ 2)
      = ∫ p : EuclideanSpace ℝ (Fin 3), F p := by
    rw [← hplan, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hApos), one_mul]
  rw [hInt_eq] at hlow_s
  -- the far-frequency mass is positive
  have hcompl : (∫ p in sᶜ, F p)
      = (∫ p : EuclideanSpace ℝ (Fin 3), F p) - (∫ p in s, F p) := by
    have h := MeasureTheory.integral_add_compl (μ := volume) hs_meas hF_int
    linarith
  have hpos_c : 0 < ∫ p in sᶜ, F p := by rw [hcompl]; linarith
  have hFnn : ∀ p, 0 ≤ F p := fun p => pow_nonneg (norm_nonneg _) 2
  -- on the far region the coefficient dominates `[R−c]₊²`
  have hpt : ∀ p ∈ sᶜ, Submission.BoseGases.fsKinCoeff c R * F p ≤
      Submission.BoseGases.fsKinCoeff c ‖p‖ * F p := by
    intro p hp
    have hpR : R ≤ ‖p‖ := by
      have h1 : ¬ (p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) := hp
      rw [Metric.mem_ball, dist_zero_right] at h1
      exact not_lt.mp h1
    exact mul_le_mul_of_nonneg_right
      (Submission.BoseGases.fsKinCoeff_mono (le_of_lt hRc) hpR) (hFnn p)
  -- integrability of the weighted integrand
  have hdom : Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * F p) := by
    have h1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * F p) :=
      Work.SmallBoxTBWord.integrable_kinFT_energy_cspt φ hφs hφc
    have h := (h1.const_mul 2).add (hF_int.const_mul (2 * c ^ 2))
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.add_apply]
    ring
  have hmeas : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖ * F p)
      volume :=
    (((continuous_fsKinCoeff c).comp continuous_norm).aestronglyMeasurable).mul
      hF_int.aestronglyMeasurable
  have hg_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖p‖ * F p) := by
    refine hdom.mono' hmeas (Filter.Eventually.of_forall (fun p => ?_))
    have h1 : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖
    have h2 : 0 ≤ F p := hFnn p
    rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
    exact mul_le_mul_of_nonneg_right (fsKinCoeff_le_two_sq_add c ‖p‖) h2
  have hcoefR : 0 < Submission.BoseGases.fsKinCoeff c R := by
    rw [Submission.BoseGases.fsKinCoeff, max_eq_left (by linarith : (0 : ℝ) ≤ R - c)]
    exact pow_pos (by linarith : (0 : ℝ) < R - c) 2
  -- the chain of inequalities
  have hstep1 : Submission.BoseGases.fsKinCoeff c R * (∫ p in sᶜ, F p)
      = ∫ p in sᶜ, Submission.BoseGases.fsKinCoeff c R * F p := by
    rw [MeasureTheory.integral_const_mul]
  have hstep2 : (∫ p in sᶜ, Submission.BoseGases.fsKinCoeff c R * F p)
      ≤ ∫ p in sᶜ, Submission.BoseGases.fsKinCoeff c ‖p‖ * F p := by
    refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
    · exact (hF_int.const_mul _).integrableOn
    · exact hg_int.integrableOn
    · show ∀ᵐ p ∂(volume.restrict sᶜ), Submission.BoseGases.fsKinCoeff c R * F p
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ * F p
      rw [MeasureTheory.ae_restrict_iff' hs_meas.compl]
      exact Filter.Eventually.of_forall (fun p hp => hpt p hp)
  have hstep3 : (∫ p in sᶜ, Submission.BoseGases.fsKinCoeff c ‖p‖ * F p)
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ * F p :=
    MeasureTheory.setIntegral_le_integral hg_int
      (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (hFnn p)))
  have hpos_int : 0 < ∫ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff c ‖p‖ * F p := by
    have h2 : 0 < Submission.BoseGases.fsKinCoeff c R * (∫ p in sᶜ, F p) :=
      mul_pos hcoefR hpos_c
    linarith [hstep1 ▸ h2, hstep2, hstep3]
  exact mul_pos (inv_pos.mpr hApos) hpos_int

end Work.BSKinetic.FarBump
