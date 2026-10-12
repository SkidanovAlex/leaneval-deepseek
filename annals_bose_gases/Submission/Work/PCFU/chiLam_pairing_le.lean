import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.chiLam_pairing_le` — the Cauchy–Schwarz estimate for the `χ_ℓ`-windowed pairing

For `ℓ > 0` and a pointwise bound `‖χ_ℓ(z)·F(z)‖ ≤ K` on the windowed pairing function, the
Bochner integral of `χ_ℓ·F·Γ` against an `AEStronglyMeasurable` `Γ` satisfies

    ‖∫_z χ_ℓ(z)·F(z)·Γ(z)‖ₑ ≤ ofReal (K·√(ℓ³)) · (∫⁻_z ‖Γ(z)‖ₑ²)^{1/2} .

The constant is **sharp**: `√(ℓ³) = (volume (boxL ℓ))^{1/2}` is the exact `L²`-mass of the window,
so the estimate is Hölder (`p = q = 2`) applied to

    `∫⁻_z ‖χ_ℓ(z)F(z)‖ₑ·‖Γ(z)‖ₑ ≤ ofReal K · ∫⁻_z 1_{boxL ℓ}(z)·‖Γ(z)‖ₑ
       ≤ ofReal K · (volume (boxL ℓ))^{1/2}·(∫⁻_z ‖Γ(z)‖ₑ²)^{1/2}`,

where the first inequality uses that `χ_ℓ` vanishes off the box `boxL ℓ = ℓ • cell` (a fact about
the corpus localization function `Work.BoseK15.corpusBox.chiLam`) and the second is Hölder on the
indicator of the box. No integrability of `Γ` is needed: the Bochner integral is controlled by the
`enorm` of the integrand (`enorm_integral_le_lintegral_enorm`), and the whole estimate lives in
`ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chiLam_pairing_le {ℓ K : ℝ} (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    {F Γ : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hKer : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z‖ ≤ K)
    (hΓ : MeasureTheory.AEStronglyMeasurable Γ MeasureTheory.volume) :
    ‖∫ z : EuclideanSpace ℝ (Fin 3),
        (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z * Γ z‖ₑ
      ≤ ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
        * (∫⁻ z : EuclideanSpace ℝ (Fin 3), ‖Γ z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  -- the box supporting `χ_ℓ` and its `ℝ≥0∞`-valued indicator
  have hbLmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
  have hsupp : ∀ z : E3, Work.BoseK15.corpusBox.chiLam ℓ z ≠ 0 →
      z ∈ Work.BoseK15.corpusBox.boxL ℓ :=
    fun z hz => Work.BoseB4.BoxData.chiLam_supp _ hℓ hz
  -- **pointwise step**: `‖χ_ℓ(z)·F(z)‖ₑ ≤ ofReal K · 1_{boxL ℓ}(z)`
  have hGle : ∀ z : E3,
      ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z‖ₑ
      ≤ ENNReal.ofReal K * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z := by
    intro z
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem hz, mul_one, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hKer z)
    · -- off the box `χ_ℓ` vanishes, so the pairing function is identically `0` there
      have hz0 : Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
        by_contra h; exact hz (hsupp z h)
      have hc0 : (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) = 0 := by
        rw [hz0]; simp
      rw [hc0, zero_mul, Set.indicator_of_notMem hz, mul_zero]
      simp
  have hu_meas : Measurable
      ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hbLmeas
  -- Bochner integral controlled by the `enorm` of the integrand
  have h1 : ‖∫ z : E3,
        (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z * Γ z‖ₑ
      ≤ ∫⁻ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z * Γ z‖ₑ :=
    MeasureTheory.enorm_integral_le_lintegral_enorm (μ := volume) _
  -- multiplicativity of `enorm`
  have h2 : ∫⁻ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z * Γ z‖ₑ
      = ∫⁻ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z‖ₑ * ‖Γ z‖ₑ := by
    refine lintegral_congr (fun z => ?_)
    rw [enorm_mul]
  -- insert the pointwise bound
  have h3 : ∫⁻ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z‖ₑ * ‖Γ z‖ₑ
      ≤ ∫⁻ z : E3,
        (ENNReal.ofReal K * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z)
          * ‖Γ z‖ₑ := by
    refine lintegral_mono (fun z => ?_)
    exact mul_le_mul_left (hGle z) _
  -- pull out the constant
  have h4 : ∫⁻ z : E3,
        (ENNReal.ofReal K * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z)
          * ‖Γ z‖ₑ
      = ENNReal.ofReal K * ∫⁻ z : E3,
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z * ‖Γ z‖ₑ := by
    rw [← lintegral_const_mul' (ENNReal.ofReal K)
      (fun z : E3 =>
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z * ‖Γ z‖ₑ)
      ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun z => ?_)
    rw [mul_assoc]
  -- Hölder with `p = q = 2` on the box indicator and `‖Γ‖ₑ`
  have h5 : ∫⁻ z : E3,
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z * ‖Γ z‖ₑ
      ≤ (∫⁻ z : E3,
          ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∫⁻ z : E3, ‖Γ z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have hp : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hp
      (f := fun z : E3 =>
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z)
      (g := fun z : E3 => ‖Γ z‖ₑ)
      hu_meas.aemeasurable hΓ.enorm
    simpa using this
  -- the second moment of the box indicator is exactly the volume of the box
  have hu_sq : ∫⁻ z : E3,
        ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z) ^ (2 : ℝ)
      = ENNReal.ofReal (ℓ ^ 3) := by
    have hpoint : ∀ z : E3,
        ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z) ^ (2 : ℝ)
        = (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z := by
      intro z
      by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hz, ENNReal.one_rpow]
      · rw [Set.indicator_of_notMem hz, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [lintegral_congr hpoint, lintegral_indicator_const hbLmeas 1, one_mul]
    exact Work.BoseB4.BoxData.volume_boxL _ hℓ
  have hsqrt : (ENNReal.ofReal (ℓ ^ 3)) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (ℓ ^ 3)) := by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  calc ‖∫ z : E3, (((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z * Γ z‖ₑ
      ≤ ∫⁻ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z * Γ z‖ₑ := h1
    _ = ∫⁻ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) * F z‖ₑ * ‖Γ z‖ₑ := h2
    _ ≤ ∫⁻ z : E3,
        (ENNReal.ofReal K * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z)
          * ‖Γ z‖ₑ := h3
    _ = ENNReal.ofReal K * ∫⁻ z : E3,
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z * ‖Γ z‖ₑ := h4
    _ ≤ ENNReal.ofReal K *
          ((∫⁻ z : E3,
              ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ENNReal)) z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫⁻ z : E3, ‖Γ z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_right h5 (ENNReal.ofReal K)
    _ = ENNReal.ofReal K *
          (ENNReal.ofReal (Real.sqrt (ℓ ^ 3))
            * (∫⁻ z : E3, ‖Γ z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        rw [hu_sq, hsqrt]
    _ = ENNReal.ofReal (K * Real.sqrt (ℓ ^ 3))
          * (∫⁻ z : E3, ‖Γ z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul hK, mul_assoc]

end Work.PCFU
