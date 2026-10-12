import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.kp_schur_pairing_le`

**Why this file exists.**  The proved module `Submission/Work/BoseBoxFock/schur_pairing_le.lean`
provides exactly the Schur test used by `PCFU/chCslot_kernelPair`, but its auxiliary lemma
`Work.BoseBoxFock.ofReal_integral_le_lintegral` collides with the identically named lemma that is
already in that file's import cone (from `Submission/Work/BoseBoxFock/B13Main.lean`), so the two
modules cannot be imported together (`import ... failed, environment already contains ...`).

This file is therefore a *verbatim copy* of `schur_pairing_le.lean` with every helper moved into the
namespace `Work.BoseBoxFock.PCFU` and prefixed by `kp_` (so nothing can collide), and with the
final theorem renamed `kp_schur_pairing_le`.  The mathematics and the proof term are unchanged.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

/-- For a nonnegative real function `h` one has `ENNReal.ofReal (∫ h) ≤ ∫⁻ ENNReal.ofReal h`.
(No measurability hypothesis is needed: if `h` is not integrable then both sides are `0`.) -/
lemma kp_ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → ℝ}
    (h0 : 0 ≤ᵐ[μ] h) :
    ENNReal.ofReal (∫ a, h a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (h a) ∂μ := by
  by_cases hint : Integrable h μ
  · rw [ofReal_integral_eq_lintegral_ofReal hint h0]
  · rw [integral_undef hint]
    simp

section SchurTest

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- **Schur's test** for a measurable kernel `K` whose `w`-slices have
`∫⁻ z, ‖K w z‖ ≤ a` and whose `z`-slices have `∫⁻ w, ‖K w z‖ ≤ b`, paired against `L²`
functions `f` and `g`. -/
theorem kp_schur_pairing_le_aux {K : α → β → ℂ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod ν))
    (hwa : ∀ᵐ w ∂μ, ∫⁻ z, ENNReal.ofReal ‖K w z‖ ∂ν ≤ ENNReal.ofReal a)
    (hwb : ∀ᵐ z ∂ν, ∫⁻ w, ENNReal.ofReal ‖K w z‖ ∂μ ≤ ENNReal.ofReal b)
    {f : α → ℂ} {g : β → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    ‖∫ w, ∫ z, f w * K w z * g z ∂ν ∂μ‖
      ≤ Real.sqrt (a * b) * Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂μ)
          * Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂ν) := by
  have hf2 : Integrable (fun w => ‖f w‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.norm).mp hf.norm
  have hg2 : Integrable (fun z => ‖g z‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable.norm).mp hg.norm
  have hA2nn : 0 ≤ ∫ w, ‖f w‖ ^ 2 ∂μ := integral_nonneg fun w => by positivity
  have hB2nn : 0 ≤ ∫ z, ‖g z‖ ^ 2 ∂ν := integral_nonneg fun z => by positivity
  have hIf : (∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ)
      = ENNReal.ofReal (∫ w, ‖f w‖ ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hf2
      (Filter.Eventually.of_forall fun w => by positivity)).symm
  have hIg : (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂ν)
      = ENNReal.ofReal (∫ z, ‖g z‖ ^ 2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hg2
      (Filter.Eventually.of_forall fun z => by positivity)).symm
  -- measurability of the building blocks
  have hf1 : AEMeasurable (fun p : α × β => f p.1) (μ.prod ν) := hf.aemeasurable.comp_fst
  have hg1 : AEMeasurable (fun p : α × β => g p.2) (μ.prod ν) := hg.aemeasurable.comp_snd
  have hK1 : AEMeasurable (fun p : α × β => K p.1 p.2) (μ.prod ν) := hK.aemeasurable
  have hfA : AEMeasurable (fun p : α × β => ‖f p.1‖ ^ 2) (μ.prod ν) := (hf1.norm).pow_const 2
  have hgB : AEMeasurable (fun p : α × β => ‖g p.2‖ ^ 2) (μ.prod ν) := (hg1.norm).pow_const 2
  have hKm : AEMeasurable (fun p : α × β => ‖K p.1 p.2‖) (μ.prod ν) := hK1.norm
  -- the two weighted `L¹` estimates
  have hL1 : ∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖) ∂(μ.prod ν)
      ≤ ENNReal.ofReal a * (∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ) := by
    have hmeas : AEMeasurable
        (Function.uncurry fun w (z : β) => ENNReal.ofReal (‖f w‖ ^ 2 * ‖K w z‖)) (μ.prod ν) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hfA.mul hKm)
    calc ∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖) ∂(μ.prod ν)
        = ∫⁻ w, ∫⁻ z, ENNReal.ofReal (‖f w‖ ^ 2 * ‖K w z‖) ∂ν ∂μ :=
          (lintegral_lintegral hmeas).symm
      _ = ∫⁻ w, ∫⁻ z, ENNReal.ofReal (‖f w‖ ^ 2) * ENNReal.ofReal ‖K w z‖ ∂ν ∂μ := by
          refine lintegral_congr fun w => lintegral_congr fun z => ?_
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) * (∫⁻ z, ENNReal.ofReal ‖K w z‖ ∂ν) ∂μ := by
          refine lintegral_congr fun w => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) * ENNReal.ofReal a ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hwa] with w hw
          exact mul_le_mul_of_nonneg_left hw (by simp)
      _ = ENNReal.ofReal a * ∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun w => mul_comm _ _
  have hL2 : ∫⁻ p : α × β, ENNReal.ofReal (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2) ∂(μ.prod ν)
      ≤ ENNReal.ofReal b * (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂ν) := by
    have hmeas : AEMeasurable
        (fun p : α × β => ENNReal.ofReal (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2)) (μ.prod ν) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hKm.mul hgB)
    calc ∫⁻ p : α × β, ENNReal.ofReal (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2) ∂(μ.prod ν)
        = ∫⁻ z, ∫⁻ w, ENNReal.ofReal (‖K w z‖ * ‖g z‖ ^ 2) ∂μ ∂ν :=
          lintegral_prod_symm _ hmeas
      _ = ∫⁻ z, ∫⁻ w, ENNReal.ofReal (‖g z‖ ^ 2) * ENNReal.ofReal ‖K w z‖ ∂μ ∂ν := by
          refine lintegral_congr fun z => lintegral_congr fun w => ?_
          rw [ENNReal.ofReal_mul (by positivity), mul_comm]
      _ = ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) * (∫⁻ w, ENNReal.ofReal ‖K w z‖ ∂μ) ∂ν := by
          refine lintegral_congr fun z => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) * ENNReal.ofReal b ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hwb] with z hz
          exact mul_le_mul_of_nonneg_left hz (by simp)
      _ = ENNReal.ofReal b * ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂ν := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun z => mul_comm _ _
  -- pointwise algebra
  have hFG : ∀ p : α × β,
      ENNReal.ofReal (Real.sqrt (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖))
        * ENNReal.ofReal (Real.sqrt (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2))
      = ENNReal.ofReal (‖f p.1‖ * ‖K p.1 p.2‖ * ‖g p.2‖) := by
    intro p
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
    congr 1
    calc ‖f p.1‖ * Real.sqrt ‖K p.1 p.2‖ * (Real.sqrt ‖K p.1 p.2‖ * ‖g p.2‖)
        = ‖f p.1‖ * (Real.sqrt ‖K p.1 p.2‖ * Real.sqrt ‖K p.1 p.2‖) * ‖g p.2‖ := by ring
      _ = ‖f p.1‖ * ‖K p.1 p.2‖ * ‖g p.2‖ := by
          rw [show Real.sqrt ‖K p.1 p.2‖ * Real.sqrt ‖K p.1 p.2‖ = ‖K p.1 p.2‖ from by
            rw [← pow_two, Real.sq_sqrt (norm_nonneg _)]]
  have hFsq : ∀ p : α × β,
      (ENNReal.ofReal (Real.sqrt (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖))) ^ (2 : ℝ)
      = ENNReal.ofReal (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖) := by
    intro p
    rw [ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hGsq : ∀ p : α × β,
      (ENNReal.ofReal (Real.sqrt (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2))) ^ (2 : ℝ)
      = ENNReal.ofReal (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2) := by
    intro p
    rw [ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hFmeas : AEMeasurable
      (fun p : α × β => ENNReal.ofReal (Real.sqrt (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖))) (μ.prod ν) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hfA.mul hKm).sqrt
  have hGmeas : AEMeasurable
      (fun p : α × β => ENNReal.ofReal (Real.sqrt (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2))) (μ.prod ν) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hKm.mul hgB).sqrt
  have hHolder :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod ν) Real.HolderConjugate.two_two hFmeas hGmeas
  -- the weighted `L¹` bound on the product space
  have hmain : ∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ * ‖K p.1 p.2‖ * ‖g p.2‖) ∂(μ.prod ν)
      ≤ ENNReal.ofReal (Real.sqrt (a * b) * Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂μ)
          * Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂ν)) := by
    calc ∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ * ‖K p.1 p.2‖ * ‖g p.2‖) ∂(μ.prod ν)
        = ∫⁻ p : α × β, ENNReal.ofReal (Real.sqrt (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖))
            * ENNReal.ofReal (Real.sqrt (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2)) ∂(μ.prod ν) :=
          lintegral_congr fun p => (hFG p).symm
      _ ≤ (∫⁻ p : α × β,
              (ENNReal.ofReal (Real.sqrt (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖))) ^ (2 : ℝ) ∂(μ.prod ν)) ^ (1/2 : ℝ)
            * (∫⁻ p : α × β,
              (ENNReal.ofReal (Real.sqrt (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2))) ^ (2 : ℝ) ∂(μ.prod ν)) ^ (1/2 : ℝ) :=
          hHolder
      _ = (∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖) ∂(μ.prod ν)) ^ (1/2 : ℝ)
            * (∫⁻ p : α × β, ENNReal.ofReal (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2) ∂(μ.prod ν)) ^ (1/2 : ℝ) := by
          exact congrArg₂ (fun (x : ENNReal) (y : ENNReal) => x ^ (1/2:ℝ) * y ^ (1/2:ℝ))
            (lintegral_congr fun p => hFsq p) (lintegral_congr fun p => hGsq p)
      _ ≤ (ENNReal.ofReal a * ∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ) ^ (1/2 : ℝ)
            * (ENNReal.ofReal b * ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂ν) ^ (1/2 : ℝ) := by
          have h1 : (∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ ^ 2 * ‖K p.1 p.2‖) ∂(μ.prod ν)) ^ (1/2 : ℝ)
              ≤ (ENNReal.ofReal a * ∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ) ^ (1/2 : ℝ) :=
            ENNReal.rpow_le_rpow hL1 (by norm_num : (0:ℝ) ≤ 1/2)
          have h2 : (∫⁻ p : α × β, ENNReal.ofReal (‖K p.1 p.2‖ * ‖g p.2‖ ^ 2) ∂(μ.prod ν)) ^ (1/2 : ℝ)
              ≤ (ENNReal.ofReal b * ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂ν) ^ (1/2 : ℝ) :=
            ENNReal.rpow_le_rpow hL2 (by norm_num : (0:ℝ) ≤ 1/2)
          exact mul_le_mul h1 h2 bot_le bot_le
      _ = ENNReal.ofReal (Real.sqrt (a * b) * Real.sqrt (∫ w, ‖f w‖ ^ 2 ∂μ)
            * Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂ν)) := by
          have hA' : ENNReal.ofReal a * (∫⁻ w, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ)
              = ENNReal.ofReal (a * ∫ w, ‖f w‖ ^ 2 ∂μ) := by
            rw [hIf, ← ENNReal.ofReal_mul ha]
          have hB' : ENNReal.ofReal b * (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂ν)
              = ENNReal.ofReal (b * ∫ z, ‖g z‖ ^ 2 ∂ν) := by
            rw [hIg, ← ENNReal.ofReal_mul hb]
          rw [hA', hB',
            ENNReal.ofReal_rpow_of_nonneg (x := a * ∫ w, ‖f w‖ ^ 2 ∂μ) (p := 1/2)
              (mul_nonneg ha hA2nn) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (x := b * ∫ z, ‖g z‖ ^ 2 ∂ν) (p := 1/2)
              (mul_nonneg hb hB2nn) (by norm_num),
            ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
            ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
          congr 1
          have h3 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b
          rw [Real.sqrt_mul ha, Real.sqrt_mul hb, h3]
          ring
  -- bound the pairing by the weighted `L¹` norm on the product space
  have hLHS : ENNReal.ofReal ‖∫ w, ∫ z, f w * K w z * g z ∂ν ∂μ‖
      ≤ ∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ * ‖K p.1 p.2‖ * ‖g p.2‖) ∂(μ.prod ν) := by
    have hmeas : AEMeasurable
        (Function.uncurry fun w (z : β) => ENNReal.ofReal ‖f w * K w z * g z‖) (μ.prod ν) :=
      ENNReal.measurable_ofReal.comp_aemeasurable ((hf1.mul hK1).mul hg1).norm
    calc ENNReal.ofReal ‖∫ w, ∫ z, f w * K w z * g z ∂ν ∂μ‖
        ≤ ENNReal.ofReal (∫ w, ‖∫ z, f w * K w z * g z ∂ν‖ ∂μ) :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
      _ ≤ ∫⁻ w, ENNReal.ofReal (‖∫ z, f w * K w z * g z ∂ν‖) ∂μ :=
          kp_ofReal_integral_le_lintegral (Filter.Eventually.of_forall fun w => norm_nonneg _)
      _ ≤ ∫⁻ w, ∫⁻ z, ENNReal.ofReal (‖f w * K w z * g z‖) ∂ν ∂μ := by
          refine lintegral_mono fun w => ?_
          exact (ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)).trans
            (kp_ofReal_integral_le_lintegral (Filter.Eventually.of_forall fun z => norm_nonneg _))
      _ = ∫⁻ p : α × β, ENNReal.ofReal (‖f p.1 * K p.1 p.2 * g p.2‖) ∂(μ.prod ν) :=
          lintegral_lintegral hmeas
      _ = ∫⁻ p : α × β, ENNReal.ofReal (‖f p.1‖ * ‖K p.1 p.2‖ * ‖g p.2‖) ∂(μ.prod ν) := by
          refine lintegral_congr fun p => ?_
          rw [norm_mul, norm_mul]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hLHS.trans hmain)

end SchurTest

theorem kp_schur_pairing_le {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : MeasureTheory.AEStronglyMeasurable (Function.uncurry K)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))))
    (hwa : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∫⁻ z, ENNReal.ofReal ‖K w z‖ ≤ ENNReal.ofReal a)
    (hwb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ∫⁻ w, ENNReal.ofReal ‖K w z‖ ≤ ENNReal.ofReal b)
    {f g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    ‖∫ w : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3), f w * K w z * g z‖
      ≤ Real.sqrt (a * b) * Real.sqrt (∫ w : EuclideanSpace ℝ (Fin 3), ‖f w‖ ^ 2)
          * Real.sqrt (∫ z : EuclideanSpace ℝ (Fin 3), ‖g z‖ ^ 2) :=
  kp_schur_pairing_le_aux ha hb hK hwa hwb hf hg

end Work.BoseBoxFock.PCFU
