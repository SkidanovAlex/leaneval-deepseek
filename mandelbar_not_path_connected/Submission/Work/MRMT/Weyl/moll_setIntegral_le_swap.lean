/-
# The `L¹`-swap estimate for mollifications

This file proves `Work.MRMT.Weyl.moll_setIntegral_le_swap`: for a locally integrable `f : ℂ → ℂ`,
a nonnegative continuous kernel `ρ` with compact support and `∫ ρ = 1`, and a compact set `K`,

  `∫ z in K, ‖moll ρ f z - f z‖ ≤ ∫ y, ρ y * (∫ z in K, ‖f (z - y) - f z‖)`.

The proof combines the pointwise bound `Work.MRMT.Weyl.norm_moll_sub_le` with Tonelli's theorem for
the nonnegative integrand `(y, z) ↦ ρ y * ‖f (z - y) - f z‖`, applied to the product measure
`(volume.restrict K) × volume`; everything is phrased in terms of the `ℝ≥0∞`-valued integral, and
the final Bochner integral is recovered with `integral_eq_lintegral_of_nonneg_ae`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.moll_L1_aux
import Submission.Work.MRMT.Weyl.continuous_setIntegral_translate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

noncomputable section

open Work.MRMT

/-- Measurability of `p ↦ g (p.1 - p.2)` for the product of Lebesgue measure with itself. -/
theorem aemeasurable_comp_sub_fst {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume) :
    AEMeasurable (fun p : ℂ × ℂ => g (p.1 - p.2)) (volume.prod volume) := by
  have h1 : AEMeasurable (fun w : ℂ × ℂ => g w.1) (volume.prod volume) :=
    hg.aemeasurable.comp_fst
  exact h1.comp_quasiMeasurePreserving
    (measurePreserving_sub_prod (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
      ).quasiMeasurePreserving

/-- Measurability of `p ↦ g (p.2 - p.1)` for the product of Lebesgue measure with itself. -/
theorem aemeasurable_comp_sub_snd {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume) :
    AEMeasurable (fun p : ℂ × ℂ => g (p.2 - p.1)) (volume.prod volume) :=
  (aemeasurable_comp_sub_fst hg).comp_quasiMeasurePreserving
    (Measure.measurePreserving_swap (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
      ).quasiMeasurePreserving

/-- A translate of a locally integrable function is integrable on a compact set. -/
theorem integrableOn_comp_sub_right {f : ℂ → ℂ} (hf : LocallyIntegrable f volume)
    {K : Set ℂ} (hK : IsCompact K) (y : ℂ) :
    IntegrableOn (fun z => f (z - y)) K := by
  rw [← integrable_indicator_iff hK.measurableSet]
  set L : Set ℂ := {w | w + y ∈ K} with hL
  have hLc : IsCompact L := by
    have him : (fun z : ℂ => z - y) '' K = {w : ℂ | w + y ∈ K} := by
      ext w
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa using hk
      · intro hw
        exact ⟨w + y, hw, by ring⟩
    rw [hL, ← him]
    exact hK.image (by fun_prop)
  have hLint : Integrable (L.indicator f) volume := by
    rw [integrable_indicator_iff hLc.measurableSet]
    exact hf.integrableOn_isCompact hLc
  have hkey : K.indicator (fun z => f (z - y)) = fun z => (L.indicator f) (z - y) := by
    funext z
    by_cases hz : z ∈ K
    · have h1 : z - y ∈ L := by rw [hL]; simpa using hz
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem h1]
    · have h1 : z - y ∉ L := by rw [hL]; simpa using hz
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem h1]
  rw [hkey]
  exact hLint.comp_sub_right y

/-- **The `L¹`-swap estimate.**  For `f` locally integrable, `ρ ≥ 0` continuous with compact
support and `∫ ρ = 1`, and `K` compact,
`∫ z in K, ‖moll ρ f z - f z‖ ≤ ∫ y, ρ y * (∫ z in K, ‖f (z - y) - f z‖)`. -/
theorem moll_setIntegral_le_swap {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hρ1 : ∫ y, ρ y = 1)
    (hρnn : ∀ y, 0 ≤ ρ y) {K : Set ℂ} (hK : IsCompact K) :
    ∫ z in K, ‖moll ρ f z - f z‖ ≤ ∫ y, ρ y * (∫ z in K, ‖f (z - y) - f z‖) := by
  set Φ : ℂ → ℂ → ℝ≥0∞ := fun z y => ENNReal.ofReal (ρ y) * ‖f (z - y) - f z‖ₑ with hΦ
  have hmollcont : Continuous (moll ρ f) := by
    have h := hρcs.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρc hf
    simpa only [moll] using h
  -- Step 1: write the left-hand side as the `toReal` of an `ℝ≥0∞`-integral.
  have hAEM : AEStronglyMeasurable (fun z => ‖moll ρ f z - f z‖) (volume.restrict K) :=
    ((hmollcont.aestronglyMeasurable.sub hf.aestronglyMeasurable).norm).mono_measure
      Measure.restrict_le_self
  have hLHS : ∫ z in K, ‖moll ρ f z - f z‖ = (∫⁻ z in K, ‖moll ρ f z - f z‖ₑ).toReal := by
    have h1 := integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict K)
      (f := fun z => ‖moll ρ f z - f z‖) (Eventually.of_forall fun z => norm_nonneg _) hAEM
    simpa only [ofReal_norm] using h1
  -- Step 2: the pointwise bound, integrated.
  have hmono : ∫⁻ z in K, ‖moll ρ f z - f z‖ₑ ≤ ∫⁻ z in K, ∫⁻ y, Φ z y := by
    refine lintegral_mono fun z => ?_
    calc ‖moll ρ f z - f z‖ₑ
        ≤ ENNReal.ofReal (∫ y, ρ y * ‖f (z - y) - f z‖) := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_moll_sub_le hf hρc hρcs hρ1 hρnn z)
      _ = ‖∫ y, ρ y * ‖f (z - y) - f z‖‖ₑ := by
          rw [Real.enorm_eq_ofReal (integral_nonneg fun y => mul_nonneg (hρnn y) (norm_nonneg _))]
      _ ≤ ∫⁻ y, ‖ρ y * ‖f (z - y) - f z‖‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, Φ z y := by
          refine lintegral_congr fun y => ?_
          rw [hΦ]
          show ‖ρ y * ‖f (z - y) - f z‖‖ₑ = ENNReal.ofReal (ρ y) * ‖f (z - y) - f z‖ₑ
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg (hρnn y) (norm_nonneg _)),
            ENNReal.ofReal_mul (hρnn y), ofReal_norm]
  -- Step 3: Tonelli.
  have hΦm : AEMeasurable
      (fun p : ℂ × ℂ => ENNReal.ofReal (ρ p.2) * ‖f (p.1 - p.2) - f p.1‖ₑ)
      ((volume.restrict K).prod volume) := by
    have h1 : AEMeasurable (fun p : ℂ × ℂ => ENNReal.ofReal (ρ p.2))
        ((volume.restrict K).prod volume) :=
      (ENNReal.continuous_ofReal.comp (hρc.comp continuous_snd)).aemeasurable
    have h2 : AEMeasurable (fun p : ℂ × ℂ => ‖f (p.1 - p.2) - f p.1‖ₑ)
        ((volume.restrict K).prod volume) := by
      have hsub : AEMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2))
          ((volume.restrict K).prod volume) :=
        (aemeasurable_comp_sub_fst hf.aestronglyMeasurable).mono_measure
          (Measure.prod_mono Measure.restrict_le_self le_rfl)
      have hfst : AEMeasurable (fun p : ℂ × ℂ => f p.1) ((volume.restrict K).prod volume) :=
        (hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self).aemeasurable.comp_fst
      exact (hsub.sub hfst).enorm
    exact h1.mul h2
  have hswap : ∫⁻ z in K, ∫⁻ y, Φ z y = ∫⁻ y, ∫⁻ z in K, Φ z y :=
    lintegral_lintegral_swap (f := Φ) hΦm
  -- Step 4: the inner integral, using that `‖f (· - y) - f ·‖` is integrable on `K`.
  have hinner : ∀ y, ∫⁻ z in K, Φ z y
      = ENNReal.ofReal (ρ y * ∫ z in K, ‖f (z - y) - f z‖) := by
    intro y
    have hJ : Integrable (fun z => ‖f (z - y) - f z‖) (volume.restrict K) :=
      ((integrableOn_comp_sub_right hf hK y).sub (hf.integrableOn_isCompact hK)).norm
    have hJm : AEMeasurable (fun z => ‖f (z - y) - f z‖ₑ) (volume.restrict K) :=
      (((integrableOn_comp_sub_right hf hK y).sub
        (hf.integrableOn_isCompact hK)).aestronglyMeasurable).enorm
    have hkey : (∫⁻ z in K, ‖f (z - y) - f z‖ₑ)
        = ENNReal.ofReal (∫ z in K, ‖f (z - y) - f z‖) := by
      have h1 : (∫⁻ z in K, ‖f (z - y) - f z‖ₑ)
          = ∫⁻ z in K, ENNReal.ofReal ‖f (z - y) - f z‖ :=
        lintegral_congr fun z => (ofReal_norm (f (z - y) - f z)).symm
      rw [h1, ← ofReal_integral_eq_lintegral_ofReal hJ (Eventually.of_forall fun z => norm_nonneg _)]
    rw [hΦ]
    simp only
    rw [lintegral_const_mul'' (ENNReal.ofReal (ρ y)) hJm]
    rw [hkey]
    rw [← ENNReal.ofReal_mul (hρnn y)]
  have hEq : ∫⁻ z in K, ∫⁻ y, Φ z y
      = ∫⁻ y, ENNReal.ofReal (ρ y * ∫ z in K, ‖f (z - y) - f z‖) := by
    rw [hswap]
    exact lintegral_congr hinner
  -- Step 5: identify the `toReal` of the `ℝ≥0∞`-integral with a Bochner integral.
  have hJcont : Continuous (fun y : ℂ => ∫ z in K, ‖f (z - y) - f z‖) :=
    (continuous_setIntegral_translate hf hK).comp continuous_neg
  have hsupp : HasCompactSupport (fun y : ℂ => ρ y * ∫ z in K, ‖f (z - y) - f z‖) :=
    hρcs.mul_right
  have hint : Integrable (fun y : ℂ => ρ y * ∫ z in K, ‖f (z - y) - f z‖) volume :=
    (hρc.mul hJcont).integrable_of_hasCompactSupport hsupp
  have hnn : ∀ y : ℂ, 0 ≤ ρ y * ∫ z in K, ‖f (z - y) - f z‖ :=
    fun y => mul_nonneg (hρnn y) (integral_nonneg fun z => norm_nonneg _)
  have htoReal : (∫⁻ y, ENNReal.ofReal (ρ y * ∫ z in K, ‖f (z - y) - f z‖)).toReal
      = ∫ y, ρ y * (∫ z in K, ‖f (z - y) - f z‖) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
    exact ENNReal.toReal_ofReal (integral_nonneg hnn)
  have hbne : (∫⁻ z in K, ∫⁻ y, Φ z y) ≠ ⊤ := by
    rw [hEq, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
    exact ENNReal.ofReal_ne_top
  rw [hLHS]
  calc (∫⁻ z in K, ‖moll ρ f z - f z‖ₑ).toReal
      ≤ (∫⁻ z in K, ∫⁻ y, Φ z y).toReal := ENNReal.toReal_mono hbne hmono
    _ = (∫⁻ y, ENNReal.ofReal (ρ y * ∫ z in K, ‖f (z - y) - f z‖)).toReal := by rw [hEq]
    _ = ∫ y, ρ y * (∫ z in K, ‖f (z - y) - f z‖) := htoReal

end

end Work.MRMT.Weyl
