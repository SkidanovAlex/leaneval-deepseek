import Mathlib
import Submission.Work.GM.Affine.region_II_resonant_high_defs
import Submission.Work.GM.Affine.window_integral_Bsum
import Submission.Work.GM.Affine.region_I_bound

/-!
# GM §9, region II (high part): the integral of the resonant majorant

This file proves `Work.GM.Affine.resMajorant_integral_le`, the step (iii)+(iv) of the strategy of
`region_II_resonant_high`: the resonant-pair majorant

`resMajorant M₁ M₂ M₃ T f ξ
   = ∑_{(m₁,ℓ) ∈ R1 M₁ × [-⌈T⁶⌉-2, ⌈T⁶⌉+2]} [|ℓ - ξ/m₁| ≤ 2/M₃] · m₁^{-2} ‖Bsum f M₂ (ξ/m₁)‖²`

integrated over `resRegion T M₁ M₃ = [-T⁶,T⁶] \ [-4M₁/M₃, 4M₁/M₃]` is at most `(8/M₃) WinMass`.

The proof is bookkeeping plus one exact change of variables:
* the integral of the finite sum is the sum of the integrals (`lintegral`/`lintegral_finsetSum`,
  so that no integrability is needed; all summands are nonnegative);
* each summand is `[|ℓ - ξ/m₁| ≤ 2/M₃] · m₁^{-2} ‖Bsum f M₂ (ξ/m₁)‖²`, i.e. the indicator of the
  window `[m₁ℓ - 2|m₁|/M₃, m₁ℓ + 2|m₁|/M₃]` times `m₁^{-2}‖Bsum f M₂ (·/m₁)‖²`; the integral of
  the indicator over `resRegion` is at most the integral over the whole window, which by
  `window_integral_Bsum` equals `m₁^{-2}·(|m₁|/M₃)·∫_{[-2,2]} ‖Hfun f M₂ M₃ ℓ τ‖² dτ`
  `= (1/(|m₁| M₃))·∫_{[-2,2]} ‖Hfun f M₂ M₃ ℓ τ‖² dτ`;
* summing over `ℓ` and applying the hypothesis `hwin` (a finite window mass is at most `WinMass`)
  leaves `Σ_{m₁ ∈ R1 M₁} 1/(|m₁| M₃) ≤ 8/M₃`, by `sum_inv_abs_R1_le`.
-/

open MeasureTheory Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The resonant window of the pair `(m, ℓ)` is the interval used in `window_integral_Bsum`. -/
private lemma mem_resWin {M₃ : ℝ} (_hM₃ : 0 < M₃) {m : ℤ} (hm : m ≠ 0) (ℓ : ℤ) (ξ : ℝ) :
    ξ ∈ Set.Icc ((m:ℝ)*(ℓ:ℝ) - 2*|(m:ℝ)|/M₃) ((m:ℝ)*(ℓ:ℝ) + 2*|(m:ℝ)|/M₃)
      ↔ |(ℓ:ℝ) - ξ/(m:ℝ)| ≤ 2/M₃ := by
  have hmR : (m:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hma : 0 < |(m:ℝ)| := abs_pos.mpr hmR
  rw [Set.mem_Icc]
  have hkey : (ℓ:ℝ) - ξ/(m:ℝ) = ((m:ℝ)*(ℓ:ℝ) - ξ)/(m:ℝ) := by field_simp
  rw [hkey, abs_div, div_le_iff₀ hma,
    show (2/M₃) * |(m:ℝ)| = 2*|(m:ℝ)|/M₃ by ring, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- `∫⁻` of an indicator over `t` is the `∫⁻` over `t ∩ s`. -/
private lemma lintegral_indicator_restrict {s t : Set ℝ} (hs : MeasurableSet s)
    (h : ℝ → ENNReal) :
    ∫⁻ x in t, s.indicator h x = ∫⁻ x in t ∩ s, h x := by
  rw [lintegral_indicator hs, Measure.restrict_restrict hs, Set.inter_comm]

/-- The `∫⁻` over an arbitrary set `R` of one summand of `resMajorant` is at most the full
window mass of the pair `(m, ℓ)`. -/
private lemma key_pair_bound {M₂ M₃ : ℝ} (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (R : Set ℝ) {m : ℤ} (hm : m ≠ 0) (ℓ : ℤ) :
    ∫⁻ ξ in R, ENNReal.ofReal
        (if |(ℓ:ℝ) - ξ/(m:ℝ)| ≤ 2/M₃ then (1/(m:ℝ)^2) * ‖Bsum f M₂ (ξ/(m:ℝ))‖^2 else 0)
      ≤ ENNReal.ofReal ((1/(m:ℝ)^2) *
          ((|(m:ℝ)|/M₃) * ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2)) := by
  have hne : (m:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  set I : Set ℝ := Set.Icc ((m:ℝ)*(ℓ:ℝ) - 2*|(m:ℝ)|/M₃) ((m:ℝ)*(ℓ:ℝ) + 2*|(m:ℝ)|/M₃) with hI
  set gp : ℝ → ℝ := fun ξ => (1/(m:ℝ)^2) * ‖Bsum f M₂ (ξ/(m:ℝ))‖^2 with hgp
  set Φ : ℝ := ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2 with hΦ
  have hfhat : Continuous (Fhat f) := by
    rw [show Fhat f = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
        (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) from rfl]
    exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
      (f := fun u : ℝ => (f u : ℂ)) Real.continuous_fourierChar (by fun_prop)
      ((hf.integrable_of_hasCompactSupport hcs).ofReal)
  have hBsumc : Continuous (fun u : ℝ => Bsum f M₂ u) := by
    simp only [Bsum]
    refine continuous_finsetSum _ (fun m₂ _ => ?_)
    exact Continuous.mul continuous_const (hfhat.comp (continuous_const.mul continuous_id))
  have hcont : Continuous gp := by
    rw [hgp]
    exact Continuous.const_mul ((hBsumc.comp (continuous_id.div_const _)).norm.pow 2) _
  have hmeasI : MeasurableSet I := measurableSet_Icc
  have hgpnn : ∀ ξ, 0 ≤ gp ξ := by intro ξ; rw [hgp]; positivity
  have hA : ∀ ξ, (if |(ℓ:ℝ) - ξ/(m:ℝ)| ≤ 2/M₃ then gp ξ else 0) = I.indicator gp ξ := by
    intro ξ
    rw [Set.indicator_apply]
    by_cases h : ξ ∈ I
    · rw [if_pos ((mem_resWin hM₃ hm ℓ ξ).mp h), if_pos h]
    · rw [if_neg (fun hc => h ((mem_resWin hM₃ hm ℓ ξ).mpr hc)), if_neg h]
  have hB : ∀ ξ, ENNReal.ofReal (I.indicator gp ξ)
      = I.indicator (fun ξ => ENNReal.ofReal (gp ξ)) ξ := by
    intro ξ
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : ξ ∈ I <;> simp [h]
  have hint : Integrable gp (volume.restrict I) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont.continuousOn
  have hEq : ∫⁻ ξ in I, ENNReal.ofReal (gp ξ) = ENNReal.ofReal (∫ ξ in I, gp ξ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hgpnn)).symm
  have hwin : ∫ ξ in I, ‖Bsum f M₂ (ξ/(m:ℝ))‖^2 = (|(m:ℝ)|/M₃) * Φ := by
    rw [hI, hΦ]; exact window_integral_Bsum hM₃ f ℓ hm
  calc ∫⁻ ξ in R, ENNReal.ofReal (if |(ℓ:ℝ) - ξ/(m:ℝ)| ≤ 2/M₃ then
          (1/(m:ℝ)^2) * ‖Bsum f M₂ (ξ/(m:ℝ))‖^2 else 0)
      = ∫⁻ ξ in R, I.indicator (fun ξ => ENNReal.ofReal (gp ξ)) ξ := by
          apply lintegral_congr; intro ξ; rw [hA ξ, hB ξ]
    _ = ∫⁻ ξ in R ∩ I, ENNReal.ofReal (gp ξ) := lintegral_indicator_restrict hmeasI _
    _ ≤ ∫⁻ ξ in I, ENNReal.ofReal (gp ξ) := lintegral_mono_set Set.inter_subset_right
    _ = ENNReal.ofReal (∫ ξ in I, gp ξ) := hEq
    _ = ENNReal.ofReal ((1/(m:ℝ)^2) * ((|(m:ℝ)|/M₃) * Φ)) := by
          rw [hgp, MeasureTheory.integral_const_mul, hwin]

theorem resMajorant_integral_le {M₁ M₂ M₃ T : ℝ} (hM₃ : 1 ≤ M₃) (hM₁ : 0 < M₁)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hwin : ∀ s : Finset ℤ,
      ∑ ℓ ∈ s, ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2 ≤ WinMass f M₂ M₃) :
    ∫ ξ in resRegion T M₁ M₃, resMajorant M₁ M₂ M₃ T f ξ ≤ (8 / M₃) * WinMass f M₂ M₃ := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  set L : Finset ℤ := Finset.Icc (-(⌈T ^ 6⌉ + 2)) (⌈T ^ 6⌉ + 2) with hL
  set S : Finset (ℤ × ℤ) := resPairs M₁ T with hS
  have hSprod : S = (R1 M₁).product L := by rw [hS, resPairs, hL]
  set Φ : ℤ × ℤ → ℝ := fun p => ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ p.2 τ‖^2 with hΦ
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => integral_nonneg (fun τ => sq_nonneg _)
  have hWnn : 0 ≤ WinMass f M₂ M₃ :=
    tsum_nonneg (fun ℓ => integral_nonneg (fun τ => sq_nonneg _))
  have hR1ne : ∀ m ∈ R1 M₁, m ≠ 0 := by
    intro m hm h
    have h2 := (Finset.mem_filter.mp hm).2
    rw [h] at h2
    simp at h2
    linarith
  have hm1 : ∀ p ∈ S, p.1 ≠ 0 := by
    intro p hp
    have hp' : p ∈ (R1 M₁).product L := hSprod ▸ hp
    exact hR1ne p.1 (Finset.mem_product.mp hp').1
  have hfhat : Continuous (Fhat f) := by
    rw [show Fhat f = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
        (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) from rfl]
    exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
      (f := fun u : ℝ => (f u : ℂ)) Real.continuous_fourierChar (by fun_prop)
      ((hf.integrable_of_hasCompactSupport hcs).ofReal)
  have hbsc : Continuous (fun u : ℝ => Bsum f M₂ u) := by
    simp only [Bsum]
    refine continuous_finsetSum _ (fun m₂ _ => ?_)
    exact Continuous.mul continuous_const (hfhat.comp (continuous_const.mul continuous_id))
  -- nonnegativity and measurability of the majorant
  have hFnn : ∀ ξ, 0 ≤ resMajorant M₁ M₂ M₃ T f ξ := by
    intro ξ
    rw [resMajorant_eq]
    apply Finset.sum_nonneg
    intro p hp
    by_cases hc : |(p.2:ℝ) - ξ/(p.1:ℝ)| ≤ 2/M₃
    · rw [if_pos hc]; positivity
    · rw [if_neg hc]
  have hFmeas : Measurable (resMajorant M₁ M₂ M₃ T f) := by
    unfold resMajorant
    refine Finset.measurable_sum _ (fun p hp => ?_)
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (isClosed_Iic.preimage
        (continuous_const.sub (continuous_id.div_const _)).abs).measurableSet
    · exact (Continuous.const_mul ((hbsc.comp (continuous_id.div_const _)).norm.pow 2) _).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hFnn)
    hFmeas.aestronglyMeasurable]
  suffices hgoal : ∫⁻ ξ in resRegion T M₁ M₃, ENNReal.ofReal (resMajorant M₁ M₂ M₃ T f ξ)
      ≤ ENNReal.ofReal ((8 / M₃) * WinMass f M₂ M₃) by
    calc (∫⁻ ξ in resRegion T M₁ M₃, ENNReal.ofReal (resMajorant M₁ M₂ M₃ T f ξ)).toReal
        ≤ (ENNReal.ofReal ((8 / M₃) * WinMass f M₂ M₃)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hgoal
      _ = (8 / M₃) * WinMass f M₂ M₃ :=
          ENNReal.toReal_ofReal (mul_nonneg (by positivity) hWnn)
  have hmeas : ∀ p ∈ S, Measurable (fun ξ : ℝ => ENNReal.ofReal
      (if |(p.2:ℝ) - ξ/(p.1:ℝ)| ≤ 2/M₃ then
        (1/(p.1:ℝ)^2) * ‖Bsum f M₂ (ξ/(p.1:ℝ))‖^2 else 0)) := by
    intro p hp
    refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ ?_ measurable_const)
    · exact (isClosed_Iic.preimage
        (continuous_const.sub (continuous_id.div_const _)).abs).measurableSet
    · exact (Continuous.const_mul ((hbsc.comp (continuous_id.div_const _)).norm.pow 2) _).measurable
  have hstep1 : ∫⁻ ξ in resRegion T M₁ M₃, ENNReal.ofReal (resMajorant M₁ M₂ M₃ T f ξ)
      = ∫⁻ ξ in resRegion T M₁ M₃, ∑ p ∈ S, ENNReal.ofReal
          (if |(p.2:ℝ) - ξ/(p.1:ℝ)| ≤ 2/M₃ then
            (1/(p.1:ℝ)^2) * ‖Bsum f M₂ (ξ/(p.1:ℝ))‖^2 else 0) := by
    apply lintegral_congr
    intro ξ
    rw [resMajorant_eq]
    exact ENNReal.ofReal_sum_of_nonneg (fun p hp => by
      by_cases hc : |(p.2:ℝ) - ξ/(p.1:ℝ)| ≤ 2/M₃
      · rw [if_pos hc]; positivity
      · rw [if_neg hc])
  have hM₃ne : M₃ ≠ 0 := ne_of_gt hM₃pos
  have hcoef : ∀ p ∈ S,
      (1/(p.1:ℝ)^2) * ((|(p.1:ℝ)| / M₃) * Φ p) = (1/(|(p.1:ℝ)| * M₃)) * Φ p := by
    intro p hp
    have h1 : (1/(p.1:ℝ)^2) * (|(p.1:ℝ)| / M₃) = 1/(|(p.1:ℝ)| * M₃) := by
      have ha : |(p.1:ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr (hm1 p hp))
      have hx : (p.1:ℝ)^2 = |(p.1:ℝ)|^2 := (sq_abs (p.1:ℝ)).symm
      rw [hx]
      field_simp
    rw [← h1]; ring
  have harith : ∑ p ∈ S, (1/(|(p.1:ℝ)| * M₃)) * Φ p ≤ (8/M₃) * WinMass f M₂ M₃ := by
    have h1 : ∑ p ∈ S, (1/(|(p.1:ℝ)| * M₃)) * Φ p
        = ∑ m ∈ R1 M₁, ∑ ℓ ∈ L, (1/(|(m:ℝ)| * M₃)) * Φ (m, ℓ) := by
      rw [hSprod]
      exact Finset.sum_product (R1 M₁) L _
    rw [h1]
    have h2 : ∀ m ∈ R1 M₁, (1/(|(m:ℝ)| * M₃)) * (∑ ℓ ∈ L, Φ (m, ℓ))
        ≤ (1/(|(m:ℝ)| * M₃)) * WinMass f M₂ M₃ := by
      intro m hm
      exact mul_le_mul_of_nonneg_left (hwin L) (le_of_lt (one_div_pos.mpr
        (mul_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (hR1ne m hm))) hM₃pos)))
    have h3 : ∑ m ∈ R1 M₁, 1/(|(m:ℝ)| * M₃) ≤ 8/M₃ := by
      have heq : ∑ m ∈ R1 M₁, 1/(|(m:ℝ)| * M₃) = (1/M₃) * ∑ m ∈ R1 M₁, 1/|(m:ℝ)| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have ha : |(m:ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr (hR1ne m hm))
        field_simp
      rw [heq]
      calc (1/M₃) * ∑ m ∈ R1 M₁, 1/|(m:ℝ)| ≤ (1/M₃) * 8 :=
            mul_le_mul_of_nonneg_left (sum_inv_abs_R1_le M₁ hM₁) (by positivity)
        _ = 8/M₃ := by ring
    calc ∑ m ∈ R1 M₁, ∑ ℓ ∈ L, (1/(|(m:ℝ)| * M₃)) * Φ (m, ℓ)
        = ∑ m ∈ R1 M₁, (1/(|(m:ℝ)| * M₃)) * (∑ ℓ ∈ L, Φ (m, ℓ)) := by
          apply Finset.sum_congr rfl; intro m hm; rw [Finset.mul_sum]
      _ ≤ ∑ m ∈ R1 M₁, (1/(|(m:ℝ)| * M₃)) * WinMass f M₂ M₃ := Finset.sum_le_sum h2
      _ = (∑ m ∈ R1 M₁, 1/(|(m:ℝ)| * M₃)) * WinMass f M₂ M₃ := by rw [Finset.sum_mul]
      _ ≤ (8/M₃) * WinMass f M₂ M₃ := mul_le_mul_of_nonneg_right h3 hWnn
  rw [hstep1, lintegral_finsetSum S hmeas]
  calc ∑ p ∈ S, ∫⁻ ξ in resRegion T M₁ M₃, ENNReal.ofReal
        (if |(p.2:ℝ) - ξ/(p.1:ℝ)| ≤ 2/M₃ then
          (1/(p.1:ℝ)^2) * ‖Bsum f M₂ (ξ/(p.1:ℝ))‖^2 else 0)
      ≤ ∑ p ∈ S, ENNReal.ofReal ((1/(p.1:ℝ)^2) * ((|(p.1:ℝ)| / M₃) * Φ p)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact key_pair_bound hM₃pos hf hcs (resRegion T M₁ M₃) (hm1 p hp) p.2
    _ = ∑ p ∈ S, ENNReal.ofReal ((1/(|(p.1:ℝ)| * M₃)) * Φ p) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hcoef p hp]
    _ = ENNReal.ofReal (∑ p ∈ S, (1/(|(p.1:ℝ)| * M₃)) * Φ p) :=
        (ENNReal.ofReal_sum_of_nonneg (fun p hp => mul_nonneg (le_of_lt (one_div_pos.mpr
          (mul_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (hm1 p hp))) hM₃pos)))
          (hΦnn p))).symm
    _ ≤ ENNReal.ofReal ((8/M₃) * WinMass f M₂ M₃) := ENNReal.ofReal_le_ofReal harith

end

end Work.GM.Affine
