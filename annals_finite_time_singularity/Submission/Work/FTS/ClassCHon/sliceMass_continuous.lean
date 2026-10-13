import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.PhiStar.Honesty.IPMemOfHkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyWAux
import Submission.Work.FTS.ClassCHon.SliceMassAux.pointwise_amgm
import Submission.Work.FTS.ClassCHon.SliceMassAux.slice_sq_ftc
import Submission.Work.FTS.ClassCHon.SliceMassAux.continuousOn_of_integral_bound
import Submission.Work.FTS.ClassCHon.SliceMassAux.integrable_prod_mixed
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.HkMem_of_outer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter
open scoped ENNReal

namespace Work.FTS.ClassCHon

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Assembly step: the same proof as `sliceMass_continuous`, with the four auxiliary facts
(delegated and proved in `SliceMassAux`) as explicit hypotheses. -/
theorem sliceMass_aux {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (h0 : Work.Spaces.HkMem α 0 F)
    (h1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ))
    (hPAMG : ∀ s θ a b : ℝ, 0 < s → θ ∈ Work.Spaces.Iθ →
      2 * |a * b| * Work.FTS.EllipticEst.sEta θ
        ≤ a ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + (s * b) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ)
    (hFTC : ∀ z₁ z₂ θ : ℝ, 0 < z₁ → z₁ ≤ z₂ → θ ∈ Set.Ioo 0 (π / 2) →
      (F z₂ θ) ^ 2 - (F z₁ θ) ^ 2
        = ∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
    (hINT : MeasureTheory.Integrable
      (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hCONT : ∀ {m Φ : ℝ → ℝ}, MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)) →
      (∀ z, 0 ≤ Φ z) →
      (∀ z₁ z₂ : ℝ, 0 < z₁ → z₁ ≤ z₂ → |m z₂ - m z₁| ≤ ∫ s in z₁..z₂, Φ s) →
      ContinuousOn m (Set.Ioi (0 : ℝ))) :
    ContinuousOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioi 0) := by
  -- `sEta` is nonnegative on `Iθ`
  have hsEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ := fun θ hθ => by
    simpa only [Work.FTS.EllipticEst.sEta, Work.FTS.EllipticEst.AngSecond.sig]
      using Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  -- the per-slice integrability of the `σ`-weighted slice masses
  have hsliceF : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := fun z hz =>
    Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem h0 (show (0 : ℝ) < z from hz)
  have hsliceZ : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := fun z hz =>
    Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem h1 (show (0 : ℝ) < z from hz)
  -- the outer integrability of the two slice masses
  have hGzInt : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (f := F) h0).1
  have hGzpInt : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta
      (f := fun z θ => z * Work.Spaces.pz F z θ) h1).1
  -- the dominating density
  set G : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      + (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hGdef
  have hGint : MeasureTheory.IntegrableOn G (Set.Ioi (0 : ℝ)) := by
    rw [hGdef]
    exact (hGzInt.add hGzpInt).mono_set
      (fun z hz => (show z ∈ Work.Spaces.Iz from le_of_lt (show (0 : ℝ) < z from hz)))
  have hGnn : ∀ z, 0 ≤ G z := by
    intro z
    rw [hGdef]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
    · exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  -- the difference bound
  have hdiff : ∀ z₁ z₂ : ℝ, 0 < z₁ → z₁ ≤ z₂ →
      |(∫ θ in Work.Spaces.Iθ, (F z₂ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        - (∫ θ in Work.Spaces.Iθ, (F z₁ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)|
      ≤ ∫ s in z₁..z₂, G s := by
    intro z₁ z₂ hz₁ hz₁₂
    have hsubIoc : Set.Ioc z₁ z₂ ⊆ Work.Spaces.Iz :=
      fun z hz => le_of_lt (lt_trans hz₁ hz.1)
    -- product-integrability of the joint integrand on the box
    have hbox : MeasureTheory.Integrable
        (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ))
        ((MeasureTheory.volume.restrict (Set.uIoc z₁ z₂)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hfull : MeasureTheory.IntegrableOn
          (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
            * Work.FTS.EllipticEst.sEta θ))
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) MeasureTheory.volume := by
        rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.volume_eq_prod,
          ← MeasureTheory.Measure.prod_restrict]
        exact hINT
      have hsub : Set.uIoc z₁ z₂ ⊆ Work.Spaces.Iz := by
        rw [Set.uIoc_of_le hz₁₂]; exact hsubIoc
      have hsmall := hfull.mono_set (Set.prod_mono hsub subset_rfl)
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      simpa only [MeasureTheory.IntegrableOn] using hsmall
    -- (a) the difference of the two masses
    have hstep1 : (∫ θ in Work.Spaces.Iθ, (F z₂ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        - (∫ θ in Work.Spaces.Iθ, (F z₁ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            ((F z₂ θ) ^ 2 - (F z₁ θ) ^ 2) * Work.FTS.EllipticEst.sEta θ := by
      rw [← MeasureTheory.integral_sub (hsliceF z₂ (by exact lt_of_lt_of_le hz₁ hz₁₂))
        (hsliceF z₁ hz₁)]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    -- (b) the fundamental theorem of calculus on each slice
    have hstep2 : (∫ θ in Work.Spaces.Iθ,
            ((F z₂ θ) ^ 2 - (F z₁ θ) ^ 2) * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            (∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
              * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
      rw [hFTC z₁ z₂ θ hz₁ hz₁₂ hθ]
    -- (c) bring `σ` inside the interval integral
    have hstep3 : (∫ θ in Work.Spaces.Iθ,
            (∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
              * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, ∫ s in z₁..z₂,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      show (∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
          * Work.FTS.EllipticEst.sEta θ
        = ∫ s in z₁..z₂,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ
      rw [intervalIntegral.integral_mul_const]
    -- (d) Fubini
    have hstep4 : (∫ θ in Work.Spaces.Iθ, ∫ s in z₁..z₂,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ)
        = ∫ s in z₁..z₂, ∫ θ in Work.Spaces.Iθ,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ :=
      (MeasureTheory.intervalIntegral_integral_swap
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (a := z₁) (b := z₂)
        (f := fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ) hbox).symm
    -- (e) the a.e. pointwise bound on the `z`-slices
    have hΦbound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc z₁ z₂)),
        |∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
            * Work.FTS.EllipticEst.sEta θ| ≤ G s := by
      have hslice_ae : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.Integrable (fun θ => 2 * F s θ * Work.Spaces.pz F s θ
            * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.Integrable.prod_right_ae hINT
      have hmono : MeasureTheory.volume.restrict (Set.Ioc z₁ z₂)
          ≤ MeasureTheory.volume.restrict Work.Spaces.Iz :=
        MeasureTheory.Measure.restrict_mono hsubIoc le_rfl
      filter_upwards [hslice_ae.filter_mono (MeasureTheory.ae_mono hmono),
        MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs_int hs_mem
      have hspos : 0 < s := lt_of_lt_of_le hz₁ (le_of_lt hs_mem.1)
      have hA : MeasureTheory.IntegrableOn
          (fun θ => (F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
        MeasureTheory.IntegrableOn.congr_fun
          ((hsliceF s ((show (0 : ℝ) < s from hspos) : s ∈ Set.Ioi (0 : ℝ))).const_mul
            ((Work.Spaces.w s) ^ 2))
          (fun θ _ => by ring) measurableSet_Icc
      have hB : MeasureTheory.IntegrableOn
          (fun θ => (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
        MeasureTheory.IntegrableOn.congr_fun
          ((hsliceZ s ((show (0 : ℝ) < s from hspos) : s ∈ Set.Ioi (0 : ℝ))).const_mul
            ((Work.Spaces.w s) ^ 2))
          (fun θ _ => by ring) measurableSet_Icc
      have hAB : MeasureTheory.IntegrableOn
          (fun θ => (F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
            + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hA.add hB
      have h2 : (∫ θ in Work.Spaces.Iθ,
            |2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ|)
          ≤ ∫ θ in Work.Spaces.Iθ,
            ((F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                * Work.FTS.EllipticEst.sEta θ) := by
        refine MeasureTheory.integral_mono_ae (MeasureTheory.Integrable.abs hs_int) hAB ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        have hp := hPAMG s θ (F s θ) (Work.Spaces.pz F s θ) hspos hθ
        have hleft : |2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ|
            = 2 * |F s θ * Work.Spaces.pz F s θ| * Work.FTS.EllipticEst.sEta θ := by
          rw [show (2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ)
              = 2 * (F s θ * Work.Spaces.pz F s θ) * Work.FTS.EllipticEst.sEta θ
            from by ring,
            abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_nonneg (hsEta_nn θ hθ)]
        rw [hleft]; exact hp
      have h3 : (∫ θ in Work.Spaces.Iθ,
            ((F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) = G s := by
        rw [hGdef]
        show (∫ θ in Work.Spaces.Iθ,
            ((F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                * Work.FTS.EllipticEst.sEta θ))
          = (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (Work.Spaces.w s) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (s * Work.Spaces.pz F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        rw [MeasureTheory.integral_add hA hB, ← MeasureTheory.integral_const_mul,
          ← MeasureTheory.integral_const_mul]
        congr 1
        · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
        · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
      calc |∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
              * Work.FTS.EllipticEst.sEta θ|
          ≤ ∫ θ in Work.Spaces.Iθ,
              |2 * F s θ * Work.Spaces.pz F s θ
                * Work.FTS.EllipticEst.sEta θ| :=
            MeasureTheory.abs_integral_le_integral_abs
        _ ≤ _ := h2
        _ = G s := h3
    -- (f) assemble
    rw [hstep1, hstep2, hstep3, hstep4]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm
      (f := fun s => ∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ) hz₁₂) ?_
    simp only [Real.norm_eq_abs]
    rw [intervalIntegral.integral_of_le hz₁₂, intervalIntegral.integral_of_le hz₁₂]
    have hbase : MeasureTheory.Integrable
        (fun s => ∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict (Set.Ioc z₁ z₂)) := by
      have h := MeasureTheory.Integrable.integral_prod_left hbox
      rw [Set.uIoc_of_le hz₁₂] at h
      exact MeasureTheory.Integrable.congr h (Filter.Eventually.of_forall fun s => rfl)
    refine MeasureTheory.integral_mono_ae hbase.abs
      (hGint.mono_set (fun z hz => (show z ∈ Set.Ioi (0 : ℝ) from lt_trans hz₁ hz.1)))
      hΦbound
  exact hCONT hGint hGnn hdiff

/-- **Continuity of the angular slice mass of an `ℋ⁰`-honest function with honest radial derivative.**

For `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, whose level-`0` `ℋ`-integrand is
honest (`HkMem α 0 F`) and whose radial derivative `z ∂_z F` is also `ℋ⁰`-honest
(`HkMem α 0 (fun z θ => z * pz F z θ)`), the angular slice mass

  `m F z := ∫_θ (F z θ)² · sin(2θ)^{-η}`

is continuous on `(0,∞)` (hence locally bounded there).

**Proof.** For each fixed `θ ∈ (0,π/2)` the slice `z ↦ F z θ` is `C^∞` on `(0,∞)`, so the FTC in
`z` gives `F(z₂,θ)² - F(z₁,θ)² = ∫_{z₁}^{z₂} 2 F(s,θ) ∂_zF(s,θ) ds` for `0 < z₁ ≤ z₂`. Multiplying
by `σ θ = sin(2θ)^{-η}` and integrating in `θ` (Fubini; the double integral of `|F ∂_zF| σ` is
finite by two Cauchy–Schwarz inequalities, using on `[z₁,z₂]` that `w² ≥ c > 0` and
`z² ≥ z₁²` together with the two outer conjuncts of `HkMem`) gives

  `m F z₂ - m F z₁ = ∫_{z₁}^{z₂} Φ s ds`,   `Φ s := ∫_θ 2 F(s,θ) ∂_zF(s,θ) σ θ dθ`,

with `∫_{z₁}^{z₂}|Φ| < ∞`; so `m F` is absolutely continuous, hence continuous, on every compact
subinterval of `(0,∞)`. -/
theorem sliceMass_continuous {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (h0 : Work.Spaces.HkMem α 0 F)
    (h1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ)) :
    ContinuousOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioi 0) := by
  exact sliceMass_aux hsm h0 h1
    (fun s θ a b hs hθ => Work.FTS.ClassCHon.SliceMassAux.pointwise_amgm hs hθ)
    (fun z₁ z₂ θ hz hz' hθ =>
      Work.FTS.ClassCHon.SliceMassAux.slice_sq_ftc (F := F) hsm hz hz' hθ)
    (Work.FTS.ClassCHon.SliceMassAux.integrable_prod_mixed hsm h0 h1)
    (fun {m Φ} hΦ hnn h => Work.FTS.ClassCHon.SliceMassAux.continuousOn_of_integral_bound hΦ hnn h)

/-! ## The weakened interface: the honest radial derivative replaced by its two *outer* bounds

The proof of `sliceMass_continuous` uses the hypothesis `h1 : HkMem α 0 (z ∂_z F)` through exactly
two facts about the function `G := z ∂_z F`:

* the *slice* conjunct: `∫_θ (G z θ)² σ θ < ∞` for every `z ∈ Ioi 0`
  (`integrableOn_sq_sEta_of_HkMem`), and
* the *outer* conjunct: `∫_z w(z)² ∫_θ (G z θ)² σ θ < ∞`.

Both are *consequences* of the two outer `∫⁻`-bounds of `HkIntegrand α 0 G` and
`HkIntegrand α 1 G`, by the every-`z` upgrade `SliceMassUpgrade.HkMem_of_outer` (the level-`1`
bound, i.e. one `D_z`-order up, is exactly the slack the repaired node `EllNode8pp` provides).
The statement below takes the two outer bounds (plus the measurabilities they need) as
hypotheses, so that a consumer which only has the *integrated* estimate at hand can still
conclude the continuity of the slice mass.

The passage from `h1` to the four outer facts is
`SliceMassUpgrade.HkMem_of_outer` applied to `G = z ∂_z F`; note that the level-`(k+1)` integrand
of `G` is the one containing `D_z²F`, i.e. the statement consumes *two* orders of the source. -/
theorem sliceMass_continuous_of_outer {α : ℝ} {F : ℝ → ℝ → ℝ} {C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (h0 : Work.Spaces.HkMem α 0 F)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ : ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz F) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas : AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz F) z θ))
        ≤ ENNReal.ofReal C₀)
    (hslmeas1 : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ : ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 (Work.Spaces.Dz F) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas1 : AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 (Work.Spaces.Dz F) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 (Work.Spaces.Dz F) z θ))
        ≤ ENNReal.ofReal C₁) :
    ContinuousOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioi 0) := by
  have h1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ) :=
    Work.FTS.ClassCHon.SliceMassUpgrade.HkMem_of_outer (α := α) (k := 0)
      (F := Work.Spaces.Dz F) hC₀ hC₁ hsm.Dz hslmeas hmeas hfin0 hslmeas1 hmeas1 hfin1
  exact sliceMass_aux hsm h0 h1
    (fun s θ a b hs hθ => Work.FTS.ClassCHon.SliceMassAux.pointwise_amgm hs hθ)
    (fun z₁ z₂ θ hz hz' hθ =>
      Work.FTS.ClassCHon.SliceMassAux.slice_sq_ftc (F := F) hsm hz hz' hθ)
    (Work.FTS.ClassCHon.SliceMassAux.integrable_prod_mixed hsm h0 h1)
    (fun {m Φ} hΦ hnn h => Work.FTS.ClassCHon.SliceMassAux.continuousOn_of_integral_bound hΦ hnn h)

end Work.FTS.ClassCHon
