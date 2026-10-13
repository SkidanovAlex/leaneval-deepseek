/-
# `cmode_memLp` — the mode coefficients of an `L²` source are `L²` in the radial variable

For a source `F` which is `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)` and whose square is
integrable there, every modal coefficient

  `cmode m F z = (∫_{Iθ} F z θ · eFam m θ · cos θ) / (∫_{Iθ} eFam m θ ^ 2 · cos θ)`

is square integrable in `z > 0`.

The proof is the classical Bessel/Cauchy–Schwarz step, integrated over `z`:

* Bessel's inequality (`cmode_bessel`, proved in the sibling module) gives, for every `z`,

    `eNorm m · (cmode m F z) ^ 2 ≤ ∫⁻ θ in Iθ, ofReal (F z θ ^ 2 · cos θ)`;

* integrating in `z` and applying Tonelli (`setLIntegral_prod`) turns the right-hand side into
  the double integral `∫⁻ p in Ioi 0 ×ˢ Iθ, ofReal (F p.1 p.2 ^ 2 · cos p.2)`, which is
  dominated by `∫⁻ p in Q0, ofReal (F p.1 p.2 ^ 2) < ∞` (the boundary `Iθ \ Ioo 0 (π/2)` is
  null, and `0 ≤ cos ≤ 1` on `Iθ`);
* dividing by the positive constant `eNorm m` gives the finiteness of
  `∫⁻ z in Ioi 0, ofReal ((cmode m F z) ^ 2)`.

Measurability of `z ↦ cmode m F z` is the Fubini measurability of the slice integral: the
integrand `(z,θ) ↦ √(cos θ) · eFam m θ · (√(cos θ) · F z θ)` is continuous on `Q0`, hence a.e.
strongly measurable for the product measure.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal BigOperators symmDiff
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

/-! ## The product set `Ioi 0 ×ˢ Iθ` is `Q0` up to a null set -/

/-- The boundary `Ioi 0 ×ˢ {0, π/2}` of the closed quadrant `Ioi 0 ×ˢ Iθ` is null. -/
theorem volume_Ioi_prod_pair : (volume : Measure (ℝ × ℝ))
    (Set.Ioi 0 ×ˢ ({0, π / 2} : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Work.Spaces.null_pair, mul_zero]

/-- Restricted to `Ioi 0 ×ˢ Iθ`, the Lebesgue measure agrees with its restriction to the open
quadrant `Q0` (the two sets differ by the null set `Ioi 0 ×ˢ {0, π/2}`). -/
theorem restrict_Ioi_prod_Iθ_eq_Q0 :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
  have hnull := volume_Ioi_prod_pair
  have hsub : (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) \ Work.FTS.EllipticEst.Q0
      ⊆ Set.Ioi 0 ×ˢ ({0, π / 2} : Set ℝ) := by
    intro p hp
    rw [Set.mem_sdiff] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp1
    refine Set.mem_prod.mpr ⟨hz, ?_⟩
    have hθ' : (0 : ℝ) ≤ p.2 ∧ p.2 ≤ π / 2 := hθ
    by_cases h : p.2 = 0
    · rw [h]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · have hpos : 0 < p.2 := lt_of_le_of_ne hθ'.1 (Ne.symm h)
      have hlt : p.2 = π / 2 := by
        by_contra hne
        exact hp2 (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hpos, lt_of_le_of_ne hθ'.2 hne⟩)
      rw [hlt]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  refine Measure.restrict_congr_set ?_
  rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
  refine measure_mono_null ?_ hnull
  rintro p (hp | hp)
  · exact hsub hp
  · exfalso
    rw [Set.mem_sdiff] at hp
    exact hp.2 (Set.mem_prod.mpr ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp.1).1,
      ⟨le_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp.1).2.1,
       le_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp.1).2.2⟩⟩)

/-! ## Measurability of the mode coefficients -/

/-- The numerator `bInt m F` of the mode coefficient is a.e. strongly measurable in `z`:
it is the `z`-slice integral of a function which is continuous on the open quadrant. -/
theorem aesm_bInt {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) (m : ℕ) :
    AEStronglyMeasurable (fun z => bInt m F z) (volume.restrict (Set.Ioi 0)) := by
  set φ : ℝ × ℝ → ℝ := fun p =>
    (Real.sqrt (Real.cos p.2) * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      * (Real.sqrt (Real.cos p.2) * F p.1 p.2) with hφ
  have hcont : ContinuousOn φ Work.FTS.EllipticEst.Q0 := by
    have h1 : Continuous (fun p : ℝ × ℝ => Real.sqrt (Real.cos p.2)) :=
      Real.continuous_sqrt.comp (Real.continuous_cos.comp continuous_snd)
    have h2 : Continuous (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2) :=
      (continuous_eFam m).comp continuous_snd
    exact (h1.continuousOn.mul h2.continuousOn).mul (h1.continuousOn.mul hsm.continuousOn)
  have haesmφ : AEStronglyMeasurable φ (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hν : (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
    Measure.restrict_congr_set Work.Spaces.Iθ_ae_eq_Ioo
  have hprod : (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ))
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
    rw [hν, Measure.prod_restrict, Measure.volume_eq_prod]
    rfl
  have haesmφ' : AEStronglyMeasurable φ (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [hprod]; exact haesmφ
  have h := haesmφ'.integral_prod_right'
  have hfun : (fun z => ∫ (y : ℝ), φ (z, y)
        ∂((volume : Measure ℝ).restrict Work.Spaces.Iθ)) = fun z => bInt m F z := by
    funext z
    simp only [hφ, bInt]
  rwa [hfun] at h

/-- The mode coefficients `cmode m F` are a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_cmode {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) (m : ℕ) :
    AEStronglyMeasurable (fun z => Work.FTS.PhiStar.Series.cmode m F z)
      (volume.restrict (Set.Ioi 0)) := by
  have hb := aesm_bInt hsm m
  have hdiv : AEStronglyMeasurable (fun z => bInt m F z / eNorm m)
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [div_eq_mul_inv] using hb.mul_const (eNorm m)⁻¹
  exact hdiv.congr (Eventually.of_forall fun z => (cmode_eq m F z).symm)

/-! ## Integrability of the squared mode coefficients -/

/-- **Bessel's inequality, integrated in `z`.**  For every `z` the Bessel bound of
`cmode_bessel` holds; Tonelli then identifies the `z`-integral of its right-hand side with the
double integral over `Ioi 0 ×ˢ Iθ`, which is finite. -/
theorem lintegral_ofReal_eNorm_mul_cmode_sq_lt_top {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Work.FTS.EllipticEst.Q0)
    (m : ℕ) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
      (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)) < ∞ := by
  let G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2)
  have hbd : ∀ z, ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) ≤
      ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := by
    intro z
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (cmode_bessel F z m)
    have hterm : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        * Work.FTS.PhiStar.Series.cmode m F z ^ 2
        = eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := rfl
    rw [← hterm]
    refine Finset.single_le_sum (f := fun k => (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam k θ ^ 2 * Real.cos θ)
        * Work.FTS.PhiStar.Series.cmode k F z ^ 2) (fun k _ => ?_)
      (Finset.mem_range.mpr (Nat.lt_succ_self m))
    have hk : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam k θ ^ 2 * Real.cos θ) = eNorm k := rfl
    rw [hk]
    exact mul_nonneg (le_of_lt (eNorm_pos k)) (sq_nonneg _)
  have hGcont : ContinuousOn G Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
        Work.FTS.EllipticEst.Q0 :=
      (hsm.continuousOn.pow 2).mul (Real.continuous_cos.comp continuous_snd).continuousOn
    exact ENNReal.continuous_ofReal.comp_continuousOn h1
  have hGmeas : AEMeasurable G
      ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [restrict_Ioi_prod_Iθ_eq_Q0]
    exact hGcont.aemeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have h1 : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := lintegral_mono hbd
  have h2 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ))
      = ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, G p :=
    (setLIntegral_prod G hGmeas).symm
  have h3 : (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, G p)
      ≤ ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
      (s := Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      (MeasurableSet.prod measurableSet_Ioi measurableSet_Iθ)] with p hp
    exact ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (sq_nonneg _) (Real.cos_le_one p.2))
  have h4 : (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (F p.1 p.2 ^ 2))
      = ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
    rw [restrict_Ioi_prod_Iθ_eq_Q0]
  have h5 : (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2)) < ∞ := by
    have hf := hasFiniteIntegral_iff_enorm.mp hL2.2
    rwa [lintegral_congr (fun p => ?_)] at hf
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := h1
    _ = ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, G p := h2
    _ ≤ ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (F p.1 p.2 ^ 2) := h3
    _ = ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := h4
    _ < ∞ := h5

/-- The squared mode coefficients are a.e. finite in the `lintegral` sense. -/
theorem lintegral_ofReal_cmode_sq_lt_top {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Work.FTS.EllipticEst.Q0)
    (m : ℕ) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2)) < ∞ := by
  have hNpos : (0 : ℝ) < eNorm m := eNorm_pos m
  have hNne : ENNReal.ofReal (eNorm m) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)
  have hle : (fun z => ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ fun z => (ENNReal.ofReal (eNorm m))⁻¹ *
          ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
    intro z
    have hz : (ENNReal.ofReal (eNorm m))⁻¹ *
        ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
        = ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
      rw [ENNReal.ofReal_mul (le_of_lt hNpos), ← mul_assoc,
        ENNReal.inv_mul_cancel hNne ENNReal.ofReal_ne_top, one_mul]
    exact le_of_eq hz.symm
  calc (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, (ENNReal.ofReal (eNorm m))⁻¹ *
          ENNReal.ofReal (eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) :=
        lintegral_mono hle
    _ = (ENNReal.ofReal (eNorm m))⁻¹ *
          ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (eNorm m *
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hNne)
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hNpos))
        (lintegral_ofReal_eNorm_mul_cmode_sq_lt_top hsm hL2 m)

/-- **The mode coefficients of an `L²` source are square integrable in the radial variable.** -/
theorem cmode_memLp {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Work.FTS.EllipticEst.Q0)
    (m : ℕ) : MeasureTheory.IntegrableOn (fun z => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) (Set.Ioi 0) := by
  refine ⟨?_, ?_⟩
  · exact aesm_cmode hsm m |>.pow 2
  · rw [hasFiniteIntegral_iff_enorm]
    have henorm : (fun z => ‖(Work.FTS.PhiStar.Series.cmode m F z) ^ 2‖ₑ)
        = fun z => ENNReal.ofReal ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
      funext z
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
    rw [henorm]
    exact lintegral_ofReal_cmode_sq_lt_top hsm hL2 m

end Work.EllipticEst.ModalSolution
