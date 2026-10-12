import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGAssembly
import Submission.Work.BoseBoxFock.pairGMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGFibre` — the per-fibre assembly of the D2 estimate

This module turns the *analytic core* of a row fibre (its pointwise mass and Dirichlet bounds, its
continuity and its differentiability, supplied by the sibling modules `pairGc13_core`,
`pairGc23_core`, `pairGc21_core`) plus the *slice identities* into the pair-energy bound

    pairEnergy ℓ (pairGc p hp Θ₀ A B) ≤ C·cA²cB²·pinL2 ℓ Θ₀·(pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) .

The assembly is `pairEnergy_le_of_box_bounds` (the windowed product rule) plus the two
double-integral bounds obtained by Cauchy–Schwarz and the slice identities.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The two-variable integrand of a fibre is strongly measurable when the fibre is continuous. -/
theorem aestronglyMeasurable_fibre {G : E3 → E3 → ℂ} (hcont : Continuous (Function.uncurry G)) :
    AEStronglyMeasurable (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2) volume :=
  (hcont.stronglyMeasurable.norm.pow 2).aestronglyMeasurable

/-- The box squared has finite measure. -/
theorem volume_boxL_prod_lt_top {ℓ : ℝ} :
    (volume : Measure (E3 × E3)) (boxL ℓ ×ˢ boxL ℓ) < ⊤ := by
  have h : IsCompact (boxL ℓ ×ˢ boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  exact lt_top_iff_ne_top.mpr h.measure_ne_top

/-- The one-particle box has finite measure. -/
theorem volume_boxL_lt_top_fibre {ℓ : ℝ} : volume (boxL ℓ) < ⊤ :=
  lt_top_iff_ne_top.mpr
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_ne_top

/-- **A bounded measurable function is integrable on the one-particle box.** -/
theorem integrableOn_boxL_of_aeBound {ℓ : ℝ} {φ : E3 → ℝ}
    (hφm : AEStronglyMeasurable φ (volume.restrict (boxL ℓ))) {C : ℝ}
    (hC : ∀ᵐ x ∂(volume.restrict (boxL ℓ)), ‖φ x‖ ≤ C) : IntegrableOn φ (boxL ℓ) :=
  IntegrableOn.of_bound volume_boxL_lt_top_fibre hφm C hC

/-- **The double-integral Cauchy–Schwarz bound.**  If `‖G w y‖² ≤ Φ w · Ψ y` on the box squared,
then the box-squared mass of `G` is at most the product of the box-integrals of `Φ` and `Ψ`. -/
theorem setIntegral_prod_le_factor {ℓ : ℝ} {f : E3 → E3 → ℝ} {Φ Ψ : E3 → ℝ}
    (hf0 : ∀ w y, 0 ≤ f w y)
    (hΦ0 : ∀ w, 0 ≤ Φ w) (hΨ0 : ∀ y, 0 ≤ Ψ y)
    (hΦm : StronglyMeasurable Φ) (hΨm : StronglyMeasurable Ψ)
    (hΦb : ∃ C, ∀ w ∈ boxL ℓ, Φ w ≤ C) (hΨb : ∃ C, ∀ y ∈ boxL ℓ, Ψ y ≤ C)
    (hpt : ∀ w y, f w y ≤ Φ w * Ψ y) :
    (∫ z in boxL ℓ ×ˢ boxL ℓ, f z.1 z.2)
      ≤ (∫ w in boxL ℓ, Φ w) * (∫ y in boxL ℓ, Ψ y) := by
  obtain ⟨CΦ, hCΦ⟩ := hΦb
  obtain ⟨CΨ, hCΨ⟩ := hΨb
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hΦint : IntegrableOn Φ (boxL ℓ) :=
    integrableOn_boxL_of_aeBound (hΦm.comp_measurable measurable_id).aestronglyMeasurable (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict hbox] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 w)]
      exact hCΦ w hw)
  have hΨint : IntegrableOn Ψ (boxL ℓ) :=
    integrableOn_boxL_of_aeBound (hΨm.comp_measurable measurable_id).aestronglyMeasurable (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict hbox] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 y)]
      exact hCΨ y hy)
  -- the majorant is integrable on the box squared
  have hmaj_int : IntegrableOn (fun z : E3 × E3 => Φ z.1 * Ψ z.2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine IntegrableOn.of_bound volume_boxL_prod_lt_top ?_ (max CΦ 0 * max CΨ 0) ?_
    · exact ((hΦm.comp_measurable measurable_fst).mul
        (hΨm.comp_measurable measurable_snd)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hΦ0 _) (hΨ0 _))]
      exact mul_le_mul (le_trans (hCΦ _ hz.1) (le_max_left CΦ 0))
        (le_trans (hCΨ _ hz.2) (le_max_left CΨ 0)) (hΨ0 _) (le_max_right CΦ 0)
  have hmono : (∫ z in boxL ℓ ×ˢ boxL ℓ, f z.1 z.2)
      ≤ ∫ z in boxL ℓ ×ˢ boxL ℓ, Φ z.1 * Ψ z.2 :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => hf0 z.1 z.2) hmaj_int
      (Eventually.of_forall fun z => hpt z.1 z.2)
  refine hmono.trans ?_
  rw [show (∫ z in boxL ℓ ×ˢ boxL ℓ, Φ z.1 * Ψ z.2)
      = ∫ z in boxL ℓ ×ˢ boxL ℓ, Φ z.1 * Ψ z.2 ∂(volume.prod volume) from rfl]
  rw [MeasureTheory.setIntegral_prod _ hmaj_int]
  rw [show (∫ w in boxL ℓ, ∫ y in boxL ℓ, Φ w * Ψ y)
      = ∫ w in boxL ℓ, Φ w * (∫ y in boxL ℓ, Ψ y) from
    integral_congr_ae (Eventually.of_forall fun w => by
      show (∫ y in boxL ℓ, Φ w * Ψ y) = Φ w * ∫ y in boxL ℓ, Ψ y
      rw [show (∫ y in boxL ℓ, Φ w * Ψ y) = ∫ y in boxL ℓ, Ψ y * Φ w from
        integral_congr_ae (Eventually.of_forall fun y => by ring)]
      rw [MeasureTheory.integral_mul_const, mul_comm])]
  rw [MeasureTheory.integral_mul_const]

/-- The window `χ_ℓ` is continuous (for every `ℓ`, including `ℓ = 0`, where it is constant). -/
theorem continuous_chiS (ℓ : ℝ) : Continuous (chiS ℓ) := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · have h : chiS 0 = fun _ : E3 => ((Submission.BoseGases.chi 0 : ℝ) : ℂ) := by
      funext x
      simp [chiS, Submission.BoseGases.chiScale]
    rw [h]
    exact continuous_const
  · exact Complex.ofRealCLM.continuous.comp
      (Submission.BoseGases.chiScale_contDiff hℓ).continuous

/-- The window `χ_ℓ` is differentiable (smooth for `ℓ ≠ 0`, constant for `ℓ = 0`). -/
theorem differentiable_chiS (ℓ : ℝ) : Differentiable ℝ (chiS ℓ) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (chiS ℓ) := by
    by_cases hℓ : ℓ = 0
    · subst hℓ
      have h : chiS 0 = fun _ : E3 => ((Submission.BoseGases.chi 0 : ℝ) : ℂ) := by
        funext x
        simp [chiS, Submission.BoseGases.chiScale]
      rw [h]
      exact contDiff_const
    · refine Complex.ofRealCLM.contDiff.comp ?_
      refine Submission.BoseGases.chi_contDiff.comp ?_
      exact contDiff_id.const_smul (ℓ⁻¹)
  exact hcd.differentiable (by simp)

/-- The χ-multiplied fibre is jointly continuous (used for the parametric measurability of the
derivative). -/
theorem continuous_chiS_mul_fibre {ℓ : ℝ} {G : E3 → E3 → ℂ}
    (hcont : Continuous (Function.uncurry G)) :
    Continuous (Function.uncurry (fun (q : E3 × E3) (w' : E3) => chiS ℓ w' * G w' q.2)) := by
  have h1 : Continuous (fun p : (E3 × E3) × E3 => chiS ℓ p.2) :=
    (continuous_chiS ℓ).comp continuous_snd
  refine h1.mul ?_
  have h2 : Continuous (fun p : (E3 × E3) × E3 => G p.2 p.1.2) :=
    hcont.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  simpa only using h2

/-- Measurability of the Dirichlet integrand `z ↦ Σ_j ‖∂_j G(·,z.2)(z.1)‖²` of a continuous
fibre. -/
theorem aesm_dirIntegrand {G : E3 → E3 → ℂ} (hcont : Continuous (Function.uncurry G)) :
    AEStronglyMeasurable (fun z : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) volume := by
  have hc : Continuous (Function.uncurry (fun (q : E3 × E3) (w' : E3) => G w' q.2)) :=
    hcont.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have hsum : Measurable (fun z : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    refine Finset.measurable_sum (Finset.univ : Finset (Fin 3)) fun j _ => ?_
    have h1 := measurable_fderiv_apply_const_with_param ℝ hc (EuclideanSpace.single j (1 : ℝ))
    have hpair : Measurable (fun z : E3 × E3 => (z, z.1)) :=
      Measurable.prod measurable_id measurable_fst
    exact (h1.comp hpair).norm.pow_const 2
  exact hsum.aestronglyMeasurable

/-- Measurability of the windowed Dirichlet integrand of the pair energy. -/
theorem aesm_LHSIntegrand {ℓ : ℝ} {G : E3 → E3 → ℂ}
    (hcont : Continuous (Function.uncurry G)) :
    AEStronglyMeasurable (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) volume := by
  have hc : Continuous (Function.uncurry (fun (q : E3 × E3) (w' : E3) => chiS ℓ w' * G w' q.2)) :=
    continuous_chiS_mul_fibre hcont
  have hsum : Measurable (fun z : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    refine Finset.measurable_sum (Finset.univ : Finset (Fin 3)) fun j _ => ?_
    have h1 := measurable_fderiv_apply_const_with_param ℝ hc (EuclideanSpace.single j (1 : ℝ))
    have hpair : Measurable (fun z : E3 × E3 => (z, z.1)) :=
      Measurable.prod measurable_id measurable_fst
    exact (h1.comp hpair).norm.pow_const 2
  have h2 : Measurable (fun z : E3 × E3 => (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) := by
    have h3 : Continuous (fun z : E3 × E3 => ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) := by
      have h4 : Continuous (fun z : E3 × E3 => chiS ℓ z.1 * G z.1 z.2) :=
        ((continuous_chiS ℓ).comp continuous_fst).mul
          (hcont.comp (continuous_fst.prodMk continuous_snd))
      exact h4.norm.pow 2
    exact (continuous_const.mul h3).measurable
  exact (hsum.add h2).aestronglyMeasurable

/-- **The pointwise product rule bound** of the pair-energy integrand. -/
theorem LHSIntegrand_le {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ} {Kg Kc : ℝ}
    (hKg : ∀ w : E3,
      ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc)
    (hder : ∀ w y : E3, DifferentiableAt ℝ (fun w' => G w' y) w) :
    ∀ w y : E3, (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ w * G w y‖ ^ 2)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G w y‖ ^ 2 + 2 * Kc * ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  intro w y
  have hchi : DifferentiableAt ℝ (chiS ℓ) w := (differentiable_chiS ℓ).differentiableAt
  have hper : ∀ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ 2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
          + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2 := by
    intro j
    have hd : HasFDerivAt (fun w' => chiS ℓ w' * G w' y)
        ((chiS ℓ w) • fderiv ℝ (fun w' => G w' y) w
          + (G w y) • fderiv ℝ (chiS ℓ) w) w :=
      hchi.hasFDerivAt.mul (hder w y).hasFDerivAt
    have hval : fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))
        = chiS ℓ w * fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))
          + G w y * fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ)) := by
      rw [hd.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hval]
    have h1 : ‖chiS ℓ w * fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))
          + G w y * fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖
          + ‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ :=
      (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    have h2 : (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖
          + ‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
        ≤ 2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
              (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
          + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
              (EuclideanSpace.single j (1 : ℝ))‖) ^ 2 := by
      nlinarith [sq_nonneg (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
              (EuclideanSpace.single j (1 : ℝ))‖
            - ‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hS : (0 : ℝ) ≤ ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have h2 : (∑ j : Fin 3,
      (2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
        + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2))
      = 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        + 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hsum : (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ 2 * Kc * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        + 2 * Kg * ‖G w y‖ ^ 2 := by
    have h1 : (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        ≤ ∑ j : Fin 3, (2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                  (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
              + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                  (EuclideanSpace.single j (1 : ℝ))‖) ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    rw [h2] at h1
    have h3 : 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          ≤ 2 * Kc * (∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith [hKc w]) hS
    have h4 : 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          ≤ 2 * Kg * ‖G w y‖ ^ 2 := by
      have h5 : 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
            ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          ≤ 2 * ‖G w y‖ ^ 2 * Kg :=
        mul_le_mul_of_nonneg_left (hKg w) (by positivity)
      linarith [h5]
    linarith [h1, h3, h4]
  have hlast : (ℓ ^ 2)⁻¹ * ‖chiS ℓ w * G w y‖ ^ 2 ≤ (ℓ ^ 2)⁻¹ * Kc * ‖G w y‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    have h3 : (0 : ℝ) ≤ (ℓ ^ 2)⁻¹ := by positivity
    calc (ℓ ^ 2)⁻¹ * (‖chiS ℓ w‖ ^ 2 * ‖G w y‖ ^ 2)
        = (ℓ ^ 2)⁻¹ * ‖chiS ℓ w‖ ^ 2 * ‖G w y‖ ^ 2 := by ring
      _ ≤ (ℓ ^ 2)⁻¹ * Kc * ‖G w y‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hKc w) h3
  linarith [hsum, hlast]

/-! ## The per-fibre assembly -/

/-- **The pair-energy bound of the block I / III.1 fibre.**  From the analytic core of `pairGc13`
(pointwise mass and Dirichlet bounds, continuity, differentiability) and the three slice identities,
the pair energy of `pairGc13` is bounded by `C·cA²cB²·pinL2·(pinDir + pinL2)`. -/
theorem pairEnergy_pairGc13_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2), ∀ {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA → 0 ≤ cB →
      (∀ w y : E3, ‖pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ z.1 * memY13 ℓ p Θ₀ z.2) →
      Continuous (Function.uncurry (pairGc13 ℓ p hp Θ₀ A B)) →
      (∫ w in boxL ℓ, memX13 ℓ p Θ₀ w) = pinL2 ℓ Θ₀ →
      (∫ y in boxL ℓ, memY13 ℓ p Θ₀ y) = ℓ ^ 3 * pinL2 ℓ Θ₀ →
      (∫ w in boxL ℓ, dirX13 ℓ p Θ₀ w) ≤ pinDir ℓ Θ₀ →
      L1Tails.pairEnergy ℓ (pairGc13 ℓ p hp Θ₀ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ * (pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) := by
  obtain ⟨Kg, hKg0, hKg⟩ := exists_chiS_grad_bound ℓ hℓ
  obtain ⟨Kc, hKc0, hKc⟩ := exists_chiS_bound ℓ hℓ
  refine ⟨ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc),
    mul_nonneg (by positivity) (le_max_of_le_left (add_nonneg (by linarith) (by positivity))), ?_⟩
  intro p hp Θ₀ A B cA cB hΘ₀ hcA hcB hval hder hdb hcont hsliceX hsliceY hsliceD
  obtain ⟨Cx, hCx0, hCx⟩ := memX13_le hℓ p hΘ₀.continuous
  obtain ⟨Cy, hCy0, hCy⟩ := memY13_le hℓ p hΘ₀.continuous
  obtain ⟨Cd, hCd0, hCd⟩ := dirX13_le hℓ p hΘ₀
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hMx0 : ∀ w, 0 ≤ memX13 ℓ p Θ₀ w := fun w => integral_nonneg fun z => by positivity
  have hMy0 : ∀ y, 0 ≤ memY13 ℓ p Θ₀ y := fun y => integral_nonneg fun z => by positivity
  have hDx0 : ∀ w, 0 ≤ dirX13 ℓ p Θ₀ w :=
    fun w => Finset.sum_nonneg fun j _ => integral_nonneg fun z => by positivity
  have hpin0 : 0 ≤ pinL2 ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hpinD0 : 0 ≤ pinDir ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hMxs : StronglyMeasurable (memX13 ℓ p Θ₀) :=
    stronglyMeasurable_memX13 (ℓ := ℓ) p hΘ₀.continuous
  have hMys : StronglyMeasurable (memY13 ℓ p Θ₀) :=
    stronglyMeasurable_memY13 (ℓ := ℓ) p hΘ₀.continuous
  have hDxs : StronglyMeasurable (dirX13 ℓ p Θ₀) := stronglyMeasurable_dirX13 (ℓ := ℓ) p hΘ₀
  have hcs0 : 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 :=
    mul_nonneg (mul_nonneg (sq_nonneg cA) (sq_nonneg cB)) (by positivity)
  have hPhi0 : ∀ w, 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w :=
    fun w => mul_nonneg hcs0 (hMx0 w)
  have hDPhi0 : ∀ w, 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ w :=
    fun w => mul_nonneg hcs0 (hDx0 w)
  -- the mass bound
  have hmass : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2)
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀) := by
    have h1 := setIntegral_prod_le_factor (ℓ := ℓ)
      (f := fun w y => ‖pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2)
      (Φ := fun w => cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w)
      (Ψ := memY13 ℓ p Θ₀)
      (fun w y => by positivity)
      hPhi0 hMy0 (hMxs.const_mul _) hMys
      ⟨cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx, fun w hw =>
        mul_le_mul_of_nonneg_left (hCx w hw) hcs0⟩
      ⟨Cy, fun y hy => hCy y hy⟩
      (fun w y => hval w y)
    rw [MeasureTheory.integral_const_mul] at h1
    rw [hsliceX, hsliceY] at h1
    exact h1
  -- the Dirichlet bound
  have hdir : (∫ z in boxL ℓ ×ˢ boxL ℓ, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDir ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀) := by
    have h1 := setIntegral_prod_le_factor (ℓ := ℓ)
      (f := fun w y => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      (Φ := fun w => cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ w)
      (Ψ := memY13 ℓ p Θ₀)
      (fun w y => Finset.sum_nonneg fun j _ => by positivity)
      hDPhi0 hMy0 (hDxs.const_mul _) hMys
      ⟨cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd, fun w hw =>
        mul_le_mul_of_nonneg_left (hCd w hw) hcs0⟩
      ⟨Cy, fun y hy => hCy y hy⟩
      (fun w y => hdb (w, y))
    rw [MeasureTheory.integral_const_mul] at h1
    have hMy0' : (0 : ℝ) ≤ ∫ y in boxL ℓ, memY13 ℓ p Θ₀ y :=
      integral_nonneg fun y => hMy0 y
    refine h1.trans ?_
    rw [hsliceY]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsliceD hcs0)
      (mul_nonneg (by positivity) hpin0)
  -- pointwise bounds on the box squared
  have hGbound : ∀ z ∈ boxL ℓ ×ˢ boxL ℓ,
      ‖pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy := by
    rintro ⟨w, y⟩ hz
    refine (hval w y).trans ?_
    calc cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y
        = (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y) := by ring
      _ ≤ (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (Cx * Cy) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hCx w hz.1) (hCy y hz.2) (hMy0 y) hCx0) hcs0
      _ = cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy := by ring
  have hDbound : ∀ z ∈ boxL ℓ ×ˢ boxL ℓ, (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy := by
    rintro ⟨w, y⟩ hz
    refine (hdb (w, y)).trans ?_
    calc cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y
        = (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (dirX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y) := by ring
      _ ≤ (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (Cd * Cy) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hCd w hz.1) (hCy y hz.2) (hMy0 y) hCd0) hcs0
      _ = cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy := by ring
  -- integrability of the mass integrand
  have hGsq_int : IntegrableOn (fun z : E3 × E3 => ‖pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine IntegrableOn.of_bound volume_boxL_prod_lt_top
      ((aestronglyMeasurable_fibre hcont).mono_measure Measure.restrict_le_self)
      (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hGbound z hz
  -- integrability of the Dirichlet integrand
  have hD_int : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine IntegrableOn.of_bound volume_boxL_prod_lt_top
      ((aesm_dirIntegrand hcont).mono_measure Measure.restrict_le_self)
      (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => by positivity)]
    exact hDbound z hz
  -- integrability of the pair-energy integrand
  have hF_int : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine IntegrableOn.of_bound volume_boxL_prod_lt_top
      ((aesm_LHSIntegrand hcont).mono_measure Measure.restrict_le_self)
      ((2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy)
        + 2 * Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy)) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (LHSIntegrand_le hℓ hKg hKc (fun w y => hder (w, y)) z.1 z.2).trans ?_
    have h3 : 0 ≤ 2 * Kg + (ℓ ^ 2)⁻¹ * Kc :=
      add_nonneg (by linarith) (by positivity)
    have h4 : 0 ≤ 2 * Kc := by linarith
    exact add_le_add (mul_le_mul_of_nonneg_left (hGbound z hz) h3)
      (mul_le_mul_of_nonneg_left (hDbound z hz) h4)
  -- the assembly
  have hmain : L1Tails.pairEnergy ℓ (pairGc13 ℓ p hp Θ₀ A B)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀
            * (ℓ ^ 3 * pinL2 ℓ Θ₀))
        + 2 * Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDir ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀)) :=
    pairEnergy_le_of_box_bounds (ℓ := ℓ) hℓ hKg0 hKc0
      (by have := hpin0; positivity)
      (by have := hpinD0; positivity)
      hKg hKc
      hF_int hGsq_int hD_int (Eventually.of_forall fun z => hder z) hmass hdir
  -- the arithmetic
  have h0 : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg cA) (sq_nonneg cB)) (by positivity)) hpin0
  have hkey : (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * pinL2 ℓ Θ₀ + 2 * Kc * pinDir ℓ Θ₀
      ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc) * (pinL2 ℓ Θ₀ + pinDir ℓ Θ₀) := by
    have h1 : 2 * Kg + (ℓ ^ 2)⁻¹ * Kc ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc) :=
      le_max_left _ _
    have h2 : 2 * Kc ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc) := le_max_right _ _
    nlinarith [h1, h2, hpin0, hpinD0]
  have hcalc : (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀
            * (ℓ ^ 3 * pinL2 ℓ Θ₀))
        + 2 * Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDir ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀))
      ≤ (ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc)) * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀
          * (pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) := by
    calc (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀
              * (ℓ ^ 3 * pinL2 ℓ Θ₀))
          + 2 * Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDir ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀))
        = (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀)
            * ((2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * pinL2 ℓ Θ₀ + 2 * Kc * pinDir ℓ Θ₀) := by
          ring
      _ ≤ (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀)
            * (max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc) * (pinL2 ℓ Θ₀ + pinDir ℓ Θ₀)) :=
          mul_le_mul_of_nonneg_left hkey h0
      _ = (ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc)) * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀
            * (pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) := by ring
  linarith [hmain, hcalc]

/-- **Generic assembly**: if the fibre `G` is pointwise dominated by `P` in mass and by `Q` in its
Dirichlet sum, with `∫P ≤ A` and `∫Q ≤ B` on the box squared, then its pair energy is at most
`C·(A+B)`. -/
theorem pairEnergy_le_of_integral_bounds {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : E3 → E3 → ℂ} {P Q : E3 × E3 → ℝ} {A B : ℝ},
      0 ≤ A → 0 ≤ B → (∀ z, 0 ≤ P z) → (∀ z, 0 ≤ Q z) →
      (∀ z : E3 × E3, ‖G z.1 z.2‖ ^ 2 ≤ P z) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Q z) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => G w' z.2) z.1) →
      Continuous (Function.uncurry G) →
      IntegrableOn P (boxL ℓ ×ˢ boxL ℓ) →
      IntegrableOn Q (boxL ℓ ×ˢ boxL ℓ) →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, P z) ≤ A →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, Q z) ≤ B →
      L1Tails.pairEnergy ℓ G ≤ C * (A + B) := by
  obtain ⟨Kg, hKg0, hKg⟩ := exists_chiS_grad_bound ℓ hℓ
  obtain ⟨Kc, hKc0, hKc⟩ := exists_chiS_bound ℓ hℓ
  refine ⟨max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc),
    le_max_of_le_left (add_nonneg (by linarith) (by positivity)), ?_⟩
  intro G P Q A B hA0 hB0 hP0 hQ0 hval hdb hder hcont hPint hQint hP hQ
  have hc1 : 0 ≤ 2 * Kg + (ℓ ^ 2)⁻¹ * Kc := add_nonneg (by linarith) (by positivity)
  have hc2 : 0 ≤ 2 * Kc := by linarith
  have hFpt : ∀ z : E3 × E3, (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * P z + 2 * Kc * Q z := by
    intro z
    refine (LHSIntegrand_le hℓ hKg hKc (fun w y => hder (w, y)) z.1 z.2).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left (hval z) hc1)
      (mul_le_mul_of_nonneg_left (hdb z) hc2)
  have hFint : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono'
      ((hPint.const_mul (2 * Kg + (ℓ ^ 2)⁻¹ * Kc)).add (hQint.const_mul (2 * Kc)))
      ((aesm_LHSIntegrand hcont).mono_measure Measure.restrict_le_self) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hFpt z
  have hGsqint : IntegrableOn (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono' hPint
      ((aestronglyMeasurable_fibre hcont).mono_measure Measure.restrict_le_self) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hval z
  have hDint : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono' hQint
      ((aesm_dirIntegrand hcont).mono_measure Measure.restrict_le_self) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => by positivity)]
    exact hdb z
  have hmass : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2) ≤ A :=
    (integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hPint
      (Eventually.of_forall fun z => hval z)).trans hP
  have hdir : (∫ z in boxL ℓ ×ˢ boxL ℓ, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ≤ B :=
    (integral_mono_of_nonneg
      (Eventually.of_forall fun z => Finset.sum_nonneg fun j _ => by positivity) hQint
      (Eventually.of_forall fun z => hdb z)).trans hQ
  have hmain := pairEnergy_le_of_box_bounds (ℓ := ℓ) hℓ hKg0 hKc0
    (by positivity) (by positivity) hKg hKc hFint hGsqint hDint
    (Eventually.of_forall fun z => hder z) hmass hdir
  nlinarith [hmain, hA0, hB0, le_max_left (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc),
    le_max_right (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) (2 * Kc)]

/-- A bounded measurable function is integrable on the box squared. -/
theorem integrableOn_boxL_prod_of_aeBound {ℓ : ℝ} {f : E3 × E3 → ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (boxL ℓ ×ˢ boxL ℓ))) {C : ℝ}
    (hC : ∀ᵐ z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)), ‖f z‖ ≤ C) :
    IntegrableOn f (boxL ℓ ×ˢ boxL ℓ) :=
  IntegrableOn.of_bound volume_boxL_prod_lt_top hfm C hC

/-- **The pair-energy bound of the block II.2 fibre `pairGc23`.** -/
theorem pairEnergy_pairGc23_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2), ∀ {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA → 0 ≤ cB →
      (∀ w y : E3, ‖pairGc23 ℓ p hp Θ₀ A B w y‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y * pinL2 ℓ Θ₀) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀) →
      Continuous (Function.uncurry (pairGc23 ℓ p hp Θ₀ A B)) →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, memX23 ℓ p Θ₀ z.1 z.2) = pinL2 ℓ Θ₀ →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, dirX23 ℓ p Θ₀ z.1 z.2) ≤ pinDir ℓ Θ₀ →
      L1Tails.pairEnergy ℓ (pairGc23 ℓ p hp Θ₀ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ * (pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) := by
  obtain ⟨Cg, hCg0, hCg⟩ := pairEnergy_le_of_integral_bounds (ℓ := ℓ) hℓ
  refine ⟨Cg * ℓ ^ 6, by positivity, ?_⟩
  intro p hp Θ₀ A B cA cB hΘ₀ hcA hcB hval hder hdb hcont hsliceM hsliceD
  obtain ⟨CM, hCM0, hCM⟩ := memX23_le hℓ p hΘ₀.continuous
  obtain ⟨CD, hCD0, hCD⟩ := dirX23_le hℓ p hΘ₀
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hpin0 : 0 ≤ pinL2 ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hpinD0 : 0 ≤ pinDir ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hcs0 : 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 :=
    mul_nonneg (mul_nonneg (sq_nonneg cA) (sq_nonneg cB)) (by positivity)
  have hhc : 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ := mul_nonneg hcs0 hpin0
  have hM0 : ∀ z : E3 × E3, 0 ≤ memX23 ℓ p Θ₀ z.1 z.2 :=
    fun z => integral_nonneg fun x => by positivity
  have hD0 : ∀ z : E3 × E3, 0 ≤ dirX23 ℓ p Θ₀ z.1 z.2 :=
    fun z => Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  have hMs : StronglyMeasurable (Function.uncurry (memX23 ℓ p Θ₀)) :=
    stronglyMeasurable_memX23 (ℓ := ℓ) p hΘ₀.continuous
  have hDs : StronglyMeasurable (Function.uncurry (dirX23 ℓ p Θ₀)) :=
    stronglyMeasurable_dirX23 (ℓ := ℓ) p hΘ₀
  have hP0 : ∀ z : E3 × E3,
      0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀ :=
    fun z => mul_nonneg (mul_nonneg hcs0 (hM0 z)) hpin0
  have hQ0 : ∀ z : E3 × E3,
      0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀ :=
    fun z => mul_nonneg (mul_nonneg hcs0 (hD0 z)) hpin0
  have hPint : IntegrableOn (fun z : E3 × E3 =>
      cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := cA ^ 2 * cB ^ 2 * ℓ ^ 6 * CM * pinL2 ℓ Θ₀) ?_ ?_
    · exact ((hMs.const_mul (cA ^ 2 * cB ^ 2 * ℓ ^ 6)).mul_const
        (pinL2 ℓ Θ₀)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 z)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hCM z.1 hz.1 z.2 hz.2) hcs0) hpin0
      -- bound
  have hQint : IntegrableOn (fun z : E3 × E3 =>
      cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := cA ^ 2 * cB ^ 2 * ℓ ^ 6 * CD * pinL2 ℓ Θ₀) ?_ ?_
    · exact ((hDs.const_mul (cA ^ 2 * cB ^ 2 * ℓ ^ 6)).mul_const
        (pinL2 ℓ Θ₀)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 z)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hCD z.1 hz.1 z.2 hz.2) hcs0) hpin0
  have hP : (∫ z in boxL ℓ ×ˢ boxL ℓ,
        cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀ := by
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul, hsliceM]
  have hQ : (∫ z in boxL ℓ ×ˢ boxL ℓ,
        cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDir ℓ Θ₀ := by
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
    calc (cA ^ 2 * cB ^ 2 * ℓ ^ 6
            * (∫ z in boxL ℓ ×ˢ boxL ℓ, dirX23 ℓ p Θ₀ z.1 z.2)) * pinL2 ℓ Θ₀
        ≤ (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinDir ℓ Θ₀) * pinL2 ℓ Θ₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsliceD hcs0) hpin0
      _ = cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDir ℓ Θ₀ := by ring
  have hC := hCg (G := pairGc23 ℓ p hp Θ₀ A B)
    (P := fun z : E3 × E3 => cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
    (Q := fun z : E3 × E3 => cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
    (A := cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀)
    (B := cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDir ℓ Θ₀)
    (by positivity) (by positivity) hP0 hQ0
    (fun z => hval z.1 z.2) (fun z => hdb z) hder hcont hPint hQint hP hQ
  have h1 : Cg * (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀
        + cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDir ℓ Θ₀)
      = (Cg * ℓ ^ 6) * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ * (pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) := by
    ring
  linarith [hC, h1.le]

/-- **The pair-energy bound of the block II.1 fibre `pairGc21`.** -/
theorem pairEnergy_pairGc21_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2), ∀ {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA →
      (∀ u y : E3, ‖pairGc21 ℓ p hp Θ₀ A u y‖ ^ 2
        ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ y u) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1) →
      Continuous (Function.uncurry (pairGc21 ℓ p hp Θ₀ A)) →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, memY21 ℓ p Θ₀ z.2 z.1) = pinL2 ℓ Θ₀ →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, dirY21 ℓ p Θ₀ z.2 z.1) ≤ pinDir ℓ Θ₀ →
      L1Tails.pairEnergy ℓ (pairGc21 ℓ p hp Θ₀ A)
        ≤ C * cA ^ 4 * pinL2 ℓ Θ₀ * (pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) := by
  obtain ⟨Cg, hCg0, hCg⟩ := pairEnergy_le_of_integral_bounds (ℓ := ℓ) hℓ
  refine ⟨Cg * ℓ ^ 6, by positivity, ?_⟩
  intro p hp Θ₀ A cA hΘ₀ hcA hval hder hdb hcont hsliceM hsliceD
  obtain ⟨CM, hCM0, hCM⟩ := memY21_le hℓ p hΘ₀.continuous
  obtain ⟨CD, hCD0, hCD⟩ := dirY21_le hℓ p hΘ₀
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hpin0 : 0 ≤ pinL2 ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hpinD0 : 0 ≤ pinDir ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hc0 : 0 ≤ cA ^ 4 * ℓ ^ 6 := mul_nonneg (by positivity) (by positivity)
  have hcc : 0 ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ := mul_nonneg hc0 hpin0
  have hM0 : ∀ z : E3 × E3, 0 ≤ memY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => integral_nonneg fun x => by positivity
  have hD0 : ∀ z : E3 × E3, 0 ≤ dirY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  have hMs : StronglyMeasurable (Function.uncurry (memY21 ℓ p Θ₀)) :=
    stronglyMeasurable_memY21 (ℓ := ℓ) p hΘ₀.continuous
  have hDs : StronglyMeasurable (Function.uncurry (dirY21 ℓ p Θ₀)) :=
    stronglyMeasurable_dirY21 (ℓ := ℓ) p hΘ₀
  have hP0 : ∀ z : E3 × E3,
      0 ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => mul_nonneg hcc (hM0 z)
  have hQ0 : ∀ z : E3 × E3,
      0 ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => mul_nonneg hcc (hD0 z)
  have hPint : IntegrableOn (fun z : E3 × E3 =>
      cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * CM) ?_ ?_
    · have hswap : Measurable (fun z : E3 × E3 => (z.2, z.1)) :=
        Measurable.prod measurable_snd measurable_fst
      exact ((hMs.comp_measurable hswap).const_mul
        (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 z)]
      exact mul_le_mul_of_nonneg_left (hCM z.2 hz.2 z.1 hz.1) hcc
  have hQint : IntegrableOn (fun z : E3 × E3 =>
      cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * CD) ?_ ?_
    · have hswap : Measurable (fun z : E3 × E3 => (z.2, z.1)) :=
        Measurable.prod measurable_snd measurable_fst
      exact ((hDs.comp_measurable hswap).const_mul
        (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 z)]
      exact mul_le_mul_of_nonneg_left (hCD z.2 hz.2 z.1 hz.1) hcc
  have hP : (∫ z in boxL ℓ ×ˢ boxL ℓ,
        cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1)
      ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀ := by
    rw [MeasureTheory.integral_const_mul, hsliceM]
  have hQ : (∫ z in boxL ℓ ×ˢ boxL ℓ,
        cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1)
      ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDir ℓ Θ₀ := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hsliceD hcc
  have hC := hCg (G := pairGc21 ℓ p hp Θ₀ A)
    (P := fun z : E3 × E3 => cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1)
    (Q := fun z : E3 × E3 => cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1)
    (A := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀)
    (B := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDir ℓ Θ₀)
    (by positivity) (by positivity) hP0 hQ0
    (fun z => hval z.1 z.2) (fun z => hdb z) hder hcont hPint hQint hP hQ
  have h1 : Cg * (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀
        + cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDir ℓ Θ₀)
      = (Cg * ℓ ^ 6) * cA ^ 4 * pinL2 ℓ Θ₀ * (pinDir ℓ Θ₀ + pinL2 ℓ Θ₀) := by
    ring
  linarith [hC, h1.le]

end Work.BoseBoxFock
