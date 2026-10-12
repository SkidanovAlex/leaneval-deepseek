import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRKDefs
import Submission.Work.BoseBoxFock.TauSmAdm.Radial
import Submission.Work.BoseBoxFock.TauSmAdm.TailBound
import Submission.Work.BoseBoxFock.TauSmAdm.integrable_and_integral_iteratedFDeriv_comp_const_smul
import Submission.Work.BoseBoxFock.TauSmAdm.integrable_one_add_norm_zpow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory Filter

noncomputable section

/-- **Admissibility of the smoothed kinetic symbol `τ̃`.**  There is a constant `K₆` such that for
every admissible choice of parameters the function `p ↦ tauSm eT s d ℓ p` is `C^∞`, nonnegative,
of quadratic growth, with integrable sixth iterated derivative, and
`∫ ‖D⁶ (tauSm eT s d ℓ)‖ ≤ K₆ · (2 s ℓ)`.

Writing `c = 2 s ℓ` and `b = 2 d s ℓ`, the symbol is the sum of two dilates of
`f₀ = tauProf ‖·‖`: `tauSm = (1-eT) c^{-2} • (f₀ ∘ (c •)) + eT b^{-2} • (f₀ ∘ (b •))`.  The
integral of `‖D⁶‖` of a dilate scales as `a³ K₆`, giving the total `(1-eT) c K₆ + eT b K₆ ≤ c K₆`;
the integrability of `‖D⁶ f₀‖` comes from the tail bound `TauSmAdm.exists_tail_bound` (decay
`(1+‖p‖)^{-5}`) together with the compactness bound on a ball. -/
theorem tauSm_admissible : ∃ K₆ : ℝ, 0 ≤ K₆ ∧
    ∀ {eT s d ℓ : ℝ}, 0 < s → 0 < d → d ≤ 1 → 0 ≤ eT → eT ≤ 1 → 0 < ℓ →
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseBoxFock.tauSm eT s d ℓ) ∧
    (∀ p, 0 ≤ Work.BoseBoxFock.tauSm eT s d ℓ p) ∧
    (∃ A : ℝ, ∀ p, |Work.BoseBoxFock.tauSm eT s d ℓ p| ≤ A * (1 + ‖p‖) ^ 2) ∧
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖iteratedFDeriv ℝ 6 (Work.BoseBoxFock.tauSm eT s d ℓ) p‖) ∧
    (∫ p : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ 6 (Work.BoseBoxFock.tauSm eT s d ℓ) p‖) ≤ K₆ * (2 * s * ℓ) := by
  -- ## the reference function `f₀ = tauProf ‖·‖`
  set f₀ : EuclideanSpace ℝ (Fin 3) → ℝ := fun q => tauProf ‖q‖ with hf₀def
  have hf₀ : ContDiff ℝ (⊤ : ℕ∞) f₀ := by
    rw [hf₀def]
    exact TauSmAdm.radial_contDiff tauPhi_contDiff tauPhi_zero_of_le_one
  have hcont₆ : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => iteratedFDeriv ℝ 6 f₀ p) :=
    hf₀.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  have hf₀nn : ∀ q : EuclideanSpace ℝ (Fin 3), 0 ≤ f₀ q := by
    intro q
    rw [hf₀def]
    exact tauPhi_nonneg _
  have hf₀le : ∀ q : EuclideanSpace ℝ (Fin 3), f₀ q ≤ ‖q‖ ^ 2 := by
    intro q
    rw [hf₀def]
    calc tauProf ‖q‖ ≤ (max 0 (‖q‖ - 1)) ^ 2 := tauPhi_le _
      _ ≤ ‖q‖ ^ 2 := by
          rcases le_or_gt ‖q‖ 1 with h | h
          · rw [max_eq_left (by linarith)]
            nlinarith [norm_nonneg q]
          · rw [max_eq_right (by linarith)]
            nlinarith [h]
  -- ## integrability of `‖D⁶ f₀‖`
  have hInt₀ : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖iteratedFDeriv ℝ 6 f₀ p‖) := by
    obtain ⟨Ctail, hCtail0, hCtail⟩ := TauSmAdm.exists_tail_bound
    obtain ⟨Cball, hCball⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 3).exists_bound_of_continuousOn
        hcont₆.continuousOn
    have htail' : ∀ p : EuclideanSpace ℝ (Fin 3), 3 ≤ ‖p‖ →
        ‖iteratedFDeriv ℝ 6 f₀ p‖ ≤ Ctail * (1 + ‖p‖) ^ (-(5:ℤ)) := by
      intro p hp
      rw [hf₀def]
      exact hCtail p hp
    refine MeasureTheory.Integrable.mono'
      (TauSmAdm.integrable_one_add_norm_zpow.const_mul
        (max (max Cball 0 * 1024) (32 * Ctail)))
      hcont₆.norm.aestronglyMeasurable (Eventually.of_forall ?_)
    intro p
    simp only [norm_norm]
    by_cases hp : ‖p‖ ≤ 3
    · have h1 : ‖iteratedFDeriv ℝ 6 f₀ p‖ ≤ max Cball 0 :=
        le_trans (hCball p (by rw [Metric.mem_closedBall, dist_zero_right]; exact hp))
          (le_max_left _ _)
      have h2 : (1:ℝ) ≤ 1024 * (1 + ‖p‖) ^ (-(5:ℤ)) := by
        have h4 : 1 + ‖p‖ ≤ 4 := by linarith [norm_nonneg p]
        have h3 : (1 + ‖p‖) ^ 5 ≤ 1024 := by
          calc (1 + ‖p‖) ^ 5 ≤ 4 ^ 5 := by gcongr
            _ = 1024 := by norm_num
        have h5 : (0:ℝ) < (1 + ‖p‖) ^ 5 := by positivity
        have h7 : (1:ℝ) ≤ 1024 * ((1 + ‖p‖) ^ 5)⁻¹ := by
          have h6 := mul_le_mul_of_nonneg_right h3
            (by positivity : (0:ℝ) ≤ ((1 + ‖p‖) ^ 5)⁻¹)
          rwa [mul_inv_cancel₀ h5.ne'] at h6
        rw [zpow_neg]
        exact h7
      have h5 : (0:ℝ) ≤ (1 + ‖p‖) ^ (-(5:ℤ)) := by positivity
      calc ‖iteratedFDeriv ℝ 6 f₀ p‖ ≤ max Cball 0 := h1
        _ = (max Cball 0) * 1 := by ring
        _ ≤ (max Cball 0) * (1024 * (1 + ‖p‖) ^ (-(5:ℤ))) :=
              mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
        _ ≤ max (max Cball 0 * 1024) (32 * Ctail) * (1 + ‖p‖) ^ (-(5:ℤ)) := by
              rw [show (max Cball 0) * (1024 * (1 + ‖p‖) ^ (-(5:ℤ)))
                  = (max Cball 0 * 1024) * (1 + ‖p‖) ^ (-(5:ℤ)) from by ring]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) h5
    · have hp3 : 3 ≤ ‖p‖ := le_of_lt (not_le.mp hp)
      have h1 := htail' p hp3
      have h6 : Ctail * (1 + ‖p‖) ^ (-(5:ℤ))
          ≤ max (max Cball 0 * 1024) (32 * Ctail) * (1 + ‖p‖) ^ (-(5:ℤ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc Ctail = Ctail * 1 := by ring
          _ ≤ Ctail * 32 := mul_le_mul_of_nonneg_left (by norm_num) hCtail0
          _ = 32 * Ctail := by ring
          _ ≤ max (max Cball 0 * 1024) (32 * Ctail) := le_max_right _ _
      exact le_trans h1 h6
  -- ## the main argument
  refine ⟨∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f₀ p‖,
    integral_nonneg (fun p => norm_nonneg _), ?_⟩
  intro eT s d ℓ hs hd hd1 heT0 heT1 hℓ
  have hK₆0 : (0:ℝ) ≤ ∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f₀ p‖ :=
    integral_nonneg (fun p => norm_nonneg _)
  -- the two scales
  set c : ℝ := 2 * s * ℓ with hc
  set b : ℝ := 2 * d * s * ℓ with hb
  have hcpos : 0 < c := by rw [hc]; positivity
  have hbpos : 0 < b := by rw [hb]; positivity
  have hbc : b ≤ c := by
    rw [hc, hb]
    nlinarith [hs, hℓ, hd, hd1]
  -- the two transformed reference functions
  set F₁ : EuclideanSpace ℝ (Fin 3) → ℝ := fun p => f₀ (c • p) with hF₁
  set F₂ : EuclideanSpace ℝ (Fin 3) → ℝ := fun p => f₀ (b • p) with hF₂
  have hF₁cd : ContDiff ℝ (⊤ : ℕ∞) F₁ := by
    rw [hF₁]
    exact hf₀.comp_continuousLinearMap (g := c • (1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
  have hF₂cd : ContDiff ℝ (⊤ : ℕ∞) F₂ := by
    rw [hF₂]
    exact hf₀.comp_continuousLinearMap (g := b • (1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
  -- the symbol is a sum of two dilates
  have hfun : tauSm eT s d ℓ = ((1 - eT) * (c ^ 2)⁻¹) • F₁ + (eT * (b ^ 2)⁻¹) • F₂ := by
    funext p
    have harg₁ : ‖p‖ / (2 * s * ℓ)⁻¹ = ‖(2 * s * ℓ) • p‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * s * ℓ), div_inv_eq_mul,
        mul_comm]
    have harg₂ : ‖p‖ / (2 * d * s * ℓ)⁻¹ = ‖(2 * d * s * ℓ) • p‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * d * s * ℓ), div_inv_eq_mul,
        mul_comm]
    rw [hF₁, hF₂, hc, hb, hf₀def]
    simp only [tauSm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [harg₁, harg₂, inv_pow, inv_pow]
  -- ## admissibility conjuncts
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (tauSm eT s d ℓ) := by
    rw [hfun]
    exact ((hF₁cd.const_smul ((1 - eT) * (c ^ 2)⁻¹)).add
      (hF₂cd.const_smul (eT * (b ^ 2)⁻¹)))
  have hnn : ∀ p, 0 ≤ tauSm eT s d ℓ p := by
    intro p
    rw [hfun]
    simp only [Pi.add_apply, Pi.smul_apply]
    refine add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) ?_)
      (mul_nonneg (mul_nonneg heT0 (by positivity)) ?_)
    · exact hf₀nn (c • p)
    · exact hf₀nn (b • p)
  have hpoly : ∃ A : ℝ, ∀ p, |tauSm eT s d ℓ p| ≤ A * (1 + ‖p‖) ^ 2 := by
    refine ⟨1, fun p => ?_⟩
    rw [abs_of_nonneg (hnn p), one_mul, hfun]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : (1 - eT) * (c ^ 2)⁻¹ * f₀ (c • p) ≤ (1 - eT) * ‖p‖ ^ 2 := by
      have h2 : f₀ (c • p) ≤ (c * ‖p‖) ^ 2 := by
        refine le_trans (hf₀le (c • p)) ?_
        rw [norm_smul, Real.norm_of_nonneg hcpos.le]
      have h3 : (c ^ 2)⁻¹ * (c * ‖p‖) ^ 2 = ‖p‖ ^ 2 := by
        field_simp
      calc (1 - eT) * (c ^ 2)⁻¹ * f₀ (c • p)
          ≤ (1 - eT) * (c ^ 2)⁻¹ * (c * ‖p‖) ^ 2 := by
            exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (by linarith) (by positivity))
        _ = (1 - eT) * ‖p‖ ^ 2 := by rw [mul_assoc, h3]
    have h4 : eT * (b ^ 2)⁻¹ * f₀ (b • p) ≤ eT * ‖p‖ ^ 2 := by
      have h2 : f₀ (b • p) ≤ (b * ‖p‖) ^ 2 := by
        refine le_trans (hf₀le (b • p)) ?_
        rw [norm_smul, Real.norm_of_nonneg hbpos.le]
      have h3 : (b ^ 2)⁻¹ * (b * ‖p‖) ^ 2 = ‖p‖ ^ 2 := by
        field_simp
      calc eT * (b ^ 2)⁻¹ * f₀ (b • p) ≤ eT * (b ^ 2)⁻¹ * (b * ‖p‖) ^ 2 := by
            exact mul_le_mul_of_nonneg_left h2 (mul_nonneg heT0 (by positivity))
        _ = eT * ‖p‖ ^ 2 := by rw [mul_assoc, h3]
    have h5 : (1 - eT) * ‖p‖ ^ 2 + eT * ‖p‖ ^ 2 = ‖p‖ ^ 2 := by ring
    have h6 : ‖p‖ ^ 2 ≤ (1 + ‖p‖) ^ 2 := by nlinarith [norm_nonneg p]
    linarith
  -- ## integrability of the sixth derivative and its integral
  have hInt₁ : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖iteratedFDeriv ℝ 6 F₁ p‖) := by
    rw [hF₁]
    exact ((TauSmAdm.integrable_and_integral_iteratedFDeriv_comp_const_smul hf₀ hcpos.ne').1).mpr hInt₀
  have hInt₂ : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖iteratedFDeriv ℝ 6 F₂ p‖) := by
    rw [hF₂]
    exact ((TauSmAdm.integrable_and_integral_iteratedFDeriv_comp_const_smul hf₀ hbpos.ne').1).mpr hInt₀
  have hIntg₁ : (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 F₁ p‖)
      = c ^ 3 * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f₀ p‖) := by
    rw [hF₁]
    rw [(TauSmAdm.integrable_and_integral_iteratedFDeriv_comp_const_smul hf₀ hcpos.ne').2,
      abs_of_pos hcpos]
  have hIntg₂ : (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 F₂ p‖)
      = b ^ 3 * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f₀ p‖) := by
    rw [hF₂]
    rw [(TauSmAdm.integrable_and_integral_iteratedFDeriv_comp_const_smul hf₀ hbpos.ne').2,
      abs_of_pos hbpos]
  have hint₁ : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (1 - eT) * (c ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₁ p‖) := hInt₁.const_mul _
  have hint₂ : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      eT * (b ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₂ p‖) := hInt₂.const_mul _
  have hdec : ∀ p : EuclideanSpace ℝ (Fin 3),
      iteratedFDeriv ℝ 6 (tauSm eT s d ℓ) p
        = ((1 - eT) * (c ^ 2)⁻¹) • iteratedFDeriv ℝ 6 F₁ p
          + (eT * (b ^ 2)⁻¹) • iteratedFDeriv ℝ 6 F₂ p := by
    intro p
    have h6le : ((6:ℕ) : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have hd₁ : ContDiffAt ℝ ((6:ℕ) : WithTop ℕ∞) (((1 - eT) * (c ^ 2)⁻¹) • F₁) p :=
      (hF₁cd.contDiffAt.const_smul ((1 - eT) * (c ^ 2)⁻¹)).of_le h6le
    have hd₂ : ContDiffAt ℝ ((6:ℕ) : WithTop ℕ∞) ((eT * (b ^ 2)⁻¹) • F₂) p :=
      (hF₂cd.contDiffAt.const_smul (eT * (b ^ 2)⁻¹)).of_le h6le
    rw [hfun, iteratedFDeriv_add_apply hd₁ hd₂,
      iteratedFDeriv_const_smul_apply (a := (1 - eT) * (c ^ 2)⁻¹)
        (hF₁cd.contDiffAt.of_le h6le),
      iteratedFDeriv_const_smul_apply (a := eT * (b ^ 2)⁻¹) (hF₂cd.contDiffAt.of_le h6le)]
  have hpoint : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ 6 (tauSm eT s d ℓ) p‖
        ≤ (1 - eT) * (c ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₁ p‖
          + eT * (b ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₂ p‖ := by
    intro p
    have hA₁ : (0:ℝ) ≤ (1 - eT) * (c ^ 2)⁻¹ := mul_nonneg (by linarith) (by positivity)
    have hA₂ : (0:ℝ) ≤ eT * (b ^ 2)⁻¹ := mul_nonneg heT0 (by positivity)
    calc ‖iteratedFDeriv ℝ 6 (tauSm eT s d ℓ) p‖
        = ‖((1 - eT) * (c ^ 2)⁻¹) • iteratedFDeriv ℝ 6 F₁ p
            + (eT * (b ^ 2)⁻¹) • iteratedFDeriv ℝ 6 F₂ p‖ := by rw [hdec p]
      _ ≤ ‖((1 - eT) * (c ^ 2)⁻¹) • iteratedFDeriv ℝ 6 F₁ p‖
            + ‖(eT * (b ^ 2)⁻¹) • iteratedFDeriv ℝ 6 F₂ p‖ := norm_add_le _ _
      _ = (1 - eT) * (c ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₁ p‖
            + eT * (b ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₂ p‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA₁,
            abs_of_nonneg hA₂]
  have hint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖iteratedFDeriv ℝ 6 (tauSm eT s d ℓ) p‖) := by
    refine MeasureTheory.Integrable.mono' (hint₁.add hint₂)
      ((hcd.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).norm).aestronglyMeasurable
      (Eventually.of_forall (fun p => by
        simp only [Pi.add_apply, norm_norm]
        exact hpoint p))
  refine ⟨hcd, hnn, hpoly, hint, ?_⟩
  calc (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 (tauSm eT s d ℓ) p‖)
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3), ((1 - eT) * (c ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₁ p‖
          + eT * (b ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 6 F₂ p‖) :=
        integral_mono_ae hint (hint₁.add hint₂)
          (Eventually.of_forall (fun p => by
            simp only [Pi.add_apply]
            exact hpoint p))
    _ = (1 - eT) * (c ^ 2)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 F₁ p‖)
          + eT * (b ^ 2)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 F₂ p‖) := by
        rw [integral_add hint₁ hint₂, integral_const_mul, integral_const_mul]
    _ = ((1 - eT) * c + eT * b) * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f₀ p‖) := by
        rw [hIntg₁, hIntg₂]
        field_simp <;> ring
    _ ≤ c * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f₀ p‖) := by
        refine mul_le_mul_of_nonneg_right ?_ hK₆0
        nlinarith [hbc, heT0, heT1]
    _ = (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 f₀ p‖) * (2 * s * ℓ) := by
        rw [hc]; ring

end

end Work.BoseBoxFock
