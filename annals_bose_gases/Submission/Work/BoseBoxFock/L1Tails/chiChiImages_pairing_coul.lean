import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.chiChiImages_split
import Submission.Work.BoseBoxFock.L1Tails.chiScale_le_of_gap
import Submission.Work.BoseBoxFock.L1Tails.coulombDual
import Submission.Work.BoseBoxFock.L1Tails.psiM_dirichlet_bound
import Submission.Work.BoseBoxFock.L1Tails.psiM_mass_bound
import Submission.Work.BoseBoxFock.L1Tails.psiM_pairing
import Submission.Work.BoseBoxFock.L1Tails.psiM_smooth_and_fderiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Filter
namespace Work.BoseBoxFock.L1Tails
local notation "E3" => EuclideanSpace ℝ (Fin 3)
open scoped Real BigOperators Topology

set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

/-! ## The `ℂ`-valued cutoff `θ_R = χ_{4R}` -/

/-- The `ℂ`-valued cutoff `θ_R = χ_{4R}` (un-normalised bump, `= 1` on the ball of radius `R`,
supported in the ball of radius `2R`). -/
def ThetaC (R : ℝ) : E3 → ℂ := fun z => ((pairTheta R z : ℝ) : ℂ)

lemma ThetaC_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (ThetaC R) :=
  Complex.ofRealCLM.contDiff.comp (pairTheta_contDiff R)

lemma ThetaC_norm_le (R : ℝ) (z : E3) : ‖ThetaC R z‖ ≤ 1 := by
  have h : ‖ThetaC R z‖ = |pairTheta R z| := by simp [ThetaC]
  rw [h, abs_of_nonneg (pairTheta_nonneg R z)]
  exact pairTheta_le_one R z

lemma ThetaC_eq_zero {R : ℝ} (hR : 0 < R) {z : E3} (hz : 2 * R ≤ ‖z‖) : ThetaC R z = 0 := by
  rw [ThetaC, pairTheta_eq_zero hR hz, Complex.ofReal_zero]

lemma ThetaC_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (ThetaC R) := by
  have h : HasCompactSupport (fun z : E3 => ((pairTheta R z : ℝ) : ℂ)) :=
    (pairTheta_hasCompactSupport hR).comp_left Complex.ofReal_zero
  exact h

lemma hasFDerivAt_ThetaC (R : ℝ) (z : E3) :
    HasFDerivAt (ThetaC R) (Complex.ofRealCLM.comp (fderiv ℝ (pairTheta R) z)) z := by
  have h1 : HasFDerivAt (Complex.ofRealCLM : ℝ → ℂ) Complex.ofRealCLM (pairTheta R z) :=
    Complex.ofRealCLM.hasFDerivAt
  have h2 : HasFDerivAt (pairTheta R) (fderiv ℝ (pairTheta R) z) z :=
    ((pairTheta_contDiff R).differentiable (by simp) z).hasFDerivAt
  exact h1.comp z h2

lemma fderiv_ThetaC_apply (R : ℝ) (z w : E3) :
    fderiv ℝ (ThetaC R) z w = ((fderiv ℝ (pairTheta R) z w : ℝ) : ℂ) := by
  rw [(hasFDerivAt_ThetaC R z).fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

lemma fderiv_ThetaC_eq_zero_of_gt {R : ℝ} (hR : 0 < R) {z : E3} (hz : 2 * R < ‖z‖) :
    fderiv ℝ (ThetaC R) z = 0 := by
  have hopen : {y : E3 | 2 * R < ‖y‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have hev : pairTheta R =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen] with y hy
    exact pairTheta_eq_zero hR hy.le
  have h0 : fderiv ℝ (pairTheta R) z = 0 := by rw [hev.fderiv_eq]; simp
  rw [(hasFDerivAt_ThetaC R z).fderiv, h0]
  ext w
  simp

/-- Pointwise bound for `fderiv (pairTheta R)`. -/
lemma norm_fderiv_pairTheta_apply_le {R : ℝ} (hR : 0 < R) (z w : E3) :
    ‖fderiv ℝ (pairTheta R) z w‖ ≤ (4 * R)⁻¹ * chiGB * ‖w‖ := by
  rw [fderiv_pairTheta_apply]
  calc ‖(4 * R)⁻¹ * fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z) w‖
      = (4 * R)⁻¹ * ‖fderiv ℝ Submission.BoseGases.chiBase ((4 * R)⁻¹ • z) w‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (4 * R)⁻¹ * (chiGB * ‖w‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right (chiBase_fderiv_le_chiGB _) (norm_nonneg _))
    _ = (4 * R)⁻¹ * chiGB * ‖w‖ := by ring

lemma norm_fderiv_ThetaC_apply_le {R : ℝ} (hR : 0 < R) (z w : E3) :
    ‖fderiv ℝ (ThetaC R) z w‖ ≤ (4 * R)⁻¹ * chiGB * ‖w‖ := by
  rw [fderiv_ThetaC_apply]
  have h1 : ‖((fderiv ℝ (pairTheta R) z w : ℝ) : ℂ)‖ = |fderiv ℝ (pairTheta R) z w| := by simp
  rw [h1, ← Real.norm_eq_abs]
  exact norm_fderiv_pairTheta_apply_le hR z w

/-! ## The bookkeeping identities for the energy `pairEnergy` -/

private lemma pairEnergy_self {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    pairEnergy ℓ G = pairDir ℓ G + pairMass ℓ G ∧ pairDir ℓ G = pairDir' ℓ G ∧
      pairMass ℓ G = pairMass' ℓ G ∧ 0 ≤ pairDir ℓ G ∧ 0 ≤ pairMass ℓ G := by
  have hbox : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := Work.BoseB4.BoxData.boxL_compact _ ℓ
  have hK : IsCompact (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    hbox.prod hbox
  have hAcont : Continuous (fun p : E3 × E3 => ∑ j : Fin 3, ‖pairVj ℓ G j p.1 p.2‖ ^ 2) :=
    continuous_finsetSum Finset.univ fun j _ =>
      ((continuous_pairVj (ℓ := ℓ) (m := 0) (G := G) hG j).norm).pow 2
  have hMcont : Continuous (fun p : E3 × E3 => (ℓ ^ 2)⁻¹ * ‖chiC ℓ p.1 * G p.1 p.2‖ ^ 2) :=
    ((((contDiff_chiC ℓ).continuous.comp continuous_fst).mul hG.continuous).norm.pow 2).const_mul _
  have hAi : Integrable (fun p : E3 × E3 => ∑ j : Fin 3, ‖pairVj ℓ G j p.1 p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact hK hAcont.continuousOn
  have hMi : Integrable (fun p : E3 × E3 => (ℓ ^ 2)⁻¹ * ‖chiC ℓ p.1 * G p.1 p.2‖ ^ 2)
      ((volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact hK hMcont.continuousOn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [pairEnergy, pairDir, pairMass, pairVj, chiC]
    exact integral_integral_add hAi hMi
  · simp only [pairDir, pairDir', pairVj, chiC]
    exact integral_integral_swap hAi
  · simp only [pairMass, pairMass', chiC]
    exact integral_integral_swap hMi
  · simp only [pairDir, pairVj, chiC]
    refine integral_nonneg_of_ae ?_
    filter_upwards with w
    refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => ?_)
    exact Finset.sum_nonneg fun j _ => by positivity
  · simp only [pairMass, chiC]
    refine integral_nonneg_of_ae ?_
    filter_upwards with w
    refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => ?_)
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg ℓ)) (by positivity)

/-! ## The per-image estimate -/

private lemma per_m_bound (K : ℕ) {Cg : ℝ} (hCgnn : 0 ≤ Cg)
    (hCg : ∀ {ℓ R : ℝ}, 0 < ℓ → 0 < R → R ≤ ℓ / 4 → ∀ {m : Fin 3 → ℤ}, m ≠ 0 →
      ∀ {z y : E3}, ‖z‖ ≤ 2 * R →
        Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
        Submission.BoseGases.chiScale ℓ y ≤ Cg * (R / ℓ) ^ (K + 1))
    {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hRℓ : R ≤ ℓ / 4)
    {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x, 0 ≤ W x)
    (hWs : ∀ x, R ≤ ‖x‖ → W x = 0) (hJ : MeasureTheory.Integrable (Work.BoseBoxFock.coulInt W))
    {G : E3 → E3 → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * G w y‖
      ≤ Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))
          * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
          * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G) := by
  have hεnn : 0 ≤ Cg * (R / ℓ) ^ (K + 1) :=
    mul_nonneg hCgnn (pow_nonneg (div_nonneg hR.le hℓ.le) _)
  have hgap : ∀ {z y : E3}, ‖z‖ ≤ 2 * R →
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
      Submission.BoseGases.chiScale ℓ y ≤ Cg * (R / ℓ) ^ (K + 1) :=
    fun {z y} hz hne => hCg hℓ hR hRℓ hm hz hne
  obtain ⟨hψcd, hψcs, hfderiv⟩ := psiM_smooth_and_fderiv (ℓ := ℓ) (m := m) (G := G) hG
  have hpair := psiM_pairing (ℓ := ℓ) (R := R) hℓ hm hWi hWs hG
  obtain ⟨hEeq, hDirEq, hMassEq, hDirnn, hMassnn⟩ := pairEnergy_self hℓ hG
  -- (1) the cutoff-times-`psiM` function
  set Ψ : E3 → ℂ := fun z => ThetaC R z * psiM ℓ m G z with hΨdef
  have hΨcd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [hΨdef]; exact (ThetaC_contDiff R).mul hψcd
  have hΨcs : HasCompactSupport Ψ := by
    rw [hΨdef]; exact (ThetaC_hasCompactSupport hR).mul_right
  -- (2) the pairing identity and the removal of the cutoff
  have hθeq : (∫ z, ((W z : ℝ) : ℂ) * Ψ z) = ∫ z, ((W z : ℝ) : ℂ) * psiM ℓ m G z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [hΨdef]
    dsimp only
    by_cases hWz : W z = 0
    · rw [hWz, Complex.ofReal_zero, zero_mul, zero_mul]
    · have hz : ‖z‖ < R := lt_of_not_ge (fun hcon => hWz (hWs z hcon))
      have h1 : pairTheta R z = 1 := pairTheta_eq_one hR hz.le
      rw [ThetaC, h1, Complex.ofReal_one, one_mul]
  -- (3) the derivative of `Ψ`
  have hfderivΨ : ∀ z : E3, fderiv ℝ Ψ z =
      ThetaC R z • fderiv ℝ (psiM ℓ m G) z
        + (psiM ℓ m G z) • fderiv ℝ (ThetaC R) z := by
    intro z
    rw [hΨdef]
    exact (((ThetaC_contDiff R).differentiable (by simp) z).hasFDerivAt.mul
      ((hψcd.differentiable (by simp)) z).hasFDerivAt).fderiv
  -- (4) the pointwise chain-rule bound
  have hpt : ∀ (j : Fin 3) (z : E3),
      ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ 2 * (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2) := by
    intro j z
    have hval : fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))
        = ThetaC R z * fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))
          + (psiM ℓ m G z) * fderiv ℝ (ThetaC R) z (EuclideanSpace.single j (1 : ℝ)) := by
      rw [hfderivΨ z, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hval]
    have hA : ‖ThetaC R z * fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ := by
      rw [norm_mul]
      calc ‖ThetaC R z‖ * _ ≤ 1 * _ :=
            mul_le_mul_of_nonneg_right (ThetaC_norm_le R z) (norm_nonneg _)
        _ = _ := one_mul _
    have hB : ‖(psiM ℓ m G z) * fderiv ℝ (ThetaC R) z (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ((4 * R)⁻¹ * chiGB) * ‖psiM ℓ m G z‖ := by
      rw [norm_mul, mul_comm (‖psiM ℓ m G z‖)
        (‖fderiv ℝ (ThetaC R) z (EuclideanSpace.single j (1 : ℝ))‖)]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h1 := norm_fderiv_ThetaC_apply_le hR z (EuclideanSpace.single j (1 : ℝ))
      have h2 : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
      rwa [h2, mul_one] at h1
    have hsum : ‖ThetaC R z * fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))
          + (psiM ℓ m G z) * fderiv ℝ (ThetaC R) z (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖
          + ((4 * R)⁻¹ * chiGB) * ‖psiM ℓ m G z‖ :=
      le_trans (norm_add_le _ _) (add_le_add hA hB)
    have hsq : (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖
          + ((4 * R)⁻¹ * chiGB) * ‖psiM ℓ m G z‖) ^ 2
        ≤ 2 * (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + (((4 * R)⁻¹ * chiGB) * ‖psiM ℓ m G z‖) ^ 2) := by
      nlinarith [sq_nonneg (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖
        - ((4 * R)⁻¹ * chiGB) * ‖psiM ℓ m G z‖)]
    calc ‖ThetaC R z * fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))
          + (psiM ℓ m G z) * fderiv ℝ (ThetaC R) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖
            + ((4 * R)⁻¹ * chiGB) * ‖psiM ℓ m G z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hsum 2
      _ ≤ 2 * (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + (((4 * R)⁻¹ * chiGB) * ‖psiM ℓ m G z‖) ^ 2) := hsq
      _ = 2 * (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2) := by ring
  -- (5) the `z`-support of `Ψ`
  have hsupp : ∀ j : Fin 3,
      ∫ z, ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        = ∫ z in Metric.closedBall (0 : E3) (2 * R),
            ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    intro j
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Metric.closedBall (0 : E3) (2 * R)) ?_).symm
    intro z hz
    have hz' : 2 * R < ‖z‖ := by
      rw [Metric.mem_closedBall, not_le, dist_zero_right] at hz
      exact hz
    have h0 : fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ)) = 0 := by
      rw [hfderivΨ z, ThetaC_eq_zero hR hz'.le, fderiv_ThetaC_eq_zero_of_gt hR hz']
      simp
    rw [h0, norm_zero]
    norm_num
  -- (6) the integral bound on the ball
  have hint : ∀ j : Fin 3,
      ∫ z in Metric.closedBall (0 : E3) (2 * R),
          ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ 2 * ((∫ z in Metric.closedBall (0 : E3) (2 * R),
              ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            + ((4 * R)⁻¹ * chiGB) ^ 2
              * (∫ z in Metric.closedBall (0 : E3) (2 * R), ‖psiM ℓ m G z‖ ^ 2)) := by
    intro j
    have hK : IsCompact (Metric.closedBall (0 : E3) (2 * R)) := isCompact_closedBall _ _
    have hcontA : Continuous
        (fun z : E3 => ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
      have h1 : Continuous (fun p : E3 × E3 => fderiv ℝ (psiM ℓ m G) p.1 p.2) :=
        hψcd.continuous_fderiv_apply (by simp)
      exact ((h1.comp (continuous_id.prodMk continuous_const)).norm).pow 2
    have hcontB : Continuous (fun z : E3 => ‖psiM ℓ m G z‖ ^ 2) :=
      (hψcd.continuous.norm).pow 2
    have hIntA : IntegrableOn
        (fun z : E3 => ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (Metric.closedBall (0 : E3) (2 * R)) volume :=
      hcontA.continuousOn.integrableOn_compact hK
    have hIntB : IntegrableOn (fun z : E3 => ‖psiM ℓ m G z‖ ^ 2)
        (Metric.closedBall (0 : E3) (2 * R)) volume :=
      hcontB.continuousOn.integrableOn_compact hK
    have hIntG : IntegrableOn
        (fun z : E3 => 2 * (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2))
        (Metric.closedBall (0 : E3) (2 * R)) volume :=
      (hIntA.add (hIntB.const_mul _)).const_mul _
    have hmono := setIntegral_mono_of_nonneg (s := Metric.closedBall (0 : E3) (2 * R))
      (f := fun z : E3 => ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      (g := fun z : E3 => 2 * (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2))
      (fun z _ => sq_nonneg _) (fun z _ => hpt j z) hIntG
    refine le_trans hmono ?_
    have step1 : (∫ z in Metric.closedBall (0 : E3) (2 * R),
          (2 * (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2)))
        = 2 * (∫ z in Metric.closedBall (0 : E3) (2 * R),
          (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2)) :=
      MeasureTheory.integral_const_mul _ _
    have step2 : (∫ z in Metric.closedBall (0 : E3) (2 * R),
          (‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2))
        = (∫ z in Metric.closedBall (0 : E3) (2 * R),
            ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          + (∫ z in Metric.closedBall (0 : E3) (2 * R),
            ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2) :=
      MeasureTheory.integral_add hIntA (hIntB.const_mul _)
    have step3 : (∫ z in Metric.closedBall (0 : E3) (2 * R),
            ((4 * R)⁻¹ * chiGB) ^ 2 * ‖psiM ℓ m G z‖ ^ 2)
        = ((4 * R)⁻¹ * chiGB) ^ 2
          * (∫ z in Metric.closedBall (0 : E3) (2 * R), ‖psiM ℓ m G z‖ ^ 2) :=
      MeasureTheory.integral_const_mul _ _
    rw [step1, step2, step3]
  -- (7) sum over the directions
  have hsum1 : ∑ j : Fin 3, ∫ z in Metric.closedBall (0 : E3) (2 * R),
        ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ 2 * ((∑ j : Fin 3, ∫ z in Metric.closedBall (0 : E3) (2 * R),
              ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            + 3 * ((4 * R)⁻¹ * chiGB) ^ 2
              * (∫ z in Metric.closedBall (0 : E3) (2 * R), ‖psiM ℓ m G z‖ ^ 2)) := by
    refine le_trans (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hint j)) ?_
    refine le_of_eq ?_
    have h1 : (∑ j : Fin 3, 2 * ((∫ z in Metric.closedBall (0 : E3) (2 * R),
            ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          + ((4 * R)⁻¹ * chiGB) ^ 2
            * (∫ z in Metric.closedBall (0 : E3) (2 * R), ‖psiM ℓ m G z‖ ^ 2)))
        = ∑ j : Fin 3, (2 * (∫ z in Metric.closedBall (0 : E3) (2 * R),
              ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            + 2 * (((4 * R)⁻¹ * chiGB) ^ 2
              * (∫ z in Metric.closedBall (0 : E3) (2 * R), ‖psiM ℓ m G z‖ ^ 2))) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  -- (8) the two delegated estimates and the constant bookkeeping
  have hdir := psiM_dirichlet_bound (ℓ := ℓ) (R := R)
    (ε := Cg * (R / ℓ) ^ (K + 1)) hℓ hεnn hG hfderiv hgap
  have hmass := psiM_mass_bound (ℓ := ℓ) (R := R)
    (ε := Cg * (R / ℓ) ^ (K + 1)) hℓ hεnn hG hgap
  have hPnn : 0 ≤ pairDir' ℓ G := hDirEq ▸ hDirnn
  have hQnn : 0 ≤ pairMass' ℓ G := hMassEq ▸ hMassnn
  have hstep : ∑ j : Fin 3, ∫ z in Metric.closedBall (0 : E3) (2 * R),
        ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ 2 * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 3 * pairDir' ℓ G
            + 3 * ((4 * R)⁻¹ * chiGB) ^ 2
              * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5 * pairMass' ℓ G)) := by
    refine le_trans hsum1 ?_
    have hB2 : 3 * ((4 * R)⁻¹ * chiGB) ^ 2
          * (∫ z in Metric.closedBall (0 : E3) (2 * R), ‖psiM ℓ m G z‖ ^ 2)
        ≤ 3 * ((4 * R)⁻¹ * chiGB) ^ 2
          * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5 * pairMass' ℓ G) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    exact mul_le_mul_of_nonneg_left (add_le_add hdir hB2) (by norm_num)
  -- (9) the constant comparison
  have hRlnn : 0 ≤ R / ℓ := div_nonneg hR.le hℓ.le
  have hRl1 : R / ℓ ≤ 1 := (div_le_one hℓ).mpr (le_trans hRℓ (by linarith))
  have hsq1 : (R / ℓ) ^ 2 ≤ 1 := by
    calc (R / ℓ) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hRlnn hRl1 2
      _ = 1 := by norm_num
  have hpowK : (R / ℓ) ^ (2 * (K + 1)) ≤ (R / ℓ) ^ (2 * K) := by
    rw [show 2 * (K + 1) = 2 * K + 2 by ring, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg hRlnn (2 * K)) hsq1
  have hcancel : (ℓ / R) ^ 2 * (R / ℓ) ^ 2 = 1 := by
    rw [← mul_pow]
    have h : ℓ / R * (R / ℓ) = 1 := by field_simp
    rw [h, one_pow]
  have hpowcancel : (ℓ / R) ^ 2 * (R / ℓ) ^ (2 * K + 2) = (R / ℓ) ^ (2 * K) := by
    rw [pow_add]
    calc (ℓ / R) ^ 2 * ((R / ℓ) ^ (2 * K) * (R / ℓ) ^ 2)
        = (R / ℓ) ^ (2 * K) * ((ℓ / R) ^ 2 * (R / ℓ) ^ 2) := by ring
      _ = (R / ℓ) ^ (2 * K) := by rw [hcancel, mul_one]
  have hc2eq : ((4 * R)⁻¹ * chiGB) ^ 2 * ℓ ^ 2 = (chiGB ^ 2 / 16) * (ℓ / R) ^ 2 := by
    field_simp
    ring
  have hε2eq : (Cg * (R / ℓ) ^ (K + 1)) ^ 2 = Cg ^ 2 * (R / ℓ) ^ (2 * (K + 1)) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (K + 1) 2]
  have hscal : 3 * ((4 * R)⁻¹ * chiGB) ^ 2
        * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5)
      = 3 * (chiGB ^ 2 / 16) * (Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3) := by
    rw [hε2eq]
    rw [show 3 * ((4 * R)⁻¹ * chiGB) ^ 2 * (Cg ^ 2 * (R / ℓ) ^ (2 * (K + 1)) * ℓ ^ 5)
        = 3 * (((4 * R)⁻¹ * chiGB) ^ 2 * ℓ ^ 2)
            * (Cg ^ 2 * (R / ℓ) ^ (2 * (K + 1)) * ℓ ^ 3) by ring]
    rw [hc2eq]
    rw [show 3 * ((chiGB ^ 2 / 16) * (ℓ / R) ^ 2)
          * (Cg ^ 2 * (R / ℓ) ^ (2 * (K + 1)) * ℓ ^ 3)
        = 3 * (chiGB ^ 2 / 16)
            * ((ℓ / R) ^ 2 * (R / ℓ) ^ (2 * (K + 1))) * (Cg ^ 2 * ℓ ^ 3) by ring]
    rw [show 2 * (K + 1) = 2 * K + 2 by ring, hpowcancel]
    ring
  have t1 : (Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 3 * pairDir' ℓ G
      ≤ Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairDir' ℓ G := by
    rw [hε2eq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowK (sq_nonneg Cg)) (by positivity)) hPnn
  have t2 : 3 * ((4 * R)⁻¹ * chiGB) ^ 2
        * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5 * pairMass' ℓ G)
      ≤ 3 * (chiGB ^ 2 / 16) * (Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairMass' ℓ G) := by
    refine le_of_eq ?_
    rw [show 3 * ((4 * R)⁻¹ * chiGB) ^ 2
          * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5 * pairMass' ℓ G)
        = 3 * ((4 * R)⁻¹ * chiGB) ^ 2 * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5)
          * pairMass' ℓ G by ring, hscal]
    ring
  have hEeq' : pairEnergy ℓ G = pairDir ℓ G + pairMass ℓ G := hEeq
  have hconst : 2 * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 3 * pairDir' ℓ G
        + 3 * ((4 * R)⁻¹ * chiGB) ^ 2
          * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5 * pairMass' ℓ G))
      ≤ 2 * Cg ^ 2 * (1 + chiGB ^ 2) * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairEnergy ℓ G := by
    have hkey : pairDir' ℓ G + (3 * chiGB ^ 2 / 16) * pairMass' ℓ G
        ≤ (1 + chiGB ^ 2) * (pairDir' ℓ G + pairMass' ℓ G) := by
      nlinarith [hPnn, hQnn, sq_nonneg chiGB]
    have hmid : 2 * (Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairDir' ℓ G
          + 3 * (chiGB ^ 2 / 16) * (Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairMass' ℓ G))
        ≤ 2 * Cg ^ 2 * (1 + chiGB ^ 2) * (R / ℓ) ^ (2 * K) * ℓ ^ 3
            * (pairDir' ℓ G + pairMass' ℓ G) := by
      have hCnn : 0 ≤ Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3 := by positivity
      have h := mul_le_mul_of_nonneg_left hkey hCnn
      nlinarith [h]
    calc 2 * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 3 * pairDir' ℓ G
          + 3 * ((4 * R)⁻¹ * chiGB) ^ 2
            * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5 * pairMass' ℓ G))
        ≤ 2 * (Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairDir' ℓ G
            + 3 * (chiGB ^ 2 / 16) * (Cg ^ 2 * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairMass' ℓ G)) :=
          mul_le_mul_of_nonneg_left (add_le_add t1 t2) (by norm_num)
      _ ≤ 2 * Cg ^ 2 * (1 + chiGB ^ 2) * (R / ℓ) ^ (2 * K) * ℓ ^ 3
            * (pairDir' ℓ G + pairMass' ℓ G) := hmid
      _ = 2 * Cg ^ 2 * (1 + chiGB ^ 2) * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairEnergy ℓ G := by
          rw [hEeq', hDirEq, hMassEq]
  have hfinal : ∑ j : Fin 3, ∫ z, ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ 2 * Cg ^ 2 * (1 + chiGB ^ 2) * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairEnergy ℓ G := by
    calc ∑ j : Fin 3, ∫ z, ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        = ∑ j : Fin 3, ∫ z in Metric.closedBall (0 : E3) (2 * R),
            ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => hsupp j
      _ ≤ 2 * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 3 * pairDir' ℓ G
            + 3 * ((4 * R)⁻¹ * chiGB) ^ 2
              * ((Cg * (R / ℓ) ^ (K + 1)) ^ 2 * ℓ ^ 5 * pairMass' ℓ G)) := hstep
      _ ≤ 2 * Cg ^ 2 * (1 + chiGB ^ 2) * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairEnergy ℓ G := hconst
  -- (10) the `Ḣ⁻¹`–`Ḣ¹` duality
  have hSumnn : 0 ≤ ∑ j : Fin 3, ∫ z, ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun z => by positivity
  have hJnn : 0 ≤ ∫ p, Work.BoseBoxFock.coulInt W p := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [(MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure E3)) (ν := (volume : Measure E3))).ae hW0,
      (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure E3)) (ν := (volume : Measure E3))).ae hW0] with p h1 h2
    exact mul_nonneg (mul_nonneg h1 h2) (inv_nonneg.mpr (norm_nonneg _))
  have hEnn : 0 ≤ pairEnergy ℓ G := by rw [hEeq]; exact add_nonneg hDirnn hMassnn
  have hT3 := coulombDual (W := W) hWi hW0 hJ hΨcd hΨcs
  have hnorm : ‖∫ z, ((W z : ℝ) : ℂ) * Ψ z‖
      ≤ Real.sqrt (((4 * Real.pi)⁻¹ * ∫ p, Work.BoseBoxFock.coulInt W p)
          * (∑ j : Fin 3, ∫ z, ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) :=
    (Real.le_sqrt (norm_nonneg _) (mul_nonneg (mul_nonneg (by positivity) hJnn) hSumnn)).mpr hT3
  have hsplit_sqrt : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d →
      Real.sqrt (a * (b * (c * d))) = Real.sqrt (a * b) * Real.sqrt c * Real.sqrt d := by
    intro a b c d ha hb hc hd
    have h1 : a * (b * (c * d)) = (a * b) * (c * d) := by ring
    rw [h1, Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_mul hc]
    ring
  have hfin : ‖∫ z, ((W z : ℝ) : ℂ) * Ψ z‖
      ≤ Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))
          * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
          * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G) := by
    have hCnn : 0 ≤ 2 * Cg ^ 2 * (1 + chiGB ^ 2) := by positivity
    calc ‖∫ z, ((W z : ℝ) : ℂ) * Ψ z‖
        ≤ Real.sqrt (((4 * Real.pi)⁻¹ * ∫ p, Work.BoseBoxFock.coulInt W p)
            * (∑ j : Fin 3, ∫ z, ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) := hnorm
      _ ≤ Real.sqrt (((4 * Real.pi)⁻¹ * ∫ p, Work.BoseBoxFock.coulInt W p)
            * ((2 * Cg ^ 2 * (1 + chiGB ^ 2)) * ((R / ℓ) ^ (2 * K)
              * (ℓ ^ 3 * pairEnergy ℓ G)))) := by
          refine Real.sqrt_le_sqrt ?_
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hJnn)
          calc ∑ j : Fin 3, ∫ z, ‖fderiv ℝ Ψ z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
              ≤ 2 * Cg ^ 2 * (1 + chiGB ^ 2) * (R / ℓ) ^ (2 * K) * ℓ ^ 3 * pairEnergy ℓ G :=
                hfinal
            _ = 2 * Cg ^ 2 * (1 + chiGB ^ 2)
                  * ((R / ℓ) ^ (2 * K) * (ℓ ^ 3 * pairEnergy ℓ G)) := by ring
      _ = Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2))) * (R / ℓ) ^ K
            * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
            * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G) := by
          rw [hsplit_sqrt ((4 * Real.pi)⁻¹ * ∫ p, Work.BoseBoxFock.coulInt W p)
            (2 * Cg ^ 2 * (1 + chiGB ^ 2)) ((R / ℓ) ^ (2 * K)) (ℓ ^ 3 * pairEnergy ℓ G)
            (mul_nonneg (by positivity) hJnn) hCnn (pow_nonneg hRlnn (2 * K))
            (mul_nonneg (by positivity) hEnn)]
          rw [show (R / ℓ) ^ (2 * K) = ((R / ℓ) ^ K) ^ 2 by
                rw [show 2 * K = K * 2 by ring, ← pow_mul],
            Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hRlnn K)]
          rw [show (4 * Real.pi)⁻¹ * (∫ p, Work.BoseBoxFock.coulInt W p)
                * (2 * Cg ^ 2 * (1 + chiGB ^ 2))
              = (4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2))
                * (∫ p, Work.BoseBoxFock.coulInt W p) by ring,
            Real.sqrt_mul (by positivity : 0 ≤ (4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))]
          ring
  -- (11) back to the pairing
  calc ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * G w y‖
      = ‖∫ z, ((W z : ℝ) : ℂ) * Ψ z‖ := by rw [hpair, ← hθeq]
    _ ≤ Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))
          * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
          * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G) := hfin

/-! ## The theorem -/

theorem chiChiImages_pairing_coul (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ℓ R : ℝ}, 0 < ℓ → 0 < R → R ≤ ℓ / 4 →
    ∀ {W : EuclideanSpace ℝ (Fin 3) → ℝ}, MeasureTheory.Integrable W →
      (∀ᵐ x, 0 ≤ W x) → (∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0) →
      MeasureTheory.Integrable (Work.BoseBoxFock.coulInt W) →
    ∀ {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ},
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G) →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ C * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
          * Real.sqrt (ℓ ^ 3 * ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
              ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
                (∑ j : Fin 3, ‖fderiv ℝ (fun w' =>
                    ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ) * G w' y) w
                    (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
                  + (ℓ ^ 2)⁻¹ * ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * G w y‖ ^ 2)) := by
  obtain ⟨Cg, hCgnn, hCg⟩ := chiScale_le_of_gap (K + 1)
  refine ⟨26 * Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2))) + 1,
    by positivity, ?_⟩
  intro ℓ R hℓ hR hRℓ W hWi hW0 hWs hJ G hG
  obtain ⟨hEeq, hDirEq, hMassEq, hDirnn, hMassnn⟩ := pairEnergy_self hℓ hG
  have hsplit := chiChiImages_split (ℓ := ℓ) (R := R) hℓ hR hRℓ hWi hWs hG
  have hcard : ((Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)).erase 0).card = 26 :=
    by decide
  have hper : ∀ m ∈ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)).erase 0,
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
            * ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * G w y‖
        ≤ Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))
            * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
            * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G) := by
    intro m hm
    exact per_m_bound K hCgnn hCg hℓ hR hRℓ hWi hW0 hWs hJ hG (Finset.mem_erase.mp hm).1
  have hJnn : 0 ≤ ∫ p, Work.BoseBoxFock.coulInt W p := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [(MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure E3)) (ν := (volume : Measure E3))).ae hW0,
      (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure E3)) (ν := (volume : Measure E3))).ae hW0] with p h1 h2
    exact mul_nonneg (mul_nonneg h1 h2) (inv_nonneg.mpr (norm_nonneg _))
  have hEnn : 0 ≤ pairEnergy ℓ G := by rw [hEeq]; exact add_nonneg hDirnn hMassnn
  have hXnn : 0 ≤ (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
      * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G) := by positivity
  have hCstnn : 0 ≤ Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2))) :=
    Real.sqrt_nonneg _
  calc ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
      ≤ ∑ m ∈ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)).erase 0,
          ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
              ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                * ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * G w y‖ := hsplit
    _ ≤ ∑ m ∈ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)).erase 0,
          (Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))
            * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
            * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G)) := Finset.sum_le_sum hper
    _ = 26 * (Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))
            * ((R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
              * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring_nf
    _ ≤ (26 * Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2))) + 1)
          * ((R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
            * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G)) := by
        rw [show 26 * (Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2)))
              * ((R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
                * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G)))
            = (26 * Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2))))
              * ((R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
                * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G)) by ring]
        refine mul_le_mul_of_nonneg_right ?_ hXnn
        linarith [hCstnn]
    _ = (26 * Real.sqrt ((4 * Real.pi)⁻¹ * (2 * Cg ^ 2 * (1 + chiGB ^ 2))) + 1)
          * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
          * Real.sqrt (ℓ ^ 3 * pairEnergy ℓ G) := by ring

end Work.BoseBoxFock.L1Tails
