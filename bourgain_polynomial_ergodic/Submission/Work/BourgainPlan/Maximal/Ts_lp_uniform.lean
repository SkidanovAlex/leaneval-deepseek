import Mathlib
import Submission.Work.BourgainPlan.Maximal.DRDFDefs
import Submission.Work.BourgainPlan.Maximal.annulusProjectionDual
import Submission.Work.BourgainPlan.Maximal.annulusSquareLpVec
import Submission.Work.BourgainPlan.Maximal.annulusSquareLpUniform
import Submission.Work.BourgainPlan.Maximal.annulusDiffSqfunLq
import Submission.Commons.Analysis.Integral.continuous_integral_czE_smul
import Submission.Work.BourgainPlan.Maximal.ell2PolyDilationSupMaxLp
import Submission.Work.BourgainPlan.Maximal.annulusPartitionDefs
import Submission.Work.BourgainPlan.Maximal.hasSum_annAtomZ
import Submission.Work.BourgainPlan.Maximal.eLpNormPairingCriterion
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_leading
import Submission.Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
import Submission.Commons.Analysis.Fourier.integrable_fourierInv_of_contDiff_hasCompactSupport
import Submission.Commons.Analysis.Fourier.integrable_fourier_of_contDiff_hasCompactSupport
import Submission.Work.BourgainPlan.Maximal.convolutionLpLinear
import Submission.Work.BourgainPlan.Maximal.annulusKernel_size
import Submission.Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite

open MeasureTheory Filter
open scoped ENNReal BigOperators FourierTransform Topology

namespace Work.BourgainPlan.Maximal

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The dyadic Littlewood–Paley symbol family `ψ(2^m ·)` -/

/-- The complex lift of `ψ`. -/
noncomputable def psiLift : ℝ → ℂ := fun ξ => ((dyadPsi ξ : ℝ) : ℂ)

/-- The `m`-th dyadic Littlewood–Paley symbol as a complex-valued function: `ξ ↦ ψ (2^m ξ)`. -/
noncomputable def psiFam (m : ℤ) : ℝ → ℂ := fun ξ => ((dyadPsi ((2 : ℝ) ^ m * ξ) : ℝ) : ℂ)

/-- The wider bump family `ξ ↦ ψ̃ (2^m ξ)`. -/
noncomputable def tildeFam (m : ℤ) : ℝ → ℂ := fun ξ => ((dyadTilde ((2 : ℝ) ^ m * ξ) : ℝ) : ℂ)

/-- The annulus kernel of the `m`-th Littlewood–Paley symbol: `κ_m = 𝓕⁻ (ψ(2^m ·))`. -/
noncomputable def kappa (m : ℤ) : ℝ → ℂ := FourierTransformInv.fourierInv (psiFam m)

/-! ## Elementary properties of `ψ` -/

lemma dyadPsi_eq (ξ : ℝ) : dyadPsi ξ = dyadTheta ξ - dyadTheta (2 * ξ) := rfl

lemma dyadPsi_eq_zero_of_abs_le_half {ξ : ℝ} (h : |ξ| ≤ 2⁻¹) : dyadPsi ξ = 0 := by
  have h1 : dyadTheta ξ = 1 := dyadTheta_spec.2.2.1 ξ (by linarith)
  have h2 : dyadTheta (2 * ξ) = 1 := by
    refine dyadTheta_spec.2.2.1 _ ?_
    rw [abs_mul]
    norm_num
    linarith
  rw [dyadPsi_eq, h1, h2, sub_self]

lemma dyadPsi_eq_zero_of_two_le_abs {ξ : ℝ} (h : 2 ≤ |ξ|) : dyadPsi ξ = 0 := by
  have h1 : dyadTheta ξ = 0 := dyadTheta_spec.2.2.2.1 ξ h
  have h2 : dyadTheta (2 * ξ) = 0 := by
    refine dyadTheta_spec.2.2.2.1 _ ?_
    rw [abs_mul]
    norm_num
    linarith
  rw [dyadPsi_eq, h1, h2, sub_self]

/-- **Support of the symbol family.** -/
lemma psiFam_support {m : ℤ} {ξ : ℝ} (h : psiFam m ξ ≠ 0) :
    (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| < 2 := by
  have hψ : dyadPsi ((2 : ℝ) ^ m * ξ) ≠ 0 := fun h0 => h (by simp [psiFam, h0])
  constructor
  · by_contra hcon
    push_neg at hcon
    exact hψ (dyadPsi_eq_zero_of_abs_le_half hcon)
  · by_contra hcon
    push_neg at hcon
    exact hψ (dyadPsi_eq_zero_of_two_le_abs hcon)

lemma psiFam_annulusSupp : AnnulusSupp psiFam := fun _ _ h => psiFam_support h

/-- `ψ̃ (2^m ξ) = 1` whenever `ψ(2^m ξ) ≠ 0`. -/
lemma tildeFam_eq_one_of_psiFam_ne_zero {m : ℤ} {ξ : ℝ} (h : psiFam m ξ ≠ 0) :
    tildeFam m ξ = 1 := by
  have hsupp := psiFam_support h
  have h3 : dyadTilde ((2 : ℝ) ^ m * ξ) = 1 := dyadTilde_one (le_of_lt hsupp.2)
  simp only [tildeFam, h3, Complex.ofReal_one]

/-! ## Smoothness and supports of the symbol family -/

lemma contDiff_dyadPsi : ContDiff ℝ (⊤ : ℕ∞) dyadPsi := by
  have hθ : ContDiff ℝ (⊤ : ℕ∞) dyadTheta := dyadTheta_spec.1
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (2 : ℝ) * ξ) := contDiff_const.mul contDiff_id
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => dyadTheta (2 * ξ)) := hθ.comp h2
  have heq : dyadPsi = fun ξ : ℝ => dyadTheta ξ - dyadTheta (2 * ξ) := by
    funext ξ; rw [dyadPsi_eq]
  rw [heq]; exact hθ.sub hcomp

lemma support_dyadPsi_subset : Function.support dyadPsi ⊆ Set.Icc (-2 : ℝ) 2 := by
  intro x hx
  have hne : dyadPsi x ≠ 0 := hx
  have h1 : 2⁻¹ < |x| := by
    by_contra hcon
    push_neg at hcon
    exact hne (dyadPsi_eq_zero_of_abs_le_half hcon)
  have h2 : |x| < 2 := by
    by_contra hcon
    push_neg at hcon
    exact hne (dyadPsi_eq_zero_of_two_le_abs hcon)
  rw [Set.mem_Icc]
  exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

lemma hasCompactSupport_dyadPsi : HasCompactSupport dyadPsi :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc support_dyadPsi_subset

lemma contDiff_psiLift : ContDiff ℝ (⊤ : ℕ∞) psiLift :=
  Complex.ofRealCLM.contDiff.comp contDiff_dyadPsi

lemma hasCompactSupport_psiLift : HasCompactSupport psiLift :=
  hasCompactSupport_dyadPsi.comp_left (by simp)

lemma contDiff_psiFam (m : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (psiFam m) := by
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => psiLift ((2 : ℝ) ^ m * ξ)) :=
    contDiff_psiLift.comp (contDiff_const.mul contDiff_id)
  have heq : psiFam m = fun ξ : ℝ => psiLift ((2 : ℝ) ^ m * ξ) := by
    funext ξ; simp [psiFam, psiLift]
  rw [heq]; exact h2

lemma hasCompactSupport_psiFam (m : ℤ) : HasCompactSupport (psiFam m) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-((2 : ℝ) ^ (1 - m))) ((2 : ℝ) ^ (1 - m))) isCompact_Icc ?_
  intro ξ hξ
  have h2 : |(2 : ℝ) ^ m * ξ| < 2 := (psiFam_support hξ).2
  have hA : |(2 : ℝ) ^ m * ξ| = (2 : ℝ) ^ m * |ξ| := by
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num) m)]
  have h4 : |ξ| = (2 : ℝ) ^ (-m) * ((2 : ℝ) ^ m * |ξ|) := by
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero,
      one_mul]
  have h3 : |ξ| < (2 : ℝ) ^ (1 - m) := by
    rw [h4]
    calc (2 : ℝ) ^ (-m) * ((2 : ℝ) ^ m * |ξ|) < (2 : ℝ) ^ (-m) * 2 :=
          mul_lt_mul_of_pos_left (hA ▸ h2) (zpow_pos (by norm_num) (-m))
      _ = (2 : ℝ) ^ (1 - m) := by
          have h1 : (2 : ℝ) ^ (-m) * 2 = (2 : ℝ) ^ (-m) * (2 : ℝ) ^ (1 : ℤ) := by rw [zpow_one]
          rw [h1, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1
          ring
  rw [Set.mem_Icc]
  exact ⟨le_of_lt (abs_lt.mp h3).1, le_of_lt (abs_lt.mp h3).2⟩

/-! ## Bounds on the iterated derivatives -/

lemma deriv_eq_zero_of_eq_zero_on_open {g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ∀ x ∈ U, g x = 0) : ∀ x ∈ U, deriv g x = 0 := by
  intro x hx
  have hmem : U ∈ 𝓝 x := hU.mem_nhds hx
  have hev : g =ᶠ[𝓝 x] (0 : ℝ → ℂ) :=
    Filter.eventually_of_mem hmem (fun y hy => by simpa using hg y hy)
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

lemma iteratedDeriv_eq_zero_of_eq_zero_on_open {g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ∀ x ∈ U, g x = 0) : ∀ k : ℕ, ∀ x ∈ U, iteratedDeriv k g x = 0 := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hg x hx
  | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      exact deriv_eq_zero_of_eq_zero_on_open hU ih x hx

/-- A `C^∞` function vanishing outside a compact set has bounded iterated derivatives. -/
lemma exists_bound_iteratedDeriv_of_support_subset {K : Set ℝ} (hK : IsCompact K) {g : ℝ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsub : Function.support g ⊆ K) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedDeriv k g x‖ ≤ B := by
  have hcont : Continuous (iteratedDeriv k g) :=
    hg.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn hK hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact le_trans (hB x hx) (le_max_left _ _)
  · have htsub : tsupport g ⊆ K := closure_minimal hsub hK.isClosed
    have hz : iteratedDeriv k g x = 0 :=
      iteratedDeriv_eq_zero_of_eq_zero_on_open hK.isClosed.isOpen_compl
        (fun y hy => image_eq_zero_of_notMem_tsupport (fun hy' => hy (htsub hy'))) k x hx
    rw [hz, norm_zero]; exact le_max_right _ _

lemma support_psiLift_subset : Function.support psiLift ⊆ Set.Icc (-2 : ℝ) 2 := fun _ hx =>
  support_dyadPsi_subset (by
    intro h0
    exact hx (by simp [psiLift, h0]))

lemma exists_bound_iteratedDeriv_psiLift (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ‖iteratedDeriv k psiLift y‖ ≤ B :=
  exists_bound_iteratedDeriv_of_support_subset isCompact_Icc contDiff_psiLift
    support_psiLift_subset k

/-- **The Mikhlin data of the family `ψ(2^m ·)`.** -/
lemma annulusSymbolSmooth_psiFam : AnnulusSymbolSmooth psiFam := by
  refine ⟨fun m ξ h => psiFam_support h, fun k => ?_⟩
  obtain ⟨B, hB0, hB⟩ := exists_bound_iteratedDeriv_psiLift k
  refine ⟨B, hB0, fun m ξ => ?_⟩
  have hcomp : ContDiff ℝ (↑k) psiLift :=
    contDiff_psiLift.of_le (WithTop.coe_le_coe.mpr le_top)
  have hkey : iteratedDeriv k (fun ξ : ℝ => psiLift ((2 : ℝ) ^ m * ξ)) ξ
      = ((2 : ℝ) ^ m) ^ k • iteratedDeriv k psiLift ((2 : ℝ) ^ m * ξ) :=
    congrFun (iteratedDeriv_comp_const_smul (f := psiLift) hcomp ((2 : ℝ) ^ m)) ξ
  have heq : psiFam m = fun ξ : ℝ => psiLift ((2 : ℝ) ^ m * ξ) := by
    funext y; simp [psiFam, psiLift]
  rw [heq, hkey, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ m) ^ k)]
  have hpow : (((2 : ℝ) ^ m) ^ k) = (2 : ℝ) ^ (m * (k : ℤ)) := by
    rw [zpow_mul, zpow_natCast]
  rw [hpow]
  calc (2 : ℝ) ^ (m * (k : ℤ)) * ‖iteratedDeriv k psiLift ((2 : ℝ) ^ m * ξ)‖
      ≤ (2 : ℝ) ^ (m * (k : ℤ)) * B := mul_le_mul_of_nonneg_left (hB _) (by positivity)
    _ = B * (2 : ℝ) ^ (m * (k : ℤ)) := by ring



/-! ## Integrability of symbols and kernels -/

lemma integrable_psiFam (m : ℤ) : Integrable (psiFam m) volume :=
  (contDiff_psiFam m).continuous.integrable_of_hasCompactSupport (hasCompactSupport_psiFam m)

lemma integrable_kappa (m : ℤ) : Integrable (kappa m) volume :=
  Commons.Analysis.Fourier.integrable_fourierInv_of_contDiff_hasCompactSupport
    (hasCompactSupport_psiFam m) (contDiff_psiFam m)

/-! ## The projection as a convolution, and the absorption of the wider bump -/

/-- `𝓕 κ_m = ψ(2^m ·)`. -/
lemma fourier_kappa (m : ℤ) : FourierTransform.fourier (kappa m) = psiFam m := by
  have h1 : Integrable (FourierTransform.fourier (psiFam m)) volume :=
    Commons.Analysis.Fourier.integrable_fourier_of_contDiff_hasCompactSupport
      (hasCompactSupport_psiFam m) (contDiff_psiFam m)
  have h2 := Continuous.fourier_fourierInv_eq (f := psiFam m) (contDiff_psiFam m).continuous
    (integrable_psiFam m) h1
  simpa [kappa] using h2

/-- `ψ̃_m · ψ_m = ψ_m` pointwise. -/
lemma tildeFam_mul_psiFam (m : ℤ) (ξ : ℝ) : tildeFam m ξ * psiFam m ξ = psiFam m ξ := by
  by_cases h : psiFam m ξ = 0
  · rw [h, mul_zero]
  · rw [tildeFam_eq_one_of_psiFam_ne_zero h, one_mul]

/-- The projection of an `L¹` function is the convolution with `κ_m`. -/
lemma dyadicProj_eq_convolution {m : ℤ} {G : ℝ → ℂ} (hG : Integrable G) (x : ℝ) :
    dyadicProj dyadPsi m G x = ∫ y, G y * kappa m (x - y) := by
  have h := Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
    (m := psiFam m) (f := G) (integrable_psiFam m) hG x
  simpa [dyadicProj, kappa, psiFam] using h

/-- The projection vanishes when the input is not integrable. -/
lemma dyadicProj_eq_zero_of_not_integrable {ψ : ℝ → ℝ} {m : ℤ} {G : ℝ → ℂ}
    (hG : ¬ Integrable G) : dyadicProj ψ m G = 0 := by
  have hf : FourierTransform.fourier G = 0 :=
    Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable hG
  funext x
  simp only [dyadicProj, hf, Pi.zero_apply, mul_zero]
  rw [Real.fourierInv_eq']
  simp

/-- The symbol `ψ_m · 𝓕G` is integrable for `G ∈ L¹`. -/
lemma integrable_psiFam_mul_fourier {m : ℤ} {G : ℝ → ℂ} (hG : Integrable G) :
    Integrable (fun ξ => psiFam m ξ * FourierTransform.fourier G ξ) :=
  (contDiff_psiFam m).continuous.mul
    (Commons.Analysis.Fourier.continuous_fourier_of_integrable G hG) |>.integrable_of_hasCompactSupport
    ((hasCompactSupport_psiFam m).mul_right)

/-- The projection of an `L¹` function is continuous. -/
lemma continuous_dyadicProj {m : ℤ} {G : ℝ → ℂ} (hG : Integrable G) :
    Continuous (dyadicProj dyadPsi m G) :=
  Commons.Analysis.Fourier.continuous_fourierInv_of_integrable _
    (integrable_psiFam_mul_fourier hG)

/-- The projection of an `L¹` function is integrable (Young's inequality). -/
lemma integrable_dyadicProj {m : ℤ} {G : ℝ → ℂ} (hG : Integrable G) :
    Integrable (dyadicProj dyadPsi m G) := by
  have hK : MemLp (kappa m) 1 volume := memLp_one_iff_integrable.mpr (integrable_kappa m)
  have hG1 : MemLp G (ENNReal.ofReal 1) volume := by
    rw [ENNReal.ofReal_one]; exact memLp_one_iff_integrable.mpr hG
  have hbound :=
    Commons.Analysis.Convolution.eLpNorm_convolution_le_complex (kappa m) G 1 le_rfl hK hG1
  have hfin : eLpNorm (fun x : ℝ => ∫ y, kappa m (x - y) * G y) (ENNReal.ofReal 1) volume < ⊤ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top hK.eLpNorm_lt_top hG1.eLpNorm_lt_top)
  have hmem : MemLp (fun x : ℝ => ∫ y, kappa m (x - y) * G y) (ENNReal.ofReal 1) volume :=
    hfin
  rw [ENNReal.ofReal_one] at hmem
  refine Integrable.congr (memLp_one_iff_integrable.mp hmem) ?_
  filter_upwards with x
  rw [dyadicProj_eq_convolution hG]
  refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
  ring


/-- **The Fourier transform of the littlewood–Paley projection** (for `L¹` input). -/
lemma fourier_dyadicProj {m : ℤ} {G : ℝ → ℂ} (hG : Integrable G) :
    FourierTransform.fourier (dyadicProj dyadPsi m G)
      = fun ξ => psiFam m ξ * FourierTransform.fourier G ξ := by
  have hconv : dyadicProj dyadPsi m G
      = MeasureTheory.convolution G (kappa m) (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x
    rw [dyadicProj_eq_convolution hG, MeasureTheory.convolution_def]
    rfl
  rw [hconv]
  funext ξ
  rw [Real.fourier_mul_convolution_eq hG (integrable_kappa m) ξ, fourier_kappa, mul_comm]

/-- **Absorption of the wider bump.**  For `G ∈ L¹`, the wider projection does nothing to the
projection of `G`. -/
lemma dyadicProj_tilde_absorption {m : ℤ} {G : ℝ → ℂ} (hG : Integrable G) (c : ℂ) :
    (fun x => dyadicProj dyadTilde m (fun y => c * dyadicProj dyadPsi m G y) x)
      =ᵐ[volume] fun y => c * dyadicProj dyadPsi m G y := by
  set w : ℝ → ℂ := dyadicProj dyadPsi m G with hwdef
  have hwint : Integrable w := integrable_dyadicProj hG
  have hcontw : Continuous w := continuous_dyadicProj hG
  have hFw : FourierTransform.fourier w
      = fun ξ => psiFam m ξ * FourierTransform.fourier G ξ := fourier_dyadicProj hG
  have hcw : Integrable (fun y => c * w y) := hwint.const_mul c
  have hFcw : FourierTransform.fourier (fun y => c * w y)
      = fun ξ => c * (psiFam m ξ * FourierTransform.fourier G ξ) := by
    funext ξ
    rw [fourier_const_mul, hFw]
  have hFcwint : Integrable (FourierTransform.fourier (fun y => c * w y)) := by
    rw [hFcw]
    exact (integrable_psiFam_mul_fourier hG).const_mul c
  have hsym : (fun ξ => tildeFam m ξ * FourierTransform.fourier (fun y => c * w y) ξ)
      = FourierTransform.fourier (fun y => c * w y) := by
    funext ξ
    rw [hFcw]
    have h1 : tildeFam m ξ * (c * (psiFam m ξ * FourierTransform.fourier G ξ))
        = c * (tildeFam m ξ * psiFam m ξ) * FourierTransform.fourier G ξ := by ring
    rw [h1, tildeFam_mul_psiFam m ξ]
    ring
  have hproj : (fun x => dyadicProj dyadTilde m (fun y => c * w y) x)
      = FourierTransformInv.fourierInv (FourierTransform.fourier (fun y => c * w y)) := by
    have h1 : (fun x => dyadicProj dyadTilde m (fun y => c * w y) x)
        = fun x => FourierTransformInv.fourierInv
            (fun ξ => tildeFam m ξ * FourierTransform.fourier (fun y => c * w y) ξ) x := by
      funext x
      rfl
    rw [h1, hsym]
  rw [hproj]
  exact Filter.EventuallyEq.of_eq
    (Continuous.fourierInv_fourier_eq (hcontw.const_mul c) hcw hFcwint)


/-! ## The dyadic annulus partition on the Littlewood–Paley bands -/

/-- The three atom scales that cover the `ψ`-band at scale `l`. -/
def atomScales (l : ℤ) : Finset ℤ := {l - 1, l, l + 1}

lemma mem_atomScales_iff {l m : ℤ} : m ∈ atomScales l ↔ m = l - 1 ∨ m = l ∨ m = l + 1 := by
  simp only [atomScales, Finset.mem_insert, Finset.mem_singleton]

/-- **The annuli determines the scale up to `1`.** -/
lemma mem_atomScales_of_mem_annuli {l m : ℤ} {ξ : ℝ}
    (hl1 : (2 : ℝ)⁻¹ < |(2 : ℝ) ^ l * ξ|) (hl2 : |(2 : ℝ) ^ l * ξ| < 2)
    (hm1 : (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ|) (hm2 : |(2 : ℝ) ^ m * ξ| < 2) :
    m ∈ atomScales l := by
  rw [mem_atomScales_iff]
  set c : ℝ := (2 : ℝ) ^ (l - m) with hc
  have hcpos : 0 < c := zpow_pos (by norm_num) _
  have hbpos : 0 < |(2 : ℝ) ^ m * ξ| := lt_trans (by norm_num) hm1
  have hrel : |(2 : ℝ) ^ l * ξ| = c * |(2 : ℝ) ^ m * ξ| := by
    rw [hc, abs_mul, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) l),
      abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) m), ← mul_assoc,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring_nf
  have hlt : c < 4 := by
    have h := hl2
    rw [hrel] at h
    calc c = (c * |(2 : ℝ) ^ m * ξ|) / |(2 : ℝ) ^ m * ξ| :=
          (mul_div_cancel_right₀ _ (ne_of_gt hbpos)).symm
      _ < 2 / |(2 : ℝ) ^ m * ξ| := div_lt_div_of_pos_right h hbpos
      _ < 2 / (2 : ℝ)⁻¹ := div_lt_div_of_pos_left (by norm_num) (by norm_num) hm1
      _ = 4 := by norm_num
  have hgt : (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ < c := by
    have h := hl1
    rw [hrel] at h
    calc (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ < (2 : ℝ)⁻¹ / |(2 : ℝ) ^ m * ξ| := by
          rw [lt_div_iff₀ hbpos]
          nlinarith [hm2, hbpos]
      _ < (c * |(2 : ℝ) ^ m * ξ|) / |(2 : ℝ) ^ m * ξ| :=
          (div_lt_div_iff_of_pos_right hbpos).mpr h
      _ = c := mul_div_cancel_right₀ _ (ne_of_gt hbpos)
  have hlt' : l - m < 2 := by
    have h4 : (2 : ℝ) ^ (l - m) < (2 : ℝ) ^ (2 : ℤ) := by
      rw [show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_num]
      exact hlt
    exact (zpow_lt_zpow_iff_right₀ (show (1:ℝ) < 2 by norm_num)).mp h4
  have hgt' : -2 < l - m := by
    have h2 : (2 : ℝ) ^ (-2 : ℤ) < (2 : ℝ) ^ (l - m) := by
      have hone : (2 : ℝ) ^ (-2 : ℤ) = (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by
        rw [zpow_neg, zpow_ofNat]
        norm_num
      rw [hone]; exact hgt
    exact (zpow_lt_zpow_iff_right₀ (show (1:ℝ) < 2 by norm_num)).mp h2
  omega

/-- **The atom partition on the `ψ`-band.** -/

lemma atomScales_sum_eq_one {l : ℤ} {ξ : ℝ} (hψ : dyadPsi ((2 : ℝ) ^ l * ξ) ≠ 0) :
    ∑ m ∈ atomScales l, annAtomC m ξ = 1 := by
  have hξne : ξ ≠ 0 := by
    intro h0
    refine hψ ?_
    rw [h0, mul_zero]
    exact dyadPsi_eq_zero_of_abs_le_half (by norm_num)
  have hband := psiFam_support (m := l) (show psiFam l ξ ≠ 0 by simpa [psiFam] using hψ)
  have hzero : ∀ m ∉ atomScales l, annAtomZ m ξ = 0 := by
    intro m hm
    by_contra hne
    exact hm (mem_atomScales_of_mem_annuli hband.1 hband.2
      (annAtomZ_support hne).1 (annAtomZ_support hne).2)
  have hsum : (∑' m : ℤ, annAtomZ m ξ) = ∑ m ∈ atomScales l, annAtomZ m ξ :=
    tsum_eq_sum hzero
  have hone : (∑ m ∈ atomScales l, annAtomZ m ξ) = 1 := by
    rw [← hsum]
    exact (hasSum_annAtomZ ξ hξne).tsum_eq
  have : (∑ m ∈ atomScales l, annAtomC m ξ) = ((∑ m ∈ atomScales l, annAtomZ m ξ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun m _ => annAtomC_apply m ξ)
  rw [this, hone, Complex.ofReal_one]


/-- **Linearity of the atom projection in the function variable.** -/
lemma annulusConv_fun_sum_eq (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (b m)) {ι : Type*} {p : ℝ} (hp : 1 ≤ p)
    (F : Finset ι) (m : ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ F, MemLp (f i) (ENNReal.ofReal p) volume) (x : ℝ) :
    annulusConv b m (fun y => ∑ i ∈ F, f i y) x = ∑ i ∈ F, annulusConv b m (f i) x := by
  simp only [annulusConv]
  rw [show (fun y : ℝ => annulusK b m (x - y) * ∑ i ∈ F, f i y)
      = fun y : ℝ => ∑ i ∈ F, annulusK b m (x - y) * f i y by
    funext y
    rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum]
  intro i hi
  exact integrable_annulusK_mul b hb hsmooth m hp (hf i hi) x

/-- **The atom recombination on a Littlewood–Paley band.**  If the Fourier transform of `g` is
supported in the `ψ`-band at scale `l`, then `g` is the sum of its three atom projections. -/
lemma eq_sum_annulusConv_of_fourier_support {l : ℤ} {g : ℝ → ℂ}
    (hgcont : Continuous g) (hgint : Integrable g) (hFg : Integrable (FourierTransform.fourier g))
    (hsupp : ∀ ξ, FourierTransform.fourier g ξ ≠ 0 → dyadPsi ((2 : ℝ) ^ l * ξ) ≠ 0) (x : ℝ) :
    g x = ∑ m ∈ atomScales l, annulusConv annAtomC m g x := by
  have hinv : (FourierTransformInv.fourierInv (FourierTransform.fourier g)) = g :=
    Continuous.fourierInv_fourier_eq hgcont hgint hFg
  have hsym : FourierTransform.fourier g
      = fun ξ => (∑ m ∈ atomScales l, annAtomC m ξ) * FourierTransform.fourier g ξ := by
    funext ξ
    by_cases h : FourierTransform.fourier g ξ = 0
    · rw [h, mul_zero]
    · rw [atomScales_sum_eq_one (hsupp ξ h), one_mul]
  have hint : ∀ m ∈ atomScales l, Integrable (fun ξ : ℝ =>
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) •
        (annAtomC m ξ * FourierTransform.fourier g ξ)) := by
    intro m _
    refine Integrable.mono' (g := fun ξ : ℝ => ‖annAtomC m ξ * FourierTransform.fourier g ξ‖)
      (Work.BourgainPlan.Maximal.integrable_annAtomC_mul_fourier m hgint).norm ?_ ?_
    · have hc : Continuous (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) *
          (annAtomC m ξ * FourierTransform.fourier g ξ)) :=
        (Complex.continuous_exp.comp (by fun_prop)).mul
          ((contDiff_annAtomC m).continuous.mul
            (Commons.Analysis.Fourier.continuous_fourier_of_integrable g hgint))
      simpa only [smul_eq_mul] using hc.aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hlin : FourierTransformInv.fourierInv
        (fun ξ => (∑ m ∈ atomScales l, annAtomC m ξ) * FourierTransform.fourier g ξ) x
      = ∑ m ∈ atomScales l,
          FourierTransformInv.fourierInv (fun ξ => annAtomC m ξ * FourierTransform.fourier g ξ) x := by
    rw [Real.fourierInv_eq']
    rw [show (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) •
          ((∑ m ∈ atomScales l, annAtomC m ξ) * FourierTransform.fourier g ξ))
        = fun ξ : ℝ => ∑ m ∈ atomScales l,
            Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) •
              (annAtomC m ξ * FourierTransform.fourier g ξ) from by
      funext ξ
      rw [Finset.sum_mul, Finset.smul_sum]]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Real.fourierInv_eq']
    · intro m hm
      exact hint m hm
  have hstep : FourierTransformInv.fourierInv (FourierTransform.fourier g) x
      = ∑ m ∈ atomScales l, annulusConv annAtomC m g x := by
    rw [hsym, hlin]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
      (Work.BourgainPlan.Maximal.integrable_annAtomC m) hgint x]
    rw [annulusConv, annulusK]
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    ring
  rw [← hstep]
  exact (congrFun hinv x).symm


/-- The three-term form of `atomScales`. -/
lemma sum_atomScales_eq (l : ℤ) (f : ℤ → ℂ) :
    ∑ m ∈ atomScales l, f m = f (l - 1) + f l + f (l + 1) := by
  have h1 : (l - 1 : ℤ) ∉ ({l, l + 1} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> omega
  have h2 : (l : ℤ) ∉ ({l + 1} : Finset ℤ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [atomScales, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  ring

/-- **The dual Littlewood–Paley estimate, reindexed along an arithmetic progression.** -/
lemma annulusProjectionDual_reindex (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℤ) (K : ℕ) (j : ℤ) (u : ℕ → ℝ → ℂ),
      (∀ k < K, MemLp (u k) (ENNReal.ofReal p) volume) →
      ∫⁻ x, ‖∑ k ∈ Finset.range K,
          annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + j) (u k) x‖ₑ ^ p
        ≤ ENNReal.ofReal (C ^ p)
          * ∫⁻ x, (∑ k ∈ Finset.range K, ‖u k x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
  obtain ⟨C₁, hC₁, hdual⟩ := annulusProjectionDual p hp
  refine ⟨C₁, hC₁, fun d hd s K j u hu => ?_⟩
  set φ : ℕ → ℤ := fun k => s + (d : ℤ) * (k : ℤ) + j with hφ
  have hinj : ∀ k k' : ℕ, k < K → k' < K → φ k = φ k' → k = k' := by
    intro k k' hk hk' heq
    rw [hφ] at heq
    have h1 : (d : ℤ) * (k : ℤ) = (d : ℤ) * (k' : ℤ) := by linarith
    have hpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have h2 : (k : ℤ) = (k' : ℤ) := mul_left_cancel₀ (ne_of_gt hpos) h1
    exact_mod_cast h2
  set G : ℤ → ℝ → ℂ := fun n =>
    if h : ∃ k ∈ Finset.range K, φ k = n then u (Classical.choose h) else 0 with hG
  have hGφ : ∀ k < K, G (φ k) = u k := by
    intro k hk
    have h : ∃ k' ∈ Finset.range K, φ k' = φ k := ⟨k, Finset.mem_range.mpr hk, rfl⟩
    rw [hG]
    simp only
    rw [dif_pos h]
    congr 1
    exact hinj (Classical.choose h) k (Finset.mem_range.mp (Classical.choose_spec h).1) hk
      (Classical.choose_spec h).2
  have hmem : ∀ n ∈ (Finset.range K).image φ, MemLp (G n) (ENNReal.ofReal p) volume := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    rw [hGφ k (Finset.mem_range.mp hk)]
    exact hu k (Finset.mem_range.mp hk)
  have hkey := hdual 0 ((Finset.range K).image φ) G hmem
  have hL : ∀ x : ℝ, (∑ n ∈ (Finset.range K).image φ,
        annulusConv annAtomC (0 + n) (G n) x)
      = ∑ k ∈ Finset.range K, annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + j) (u k) x := by
    intro x
    rw [Finset.sum_image (fun k hk k' hk' heq =>
      hinj k k' (Finset.mem_range.mp hk) (Finset.mem_range.mp hk') heq)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hGφ k (Finset.mem_range.mp hk), hφ]
    ring_nf
  have hR : ∀ x : ℝ, (∑ n ∈ (Finset.range K).image φ, ‖G n x‖ₑ ^ (2 : ℝ))
      = ∑ k ∈ Finset.range K, ‖u k x‖ₑ ^ (2 : ℝ) := by
    intro x
    rw [Finset.sum_image (fun k hk k' hk' heq =>
      hinj k k' (Finset.mem_range.mp hk) (Finset.mem_range.mp hk') heq)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hGφ k (Finset.mem_range.mp hk)]
  calc ∫⁻ x, ‖∑ k ∈ Finset.range K,
          annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + j) (u k) x‖ₑ ^ p
      = ∫⁻ x, ‖∑ n ∈ (Finset.range K).image φ,
          annulusConv annAtomC (0 + n) (G n) x‖ₑ ^ p := by
        refine lintegral_congr (fun x => ?_)
        rw [← hL x]
    _ ≤ ENNReal.ofReal (C₁ ^ p)
          * ∫⁻ x, (∑ n ∈ (Finset.range K).image φ, ‖G n x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := hkey
    _ = ENNReal.ofReal (C₁ ^ p)
          * ∫⁻ x, (∑ k ∈ Finset.range K, ‖u k x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
        congr 1
        refine lintegral_congr (fun x => ?_)
        rw [hR x]


/-! ## The vector-valued maximal bound for the curve-average differences -/

lemma enorm_ofReal_eq_cplx (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  norm_num

/-- **The curve average is dominated by the sup of the curve averages** (a tautological pointwise
form, used to feed `ell2PolyDilationSupMaxLp`). -/
lemma enorm_curveSigma_le_sup (P : Polynomial ℤ) (N : ℕ) {g : ℝ → ℂ} (x : ℝ) :
    ‖curveSigma P N g x‖ₑ ≤ ⨆ M : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
      ‖g (x - (P.map (Int.castRingHom ℝ)).eval ((M : ℝ) * s))‖ₑ := by
  have h1 : ‖curveSigma P N g x‖ ≤ (∫⁻ s in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal ‖g (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖).toReal := by
    rw [curveSigma, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact MeasureTheory.norm_integral_le_lintegral_norm
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (fun s : ℝ => g (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s)))
  rw [enorm_ofReal_eq_cplx]
  refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
  refine le_trans ENNReal.ofReal_toReal_le ?_
  refine le_trans (le_of_eq (lintegral_congr (fun s => (enorm_ofReal_eq_cplx _).symm))) ?_
  exact le_iSup (fun M : ℕ => ∫⁻ s in Set.Ioc (0 : ℝ) 1,
    ‖g (x - (P.map (Int.castRingHom ℝ)).eval ((M : ℝ) * s))‖ₑ) N

/-- From an `∫⁻ (·)^p` bound for `ℝ≥0∞`-valued functions to the `eLpNorm` bound. -/
lemma eLpNorm_le_of_lintegral_rpow_le_eNN' {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    {G H : ℝ → ℝ≥0∞} (h : ∫⁻ x, G x ^ p ≤ ENNReal.ofReal C * ∫⁻ x, H x ^ p)
    (hG : AEMeasurable G volume) (hH : AEMeasurable H volume) :
    eLpNorm G (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal (C ^ (1 / p)) * eLpNorm H (ENNReal.ofReal p) (volume : Measure ℝ) := by
  rw [← eLpNorm_rpow_self hp (g := G) hG, ← eLpNorm_rpow_self hp (g := H) hH] at h
  have hCeq : (ENNReal.ofReal (C ^ (1 / p))) ^ p = ENNReal.ofReal C := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC _) hp.le, ← Real.rpow_mul hC,
      one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  rw [← hCeq, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le] at h
  exact (ENNReal.rpow_le_rpow_iff hp).mp h

/-- Reindexing `Σ_{k < K}` as `Σ_{t : Fin K}`. -/
lemma sum_range_enorm_sq_eq_sum_fin {K : ℕ} (F : ℕ → ℝ → ℂ) (x : ℝ) :
    (∑ k ∈ Finset.range K, ‖F k x‖ₑ ^ (2 : ℝ)) = ∑ t : Fin K, ‖F t.1 x‖ₑ ^ (2 : ℝ) :=
  (Fin.sum_univ_eq_sum_range (fun k => ‖F k x‖ₑ ^ (2 : ℝ)) K).symm

/-- **The vector-valued maximal inequality for the dyadic curve-average differences** (the
`Fin K`-indexed form). -/
theorem dyadD_vec_eLpNorm_fin (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff)
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (g : Fin K → ℝ → ℂ),
      (∀ k, Measurable (g k)) →
      (∀ k, MemLp (g k) (ENNReal.ofReal p) volume) →
      eLpNorm (fun x => (∑ k : Fin K, ‖dyadD P k.1 (g k) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal C
        * eLpNorm (fun x => (∑ k : Fin K, ‖g k x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
          (ENNReal.ofReal p) volume := by
  obtain ⟨m, hm⟩ := poly_leading_shift_nonneg P hlc
  have hQ : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval x := by
    intro x hx
    rw [poly_eval_map_add_C]
    exact hm x hx
  have hp1 : (1 : ℝ) < p := lt_of_lt_of_le one_lt_two hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  obtain ⟨C₁, hC₁, hmain⟩ := ell2PolyDilationSupMaxLp (P + Polynomial.C m) hQ (p := p) hp1
  refine ⟨2 * C₁, by positivity, fun K g hgm hgmem => ?_⟩
  set f : Fin K → ℝ → ℝ := fun t y => ‖g t (y + (m : ℝ))‖ with hfdef
  have hfmeas : ∀ t, Measurable (f t) := fun t =>
    (hgm t).norm.comp (measurable_id.add measurable_const)
  have hmain' := hmain K f hfmeas
  have hf_enorm : ∀ (t : Fin K) (y : ℝ), ‖f t y‖ₑ = ‖g t (y + (m : ℝ))‖ₑ := by
    intro t y
    rw [hfdef]
    simp only
    exact (Real.enorm_eq_ofReal (norm_nonneg _)).trans (enorm_ofReal_eq_cplx _).symm
  -- pointwise domination of one dyadic difference by the polynomial maximal function
  have hterm : ∀ (t : Fin K) (x : ℝ), ‖dyadD P t.1 (g t) x‖ₑ
      ≤ 2 * (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) := by
    intro t x
    have h1 := enorm_curveSigma_le_sup P (2 ^ t.1) (g := g t) x
    have h2 := enorm_curveSigma_le_sup P (2 ^ (t.1 + 1)) (g := g t) x
    have h3 : ‖dyadD P t.1 (g t) x‖ₑ
        ≤ ‖curveSigma P (2 ^ t.1) (g t) x‖ₑ + ‖curveSigma P (2 ^ (t.1 + 1)) (g t) x‖ₑ := by
      rw [dyadD]
      calc ‖curveSigma P (2 ^ t.1) (g t) x - curveSigma P (2 ^ (t.1 + 1)) (g t) x‖ₑ
          = ‖curveSigma P (2 ^ t.1) (g t) x + (-(curveSigma P (2 ^ (t.1 + 1)) (g t) x))‖ₑ := by
            rw [sub_eq_add_neg]
        _ ≤ ‖curveSigma P (2 ^ t.1) (g t) x‖ₑ + ‖-(curveSigma P (2 ^ (t.1 + 1)) (g t) x)‖ₑ :=
            enorm_add_le _ _
        _ = ‖curveSigma P (2 ^ t.1) (g t) x‖ₑ + ‖curveSigma P (2 ^ (t.1 + 1)) (g t) x‖ₑ := by
            rw [enorm_neg]
    refine h3.trans ?_
    rw [two_mul]
    exact add_le_add h1 h2
  -- the sup-sum for `f` equals the sup-sum for `g`
  have hSUP : ∀ x : ℝ, (∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ‖f t (x - ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ)
          ^ (2 : ℝ))
      = ∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ) := by
    intro x
    refine Finset.sum_congr rfl (fun t _ => ?_)
    congr 1
    refine iSup_congr (fun N => ?_)
    refine lintegral_congr (fun s => ?_)
    rw [hf_enorm]
    congr 1
    rw [poly_eval_map_add_C]
    ring
  have hL : ∫⁻ x, (∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ‖f t (x - ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ)
          ^ (2 : ℝ)) ^ (p / 2)
      = ∫⁻ x, (∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2) :=
    lintegral_congr (fun x => by rw [hSUP x])
  have hR : ∫⁻ x, (ell2Sq f x) ^ (p / 2)
      = ∫⁻ x, (∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
    have h1 : (fun x : ℝ => (ell2Sq f x) ^ (p / 2))
        = fun x : ℝ => (∑ t : Fin K, ‖g t (x + (m : ℝ))‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
      funext x
      rw [ell2Sq]
      congr 1
      exact Finset.sum_congr rfl (fun t _ => by rw [hf_enorm t x])
    rw [h1]
    exact MeasureTheory.lintegral_add_right_eq_self
      (fun x : ℝ => (∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) (m : ℝ)
  have hmid : ∫⁻ x, (∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2)
      ≤ ENNReal.ofReal (C₁ ^ p) * ∫⁻ x, (∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
    calc ∫⁻ x, (∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2)
        = ∫⁻ x, (∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ‖f t (x - ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ)
              ^ (2 : ℝ)) ^ (p / 2) := hL.symm
      _ ≤ ENNReal.ofReal (C₁ ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p / 2) := hmain'
      _ = ENNReal.ofReal (C₁ ^ p) * ∫⁻ x, (∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
          rw [hR]
  have hsq : ∀ x : ℝ, (∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ))
      ≤ 4 * ∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ) := by
    intro x
    calc (∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ))
        ≤ ∑ t : Fin K, (2 * (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ)) ^ (2 : ℝ) :=
          Finset.sum_le_sum (fun t _ => ENNReal.rpow_le_rpow (hterm t x) (by norm_num))
      _ = 4 * ∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  have h4 : (4 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal (C₁ ^ p) = ENNReal.ofReal ((2 * C₁) ^ p) := by
    have h2 : (4 : ℝ≥0∞) ^ (p / 2) = ENNReal.ofReal ((2 : ℝ) ^ p) := by
      have hbase : (4 : ℝ≥0∞) ^ (p / 2) = (2 : ℝ≥0∞) ^ p := by
        rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 : ℕ) by norm_num,
          ← ENNReal.rpow_natCast (2 : ℝ≥0∞) 2, ← ENNReal.rpow_mul]
        congr 1
        push_cast
        ring
      rw [hbase, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0.le]
    rw [h2, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hC₁.le]
  have hfinal : ∫⁻ x, ((∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ p
      ≤ ENNReal.ofReal ((2 * C₁) ^ p)
        * ∫⁻ x, ((∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ p := by
    have hG : ∀ x : ℝ, ((∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ p
        = (∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
      intro x
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have hH : ∀ x : ℝ, ((∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ p
        = (∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
      intro x
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    calc ∫⁻ x, ((∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ p
        = ∫⁻ x, (∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2) :=
          lintegral_congr hG
      _ ≤ ∫⁻ x, (4 * ∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2) :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hsq x) (by positivity))
      _ = (4 : ℝ≥0∞) ^ (p / 2) * ∫⁻ x, (∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2) := by
          rw [show (fun x : ℝ => (4 * ∑ t : Fin K, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
                ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2))
              = fun x : ℝ => (4 : ℝ≥0∞) ^ (p / 2) * (∑ t : Fin K, (⨆ N : ℕ,
                ∫⁻ s in Set.Ioc (0 : ℝ) 1,
                ‖g t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2)
              from by funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]]
          rw [lintegral_const_mul' ((4 : ℝ≥0∞) ^ (p / 2)) _
            (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))]
      _ ≤ (4 : ℝ≥0∞) ^ (p / 2) * (ENNReal.ofReal (C₁ ^ p)
            * ∫⁻ x, (∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) :=
          mul_le_mul_of_nonneg_left hmid zero_le
      _ = ENNReal.ofReal ((2 * C₁) ^ p)
            * ∫⁻ x, ((∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ p := by
          rw [← lintegral_congr hH, ← mul_assoc, h4]
  have hcs : ∀ (t : Fin K) (n : ℕ), AEMeasurable (curveSigma P n (g t)) volume := by
    intro t n
    have hJ : StronglyMeasurable (fun z : ℝ × ℝ =>
        g t (z.1 - (toRealPoly P).eval ((n : ℝ) * z.2))) :=
      ((hgm t).comp (measurable_fst.sub ((toRealPoly P).continuous.measurable.comp
        (measurable_const.mul measurable_snd)))).stronglyMeasurable
    have hI := hJ.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
    refine hI.measurable.aemeasurable.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [curveSigma, intervalIntegral.integral_of_le zero_le_one]
  have hGm : AEMeasurable (fun x => (∑ t : Fin K, ‖dyadD P t.1 (g t) x‖ₑ ^ (2 : ℝ))
      ^ ((1 : ℝ) / 2)) volume :=
    (Finset.aemeasurable_fun_sum _ fun t _ =>
      (((hcs t _).sub (hcs t _)).enorm.pow_const _)).pow_const _
  have hHm : AEMeasurable (fun x => (∑ t : Fin K, ‖g t x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) volume :=
    (Finset.aemeasurable_fun_sum _ fun t _ => ((hgm t).aemeasurable.enorm.pow_const _)).pow_const _
  have hkey := eLpNorm_le_of_lintegral_rpow_le_eNN' hp0 (by positivity : (0 : ℝ) ≤ (2 * C₁) ^ p)
    hfinal hGm hHm
  have harith : ((2 * C₁) ^ p) ^ (1 / p) = 2 * C₁ := by
    rw [← Real.rpow_mul (by positivity), mul_one_div, div_self hp0.ne', Real.rpow_one]
  rw [harith] at hkey
  exact hkey

/-- **The vector-valued maximal inequality for the dyadic curve-average differences.**

For `2 ≤ p < ∞` there is `C > 0` such that for every `K`, every measurable `L^p` family
`g : ℕ → (ℝ → ℂ)`:
`‖(Σ_{k<K} ‖D_k (g k)‖²)^{1/2}‖_{L^p} ≤ C ‖(Σ_{k<K} ‖g k‖²)^{1/2}‖_{L^p}`,
where `D_k = σ_{2^k} - σ_{2^{k+1}}` is the dyadic difference of the curve averages. -/
theorem dyadD_vec_eLpNorm (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff)
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (g : ℕ → ℝ → ℂ),
      (∀ k, Measurable (g k)) →
      (∀ k, MemLp (g k) (ENNReal.ofReal p) volume) →
      eLpNorm (fun x => (∑ k ∈ Finset.range K, ‖dyadD P k (g k) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal C
        * eLpNorm (fun x => (∑ k ∈ Finset.range K, ‖g k x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
          (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hfin⟩ := dyadD_vec_eLpNorm_fin P hdeg hlc hp
  refine ⟨C, hC, fun K g hgm hgmem => ?_⟩
  have h := hfin K (fun t : Fin K => g t.1) (fun t => hgm t.1) (fun t => hgmem t.1)
  have e1 : (fun x : ℝ => (∑ k ∈ Finset.range K, ‖dyadD P k (g k) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
      = fun x : ℝ => (∑ t : Fin K, ‖dyadD P t.1 (g t.1) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    funext x
    rw [sum_range_enorm_sq_eq_sum_fin (fun k => dyadD P k (g k)) x]
  have e2 : (fun x : ℝ => (∑ k ∈ Finset.range K, ‖g k x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
      = fun x : ℝ => (∑ t : Fin K, ‖g t.1 x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    funext x
    rw [sum_range_enorm_sq_eq_sum_fin g x]
  rw [e1, e2]
  exact h
/-! ## The forward square-function bound for the Littlewood–Paley family -/

/-- From an `∫⁻ (·)^p` bound for a complex function to the `eLpNorm` bound. -/
lemma eLpNorm_le_of_lintegral_cplx {p : ℝ} (hp : 0 < p) {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {sf : ℝ → ℝ≥0∞}
    (h : ∫⁻ x, ‖f x‖ₑ ^ p ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, sf x ^ p)
    (hf : AEStronglyMeasurable f volume) (hsf : AEMeasurable sf volume) :
    eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm sf (ENNReal.ofReal p) (volume : Measure ℝ) := by
  rw [← annulusELpNorm_rpow_eq_lintegral hp (g := f) hf,
    ← eLpNorm_rpow_self hp (g := sf) hsf] at h
  have hCeq : (ENNReal.ofReal C) ^ p = ENNReal.ofReal (C ^ p) :=
    ENNReal.ofReal_rpow_of_nonneg hC hp.le
  rw [← hCeq, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le] at h
  exact (ENNReal.rpow_le_rpow_iff hp).mp h

/-- **The reverse Littlewood–Paley bound on lacunary Littlewood–Paley bands.**  If each `v k` has
Fourier transform supported in the `ψ`-band at scale `s + d k` with `d ≥ 2`, then the `L^p` norm of
the sum is controlled by the `ℓ²`-square function of the pieces. -/
theorem reverseLP_of_band {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (s : ℤ) (K : ℕ) (v : ℕ → ℝ → ℂ),
      2 ≤ d →
      (∀ k < K, Integrable (v k)) →
      (∀ k < K, Continuous (v k)) →
      (∀ k < K, Integrable (FourierTransform.fourier (v k))) →
      (∀ k < K, ∀ ξ : ℝ, FourierTransform.fourier (v k) ξ ≠ 0 →
        dyadPsi ((2 : ℝ) ^ (s + (d : ℤ) * (k : ℤ)) * ξ) ≠ 0) →
      (∀ k < K, MemLp (v k) (ENNReal.ofReal p) volume) →
      eLpNorm (fun x => ∑ k ∈ Finset.range K, v k x) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal C *
          eLpNorm (fun x => (∑ k ∈ Finset.range K, ‖v k x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
            (ENNReal.ofReal p) volume := by
  obtain ⟨C₁, hC₁, hdual⟩ := annulusProjectionDual_reindex p hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  refine ⟨3 * C₁, by positivity, fun d s K v hd hvint hvcont hvF hvband hvp => ?_⟩
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hdec : ∀ k < K, ∀ x, v k x
      = ∑ m ∈ atomScales (s + (d : ℤ) * (k : ℤ)), annulusConv annAtomC m (v k) x :=
    fun k hk x => eq_sum_annulusConv_of_fourier_support (hvcont k hk) (hvint k hk)
      (hvF k hk) (hvband k hk) x
  have hsplit : ∀ k < K, ∀ x, v k x
      = annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) - 1) (v k) x
        + annulusConv annAtomC (s + (d : ℤ) * (k : ℤ)) (v k) x
        + annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + 1) (v k) x := by
    intro k hk x
    rw [hdec k hk x, sum_atomScales_eq]
  have hthree : (fun x => ∑ k ∈ Finset.range K, v k x)
      = fun x => (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) - 1) (v k) x)
          + (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ)) (v k) x)
          + (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + 1) (v k) x) := by
    funext x
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hsplit k (Finset.mem_range.mp hk) x]
  have hsingle : ∀ j : ℤ,
      eLpNorm (fun x => ∑ k ∈ Finset.range K,
          annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + j) (v k) x)
          (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal C₁ *
          eLpNorm (fun x => (∑ k ∈ Finset.range K, ‖v k x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
            (ENNReal.ofReal p) volume := by
    intro j
    have hkey := hdual d hd1 s K j v hvp
    refine eLpNorm_le_of_lintegral_cplx hp0 hC₁.le (le_trans hkey (le_of_eq ?_))
      (Finset.aemeasurable_fun_sum _ (fun k hk =>
        aemeasurable_annulusConv annAtomC _ (hvp k (Finset.mem_range.mp hk)).aemeasurable
          (aemeasurable_annulusK annAtomC _))).aestronglyMeasurable
      ((Finset.aemeasurable_fun_sum _ fun k hk =>
        (hvp k (Finset.mem_range.mp hk)).aemeasurable.enorm.pow_const _).pow_const _)
    congr 1
    refine lintegral_congr (fun x => ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hmess : ∀ j : ℤ, AEStronglyMeasurable (fun x : ℝ => ∑ k ∈ Finset.range K,
      annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + j) (v k) x) volume := by
    intro j
    exact (Finset.aemeasurable_fun_sum _ (fun k hk =>
      aemeasurable_annulusConv annAtomC _ (hvp k (Finset.mem_range.mp hk)).aemeasurable
        (aemeasurable_annulusK annAtomC _))).aestronglyMeasurable
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  rw [hthree]
  set E : ℝ≥0∞ := eLpNorm (fun x => (∑ k ∈ Finset.range K, ‖v k x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
    (ENNReal.ofReal p) volume with hE
  have h0 : ∀ j : ℤ, eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K,
      annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + j) (v k) x) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal C₁ * E := fun j => hsingle j
  calc eLpNorm (fun x : ℝ => (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) - 1) (v k) x)
          + (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ)) (v k) x)
          + (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + 1) (v k) x))
        (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x : ℝ => (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) - 1) (v k) x)
          + (∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ)) (v k) x))
          (ENNReal.ofReal p) volume
        + eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + 1) (v k) x)
          (ENNReal.ofReal p) volume :=
        eLpNorm_add_le h1p
    _ ≤ (eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) - 1) (v k) x)
          (ENNReal.ofReal p) volume
        + eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ)) (v k) x)
          (ENNReal.ofReal p) volume)
        + eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K,
            annulusConv annAtomC (s + (d : ℤ) * (k : ℤ) + 1) (v k) x)
          (ENNReal.ofReal p) volume := by
        exact add_le_add (eLpNorm_add_le h1p) le_rfl
    _ ≤ (ENNReal.ofReal C₁ * E + ENNReal.ofReal C₁ * E) + ENNReal.ofReal C₁ * E := by
        refine add_le_add (add_le_add (h0 (-1)) (by simpa using h0 0)) (by simpa using h0 1)
    _ = ENNReal.ofReal (3 * C₁) * E := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          show ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) from ENNReal.ofReal_ofNat 3]
        ring

/-- **The `ℓ²` square function of the Littlewood–Paley family**, in integral form. -/
lemma squareFunction_psiFam_lintegral {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℤ) (F : Finset ℤ) (h : ℝ → ℂ),
      MemLp h (ENNReal.ofReal p) volume →
      ∫⁻ x, (∑ n ∈ F, ‖annulusConv psiFam (s + n) h x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖h x‖ₑ ^ p := by
  obtain ⟨C, hC, hmain⟩ :=
    annulusSquareLpVec psiFam annulusSymbolSmooth_psiFam contDiff_psiFam (p := p) hp
  refine ⟨C, hC, fun s F h hh => ?_⟩
  have h1 := hmain (κ := Unit) s F (fun _ : Unit => h) (fun _ => hh)
  rw [Finset.univ_unique] at h1
  simp only [Finset.sum_singleton] at h1
  have h2 : ∀ x : ℝ, (‖h x‖ₑ ^ (2 : ℝ)) ^ (p / 2) = ‖h x‖ₑ ^ p := by
    intro x
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  rw [lintegral_congr h2] at h1
  exact h1

/-- **The `ℓ²` square function of the Littlewood–Paley family**, in `eLpNorm` form. -/
lemma squareFunction_psiFam_eLpNorm {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℤ) (F : Finset ℤ) (h : ℝ → ℂ),
      MemLp h (ENNReal.ofReal p) volume →
      eLpNorm (fun x => (∑ n ∈ F, ‖annulusConv psiFam (s + n) h x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hmain⟩ := squareFunction_psiFam_lintegral (p := p) hp
  refine ⟨C, hC, fun s F h hh => ?_⟩
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hCp : (C ^ p) ^ (p⁻¹) = C := by
    rw [← Real.rpow_mul (by positivity), mul_inv_cancel₀ hp0.ne', Real.rpow_one]
  have hbound : ∫⁻ x, ((∑ n ∈ F, ‖annulusConv psiFam (s + n) h x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ p
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖h x‖ₑ ^ p := by
    refine le_of_eq_of_le ?_ (hmain s F h hh)
    refine lintegral_congr (fun x => ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have h := eLpNorm_le_of_lintegral_rpow_le_eNN (q := p) (C := C ^ p) hp0 (by positivity)
    (g := fun x => (∑ n ∈ F, ‖annulusConv psiFam (s + n) h x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
    (f := h) hbound
    ((Finset.aemeasurable_fun_sum _ fun n _ =>
      (aemeasurable_annulusConv psiFam _ hh.aestronglyMeasurable.aemeasurable
        (aemeasurable_annulusK psiFam _)).enorm.pow_const _).pow_const _)
    hh.aestronglyMeasurable
  simpa [hCp] using h

/-! ## Commutation of the annulus convolution with the curve averages

This is the analytic core of step 4(c): the annulus convolution `κ_l * ·` commutes with the curve
average `σ_N`, so the `ℓ²`-square function of the pieces `T_{l_k} (D_k h)` is the square function
of `D_k (T_{l_k} h)`, to which the vector-valued maximal inequality applies. -/

/-- The parameter measure of the curve averages: Lebesgue measure restricted to `(0,1]` (a
probability measure). -/
noncomputable def tslpNu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

lemma tslpNu_univ : tslpNu Set.univ = 1 := by
  rw [tslpNu, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

instance tslpNu_isFinite : IsFiniteMeasure tslpNu :=
  ⟨by rw [tslpNu_univ]; exact ENNReal.one_lt_top⟩

/-- `curveSigma` as an integral against `tslpNu`. -/
lemma curveSigma_eq_tslpNu (P : Polynomial ℤ) (N : ℕ) (h : ℝ → ℂ) (x : ℝ) :
    curveSigma P N h x = ∫ t, h (x - (toRealPoly P).eval ((N : ℝ) * t)) ∂tslpNu := by
  rw [curveSigma_apply, tslpNu, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The curve map `(y,t) ↦ y - P (N t)` is quasi-measure-preserving for
`volume ⊗ tslpNu → volume`. -/
lemma tslpNu_qmp (P : Polynomial ℤ) (N : ℕ) :
    Measure.QuasiMeasurePreserving
      (fun p : ℝ × ℝ => p.1 - (toRealPoly P).eval ((N : ℝ) * p.2))
      (volume.prod tslpNu) volume := by
  set Q : ℝ → ℝ := fun t => (toRealPoly P).eval ((N : ℝ) * t) with hQdef
  have hQcont : Continuous Q := by
    rw [hQdef]
    exact (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  set ν : Measure ℝ := Measure.map Q tslpNu with hνdef
  have hqmp1 : Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - p.2)
      ((volume : Measure ℝ).prod ν) volume :=
    quasiMeasurePreserving_sub_of_right_invariant volume ν
  have hmap : Measure.map (Prod.map id Q) ((volume : Measure ℝ).prod tslpNu)
      = ((volume : Measure ℝ).prod ν) := by
    rw [← Measure.map_prod_map (volume : Measure ℝ) tslpNu measurable_id hQcont.measurable,
      Measure.map_id, hνdef]
  exact hqmp1.comp ⟨Measurable.prodMap measurable_id hQcont.measurable, by rw [hmap]⟩

/-- Joint a.e. strong measurability of `h (y - P (N t))` on `volume ⊗ tslpNu`. -/
lemma aestronglyMeasurable_curve (P : Polynomial ℤ) (N : ℕ) {h : ℝ → ℂ}
    (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => h (p.1 - (toRealPoly P).eval ((N : ℝ) * p.2)))
      (volume.prod tslpNu) :=
  hh.comp_quasiMeasurePreserving (tslpNu_qmp P N)

/-- **The curve average is an `L^p` contraction** (`p ≥ 1`) and maps `L^p` into `L^p`. -/
theorem memLp_curveSigma' (P : Polynomial ℤ) (N : ℕ) {p : ℝ} (hp : 1 ≤ p) {h : ℝ → ℂ}
    (hh : MemLp h (ENNReal.ofReal p) volume) :
    MemLp (curveSigma P N h) (ENNReal.ofReal p) volume ∧
      eLpNorm (curveSigma P N h) (ENNReal.ofReal p) volume
        ≤ eLpNorm h (ENNReal.ofReal p) volume := by
  have hcs : ∀ x : ℝ,
      curveSigma P N h x = ∫ t, h (x - (toRealPoly P).eval ((N : ℝ) * t)) ∂tslpNu :=
    fun x => curveSigma_eq_tslpNu P N h x
  have hS_aesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => h (p.1 - (toRealPoly P).eval ((N : ℝ) * p.2)))
      (volume.prod tslpNu) := aestronglyMeasurable_curve P N hh.aestronglyMeasurable
  have hF : AEMeasurable (Function.uncurry
      (fun x t : ℝ => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ))
      ((volume : Measure ℝ).prod tslpNu) := hS_aesm.enorm
  have hmink :=
    Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite
      (μ := (volume : Measure ℝ)) (ν := tslpNu) (p := ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top
      (F := fun x t : ℝ => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ) hF
  have htrans : ∀ c : ℝ,
      eLpNorm (fun x => ‖h (x - c)‖ₑ) (ENNReal.ofReal p) volume
        = eLpNorm h (ENNReal.ofReal p) volume := by
    intro c
    have hmp : MeasurePreserving (fun x : ℝ => x - c) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-c)
    have h1 : eLpNorm (fun x : ℝ => h (x - c)) (ENNReal.ofReal p) volume
        = eLpNorm h (ENNReal.ofReal p) volume :=
      eLpNorm_comp_measurePreserving hh.aestronglyMeasurable hmp
    rw [← h1, eLpNorm_enorm (fun x : ℝ => h (x - c))
      (hh.aestronglyMeasurable.comp_measurePreserving hmp)]
  have hstep4 : ∫⁻ t, eLpNorm (fun x => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ)
        (ENNReal.ofReal p) volume ∂tslpNu = eLpNorm h (ENNReal.ofReal p) volume := by
    calc ∫⁻ t, eLpNorm (fun x => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ)
          (ENNReal.ofReal p) volume ∂tslpNu
        = ∫⁻ _t, eLpNorm h (ENNReal.ofReal p) volume ∂tslpNu :=
          lintegral_congr (fun t => htrans _)
      _ = eLpNorm h (ENNReal.ofReal p) volume := by rw [lintegral_const, tslpNu_univ, mul_one]
  have hbound : eLpNorm (curveSigma P N h) (ENNReal.ofReal p) volume
      ≤ eLpNorm h (ENNReal.ofReal p) volume := by
    calc eLpNorm (curveSigma P N h) (ENNReal.ofReal p) volume
        = eLpNorm (fun x => ∫ t, h (x - (toRealPoly P).eval ((N : ℝ) * t)) ∂tslpNu)
            (ENNReal.ofReal p) volume :=
          eLpNorm_congr_ae (Filter.Eventually.of_forall hcs)
      _ ≤ eLpNorm (fun x => ∫⁻ t, ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu)
            (ENNReal.ofReal p) volume := by
          refine eLpNorm_mono_enorm_ae hS_aesm.integral_prod_right' ?_
          filter_upwards with x
          calc ‖∫ t, h (x - (toRealPoly P).eval ((N : ℝ) * t)) ∂tslpNu‖ₑ
              ≤ ∫⁻ t, ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu :=
                enorm_integral_le_lintegral_enorm _
            _ = ‖∫⁻ t, ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu‖ₑ :=
                (enorm_eq_self _).symm
      _ ≤ ∫⁻ t, eLpNorm (fun x => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ)
            (ENNReal.ofReal p) volume ∂tslpNu := hmink
      _ = eLpNorm h (ENNReal.ofReal p) volume := hstep4
  have hAE : AEStronglyMeasurable (curveSigma P N h) volume := by
    have h1 : AEStronglyMeasurable
        (fun x => ∫ t, h (x - (toRealPoly P).eval ((N : ℝ) * t)) ∂tslpNu) volume :=
      hS_aesm.integral_prod_right'
    rw [show curveSigma P N h
        = (fun x => ∫ t, h (x - (toRealPoly P).eval ((N : ℝ) * t)) ∂tslpNu) from funext hcs]
    exact h1
  exact ⟨lt_of_le_of_lt hbound hh.eLpNorm_lt_top, hbound⟩

/-- `∫⁻ (F x)^p` in terms of the `eLpNorm`, for `ℝ≥0∞`-valued `F`. -/
lemma lintegral_rpow_eq_eLpNorm_rpow {p : ℝ} (hp : 0 < p) (F : ℝ → ℝ≥0∞)
    (hF : AEMeasurable F volume) :
    ∫⁻ x, (F x) ^ p = (eLpNorm F (ENNReal.ofReal p) (volume : Measure ℝ)) ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp only [enorm_eq_self]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- `∫⁻ ‖g‖^p < ∞` for `g ∈ L^p`. -/
lemma lintegral_enorm_rpow_lt_top {p : ℝ} (hp : 0 < p) {g : ℝ → ℂ}
    (hg : MemLp g (ENNReal.ofReal p) volume) : ∫⁻ y, ‖g y‖ₑ ^ p < ⊤ := by
  rw [lintegral_rpow_eq_eLpNorm_rpow hp (fun y => ‖g y‖ₑ) hg.aestronglyMeasurable.enorm,
    eLpNorm_enorm _ hg.aestronglyMeasurable]
  exact (ENNReal.rpow_lt_top_iff_of_pos hp).mpr hg.eLpNorm_lt_top

/-- The annulus kernel is continuous. -/
lemma continuous_kappa (l : ℤ) : Continuous (kappa l) :=
  Commons.Analysis.Fourier.continuous_fourierInv_of_integrable (psiFam l) (integrable_psiFam l)

/-- The annulus kernel is essentially bounded. -/
lemma norm_kappa_le (l : ℤ) (z : ℝ) : ‖kappa l z‖ ≤ ∫ y, ‖psiFam l y‖ :=
  annulusK_fourierInv_le_integral (psiFam l) z

/-- The conjugate exponent of an exponent `p > 1` is `> 1`. -/
lemma one_lt_of_holderConjugate {p q : ℝ} (hp : 1 < p) (hpq : p.HolderConjugate q) : 1 < q := by
  have hpos : 0 < q := hpq.right_pos
  have h := hpq.inv_add_inv_eq_inv
  rw [inv_one] at h
  have hpinv : p⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hp
  have hqinv : q⁻¹ = 1 - p⁻¹ := by linarith
  have hqinvlt : q⁻¹ < (1 : ℝ)⁻¹ := by
    rw [hqinv, inv_one]
    have hpinvpos : (0 : ℝ) < p⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hp)
    linarith
  exact (inv_lt_inv₀ hpos one_pos).mp hqinvlt

/-- `∫⁻ ‖κ_l (x - ·)‖^q < ∞` for every `q ≥ 1`. -/
lemma lintegral_kappa_shift_rpow_lt_top (l : ℤ) {q : ℝ} (hq : 1 ≤ q) (x : ℝ) :
    ∫⁻ y, ‖kappa l (x - y)‖ₑ ^ q < ⊤ := by
  set M : ℝ := ∫ y, ‖psiFam l y‖ with hMdef
  have hMnn : 0 ≤ M := integral_nonneg (fun y => norm_nonneg _)
  have hreal : ∀ t : ℝ, 0 ≤ t → t ≤ M → t ^ q ≤ M ^ (q - 1) * t := by
    intro t ht0 htM
    rcases eq_or_lt_of_le ht0 with h | ht
    · rw [← h, Real.zero_rpow (by linarith : q ≠ 0), mul_zero]
    · rw [show t ^ q = t ^ (q - 1) * t ^ (1 : ℝ) from by
          rw [← Real.rpow_add ht]; ring_nf, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.le htM (by linarith)) ht0
  have hpoint : ∀ y : ℝ, ‖kappa l (x - y)‖ₑ ^ q
      ≤ ENNReal.ofReal (M ^ (q - 1)) * ‖kappa l (x - y)‖ₑ := by
    intro y
    have h1 : ‖kappa l (x - y)‖ ≤ M := norm_kappa_le l (x - y)
    have h2 := hreal ‖kappa l (x - y)‖ (norm_nonneg _) h1
    calc ‖kappa l (x - y)‖ₑ ^ q
        = (ENNReal.ofReal ‖kappa l (x - y)‖) ^ q := by
          rw [enorm_ofReal_eq_cplx]
      _ = ENNReal.ofReal (‖kappa l (x - y)‖ ^ q) :=
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)
      _ ≤ ENNReal.ofReal (M ^ (q - 1) * ‖kappa l (x - y)‖) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (M ^ (q - 1)) * ‖kappa l (x - y)‖ₑ := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hMnn _), enorm_ofReal_eq_cplx]
  have hmul : ∫⁻ y, ‖kappa l (x - y)‖ₑ ^ q
      ≤ ENNReal.ofReal (M ^ (q - 1)) * ∫⁻ y, ‖kappa l (x - y)‖ₑ := by
    calc ∫⁻ y, ‖kappa l (x - y)‖ₑ ^ q
        ≤ ∫⁻ y, ENNReal.ofReal (M ^ (q - 1)) * ‖kappa l (x - y)‖ₑ := lintegral_mono hpoint
      _ = ENNReal.ofReal (M ^ (q - 1)) * ∫⁻ y, ‖kappa l (x - y)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine lt_of_le_of_lt hmul (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  rw [show (fun y : ℝ => ‖kappa l (x - y)‖ₑ)
      = (fun y : ℝ => (fun z : ℝ => ‖kappa l z‖ₑ) (x - y)) from rfl,
    lintegral_sub_left_eq_self (fun z : ℝ => ‖kappa l z‖ₑ) x]
  exact (integrable_kappa l).hasFiniteIntegral

/-- Hölder: `∫⁻ ‖κ_l (x - ·) · g‖ < ∞` for `g ∈ L^p`, `p > 1`. -/
lemma lintegral_kappa_mul_lt_top (l : ℤ) {p q : ℝ} (hp : 1 < p) (hpq : p.HolderConjugate q)
    {g : ℝ → ℂ} (hg : MemLp g (ENNReal.ofReal p) volume) (x : ℝ) :
    ∫⁻ y, ‖kappa l (x - y) * g y‖ₑ < ⊤ := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hq1 : 1 ≤ q := by
    have h := hpq.inv_add_inv_eq_inv
    have hqpos : 0 < q := hpq.right_pos
    by_contra hcon
    push_neg at hcon
    have h1 : q⁻¹ ≥ 1 := by
      rw [ge_iff_le, ← one_div, one_le_div hqpos]
      exact hcon.le
    have h2 : p⁻¹ > 0 := by positivity
    rw [inv_one] at h
    linarith
  have hκae : AEMeasurable (fun y : ℝ => ‖kappa l (x - y)‖ₑ) volume :=
    ((continuous_kappa l).comp (continuous_const.sub continuous_id)).measurable.enorm.aemeasurable
  have hgae : AEMeasurable (fun y : ℝ => ‖g y‖ₑ) volume := (hg.aestronglyMeasurable.aemeasurable).enorm
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (volume : Measure ℝ)) hpq.symm hκae hgae
  simp only [Pi.mul_apply] at hHolder
  rw [show (fun y : ℝ => ‖kappa l (x - y) * g y‖ₑ)
      = (fun y : ℝ => ‖kappa l (x - y)‖ₑ * ‖g y‖ₑ) from funext (fun y => enorm_mul _ _)]
  refine lt_of_le_of_lt hHolder (ENNReal.mul_lt_top ?_ ?_)
  · exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0:ℝ) < 1/q)).mpr
      (lintegral_kappa_shift_rpow_lt_top l hq1 x)
  · exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0:ℝ) < 1/p)).mpr
      (lintegral_enorm_rpow_lt_top hp0 hg)


/-- Minkowski: the `L^p` norm of the `ℝ≥0∞`-valued curve average is at most the `L^p` norm of `h`. -/
lemma eLpNorm_curveAvg_le (P : Polynomial ℤ) (N : ℕ) {p : ℝ} (hp : 1 ≤ p) {h : ℝ → ℂ}
    (hh : MemLp h (ENNReal.ofReal p) volume) :
    eLpNorm (fun y => ∫⁻ t, ‖h (y - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu)
        (ENNReal.ofReal p) volume ≤ eLpNorm h (ENNReal.ofReal p) volume := by
  have hS_aesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => h (p.1 - (toRealPoly P).eval ((N : ℝ) * p.2)))
      (volume.prod tslpNu) := aestronglyMeasurable_curve P N hh.aestronglyMeasurable
  have hF : AEMeasurable (Function.uncurry
      (fun x t : ℝ => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ))
      ((volume : Measure ℝ).prod tslpNu) := hS_aesm.enorm
  have hmink :=
    Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite
      (μ := (volume : Measure ℝ)) (ν := tslpNu) (p := ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top
      (F := fun x t : ℝ => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ) hF
  have htrans : ∀ c : ℝ,
      eLpNorm (fun x => ‖h (x - c)‖ₑ) (ENNReal.ofReal p) volume
        = eLpNorm h (ENNReal.ofReal p) volume := by
    intro c
    have hmp : MeasurePreserving (fun x : ℝ => x - c) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-c)
    have h1 : eLpNorm (fun x : ℝ => h (x - c)) (ENNReal.ofReal p) volume
        = eLpNorm h (ENNReal.ofReal p) volume :=
      eLpNorm_comp_measurePreserving hh.aestronglyMeasurable hmp
    rw [← h1, eLpNorm_enorm (fun x : ℝ => h (x - c))
      (hh.aestronglyMeasurable.comp_measurePreserving hmp)]
  refine hmink.trans (le_of_eq ?_)
  calc ∫⁻ t, eLpNorm (fun x => ‖h (x - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ)
        (ENNReal.ofReal p) volume ∂tslpNu
      = ∫⁻ _t, eLpNorm h (ENNReal.ofReal p) volume ∂tslpNu :=
        lintegral_congr (fun t => htrans _)
    _ = eLpNorm h (ENNReal.ofReal p) volume := by rw [lintegral_const, tslpNu_univ, mul_one]

/-- `∫⁻ (curve average)^p < ∞`. -/
lemma lintegral_curveAvg_rpow_lt_top (P : Polynomial ℤ) (N : ℕ) {p : ℝ} (hp : 1 ≤ p)
    {h : ℝ → ℂ} (hh : MemLp h (ENNReal.ofReal p) volume) :
    ∫⁻ y, (∫⁻ t, ‖h (y - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu) ^ p < ⊤ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  rw [lintegral_rpow_eq_eLpNorm_rpow hp0 (fun y =>
    ∫⁻ t, ‖h (y - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu)
    ((aestronglyMeasurable_curve P N hh.aestronglyMeasurable).enorm.lintegral_prod_right')]
  exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mpr
    (lt_of_le_of_lt (eLpNorm_curveAvg_le P N hp hh) hh.eLpNorm_lt_top)

/-- The convolution of the annulus kernel with an `L^p` function is integrable for every `x`. -/
lemma integrable_kappa_mul_of_memLp (l : ℤ) {p q : ℝ} (hp : 1 < p) (hpq : p.HolderConjugate q)
    {g : ℝ → ℂ} (hg : MemLp g (ENNReal.ofReal p) volume) (x : ℝ) :
    Integrable (fun y : ℝ => kappa l (x - y) * g y) volume :=
  ⟨((continuous_kappa l).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hg.aestronglyMeasurable,
    lintegral_kappa_mul_lt_top l hp hpq hg x⟩

/-- **The annulus convolution commutes with the curve average.** -/
theorem annulusConv_curveSigma (P : Polynomial ℤ) (N : ℕ) (l : ℤ) {p q : ℝ} (hp : 1 < p)
    (hpq : p.HolderConjugate q) {h : ℝ → ℂ} (hh : MemLp h (ENNReal.ofReal p) volume) (x : ℝ) :
    annulusConv psiFam l (curveSigma P N h) x = curveSigma P N (annulusConv psiFam l h) x := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  set F : ℝ → ℝ → ℂ :=
    fun y t => kappa l (x - y) * h (y - (toRealPoly P).eval ((N : ℝ) * t)) with hFdef
  -- joint a.e. strong measurability
  have hFae : AEStronglyMeasurable (Function.uncurry F) ((volume : Measure ℝ).prod tslpNu) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => kappa l (x - p.1))
        ((volume : Measure ℝ).prod tslpNu) :=
      ((continuous_kappa l).comp (continuous_const.sub continuous_fst)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => h (p.1 - (toRealPoly P).eval ((N : ℝ) * p.2)))
        ((volume : Measure ℝ).prod tslpNu) := aestronglyMeasurable_curve P N hh.aestronglyMeasurable
    exact h1.mul h2
  -- the product integrability: Tonelli + Hölder in the space variable
  have hFfin : ∫⁻ z : ℝ × ℝ, ‖Function.uncurry F z‖ₑ ∂((volume : Measure ℝ).prod tslpNu) < ⊤ := by
    have hfun : (fun z : ℝ × ℝ => ‖Function.uncurry F z‖ₑ)
        = fun z : ℝ × ℝ => ‖kappa l (x - z.1)‖ₑ
            * ‖h (z.1 - (toRealPoly P).eval ((N : ℝ) * z.2))‖ₑ := by
      funext z
      simp only [Function.uncurry, hFdef, enorm_mul]
    rw [hfun]
    have hpair : AEMeasurable (fun z : ℝ × ℝ => ‖kappa l (x - z.1)‖ₑ
        * ‖h (z.1 - (toRealPoly P).eval ((N : ℝ) * z.2))‖ₑ)
        ((volume : Measure ℝ).prod tslpNu) := by
      have h1 : AEMeasurable (fun z : ℝ × ℝ => ‖kappa l (x - z.1)‖ₑ)
          ((volume : Measure ℝ).prod tslpNu) :=
        (((continuous_kappa l).comp (continuous_const.sub continuous_fst)).measurable.enorm).aemeasurable
      have h2 : AEMeasurable
          (fun z : ℝ × ℝ => ‖h (z.1 - (toRealPoly P).eval ((N : ℝ) * z.2))‖ₑ)
          ((volume : Measure ℝ).prod tslpNu) := (aestronglyMeasurable_curve P N hh.aestronglyMeasurable).enorm
      exact h1.mul h2
    rw [MeasureTheory.lintegral_prod (μ := (volume : Measure ℝ)) (ν := tslpNu)
      (f := fun z : ℝ × ℝ => ‖kappa l (x - z.1)‖ₑ
        * ‖h (z.1 - (toRealPoly P).eval ((N : ℝ) * z.2))‖ₑ) hpair]
    have hinner : ∀ y : ℝ,
        ∫⁻ t, ‖kappa l (x - y)‖ₑ * ‖h (y - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu
          = ‖kappa l (x - y)‖ₑ
            * (∫⁻ t, ‖h (y - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu) := by
      intro y
      rw [lintegral_const_mul' _ _ enorm_ne_top]
    rw [lintegral_congr hinner]
    have hκae : AEMeasurable (fun y : ℝ => ‖kappa l (x - y)‖ₑ) volume :=
      ((continuous_kappa l).comp (continuous_const.sub continuous_id)).measurable.enorm.aemeasurable
    have hAae : AEMeasurable
        (fun y : ℝ => ∫⁻ t, ‖h (y - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu) volume := by
      have hS := aestronglyMeasurable_curve P N hh.aestronglyMeasurable
      exact (hS.enorm).lintegral_prod_right'
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (volume : Measure ℝ)) hpq.symm
      (f := fun y : ℝ => ‖kappa l (x - y)‖ₑ)
      (g := fun y : ℝ => ∫⁻ t, ‖h (y - (toRealPoly P).eval ((N : ℝ) * t))‖ₑ ∂tslpNu) hκae hAae
    simp only [Pi.mul_apply] at hHolder
    refine lt_of_le_of_lt hHolder (ENNReal.mul_lt_top ?_ ?_)
    · exact (ENNReal.rpow_lt_top_iff_of_pos (div_pos one_pos hpq.right_pos)).mpr
        (lintegral_kappa_shift_rpow_lt_top l (one_lt_of_holderConjugate hp hpq).le x)
    · exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0:ℝ) < 1/p)).mpr
        (lintegral_curveAvg_rpow_lt_top P N hp.le hh)
  have hFint : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod tslpNu) :=
    ⟨hFae, hFfin⟩
  calc annulusConv psiFam l (curveSigma P N h) x
      = ∫ y, ∫ t, F y t ∂tslpNu ∂(volume : Measure ℝ) := by
        rw [annulusConv]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        show annulusK psiFam l (x - y) * curveSigma P N h y
          = ∫ t, F y t ∂tslpNu
        rw [curveSigma_eq_tslpNu]
        exact (MeasureTheory.integral_smul (μ := tslpNu) (c := kappa l (x - y))
          (f := fun t : ℝ => h (y - (toRealPoly P).eval ((N : ℝ) * t)))).symm
    _ = ∫ t, ∫ y, F y t ∂(volume : Measure ℝ) ∂tslpNu := integral_integral_swap hFint
    _ = ∫ t, ∫ y, F (y + (toRealPoly P).eval ((N : ℝ) * t)) t ∂(volume : Measure ℝ) ∂tslpNu := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        exact (MeasureTheory.integral_add_right_eq_self (fun z : ℝ => F z t)
          ((toRealPoly P).eval ((N : ℝ) * t))).symm
    _ = ∫ t, ∫ y, kappa l (x - (toRealPoly P).eval ((N : ℝ) * t) - y) * h y
          ∂(volume : Measure ℝ) ∂tslpNu := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        simp only [hFdef]
        rw [show y + (toRealPoly P).eval ((N : ℝ) * t) - (toRealPoly P).eval ((N : ℝ) * t) = y from by ring,
          show x - (y + (toRealPoly P).eval ((N : ℝ) * t))
              = x - (toRealPoly P).eval ((N : ℝ) * t) - y from by ring]
    _ = ∫ t, annulusConv psiFam l h (x - (toRealPoly P).eval ((N : ℝ) * t)) ∂tslpNu := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        show (∫ y, kappa l (x - (toRealPoly P).eval ((N : ℝ) * t) - y) * h y
            ∂(volume : Measure ℝ))
          = annulusConv psiFam l h (x - (toRealPoly P).eval ((N : ℝ) * t))
        rw [annulusConv]
        rfl
    _ = curveSigma P N (annulusConv psiFam l h) x := by
        rw [curveSigma_eq_tslpNu]

/-- **The annulus convolution commutes with the dyadic difference of curve averages.** -/
theorem annulusConv_dyadD (P : Polynomial ℤ) (k : ℕ) (l : ℤ) {p q : ℝ} (hp : 1 < p)
    (hpq : p.HolderConjugate q) {h : ℝ → ℂ} (hh : MemLp h (ENNReal.ofReal p) volume) (x : ℝ) :
    annulusConv psiFam l (dyadD P k h) x = dyadD P k (annulusConv psiFam l h) x := by
  have h1 := annulusConv_curveSigma P (2 ^ k) l hp hpq hh x
  have h2 := annulusConv_curveSigma P (2 ^ (k + 1)) l hp hpq hh x
  have hM1 : MemLp (curveSigma P (2 ^ k) h) (ENNReal.ofReal p) volume :=
    (memLp_curveSigma' P (2 ^ k) hp.le hh).1
  have hM2 : MemLp (curveSigma P (2 ^ (k + 1)) h) (ENNReal.ofReal p) volume :=
    (memLp_curveSigma' P (2 ^ (k + 1)) hp.le hh).1
  have hInt1 := integrable_kappa_mul_of_memLp l hp hpq hM1 x
  have hInt2 := integrable_kappa_mul_of_memLp l hp hpq hM2 x
  have hsub : annulusConv psiFam l (dyadD P k h) x
      = annulusConv psiFam l (curveSigma P (2 ^ k) h) x
        - annulusConv psiFam l (curveSigma P (2 ^ (k + 1)) h) x := by
    rw [show dyadD P k h
        = fun y : ℝ => curveSigma P (2 ^ k) h y - curveSigma P (2 ^ (k + 1)) h y from rfl]
    rw [annulusConv]
    simp only [mul_sub]
    rw [annulusConv]
    exact MeasureTheory.integral_sub hInt1 hInt2
  rw [hsub, h1, h2]
  rfl



/-! ## Auxiliary facts for the assembly of `Ts_lp_uniform` -/

/-- The Fourier transform only depends on the a.e. class. -/
lemma fourier_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    FourierTransform.fourier f = FourierTransform.fourier g := by
  by_cases hf : Integrable f volume
  · have hg : Integrable g volume := hf.congr h
    funext ξ
    rw [Real.fourier_eq, Real.fourier_eq]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  · have hg : ¬ Integrable g volume := fun hg' => hf (hg'.congr h.symm)
    rw [Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable hf,
      Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable hg]

/-- If `t` is a null set, then for a.e. `x` the curve `s ↦ x - P (N s)` avoids `t` for a.e. `s`. -/
lemma ae_curve_compl_of_null (P : Polynomial ℤ) (N : ℕ) {t : Set ℝ} (htmeas : MeasurableSet t)
    (ht0 : volume t = 0) :
    ∀ᵐ x ∂(volume : Measure ℝ), ∀ᵐ s ∂tslpNu,
      x - (toRealPoly P).eval ((N : ℝ) * s) ∉ t := by
  have hQmeas : Measurable (fun p : ℝ × ℝ => (toRealPoly P).eval ((N : ℝ) * p.2)) :=
    (Polynomial.continuous (toRealPoly P)).measurable.comp
      ((continuous_const.mul continuous_id).measurable.comp measurable_snd)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      t.indicator (fun _ => (1 : ℝ≥0∞)) (p.1 - (toRealPoly P).eval ((N : ℝ) * p.2))) :=
    (Measurable.indicator measurable_const htmeas).comp (measurable_fst.sub hQmeas)
  have hswap := MeasureTheory.lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := tslpNu)
    (f := fun x s : ℝ => t.indicator (fun _ => (1 : ℝ≥0∞))
      (x - (toRealPoly P).eval ((N : ℝ) * s))) hmeas.aemeasurable
  have hinner : ∀ s : ℝ, ∫⁻ x, t.indicator (fun _ => (1 : ℝ≥0∞))
      (x - (toRealPoly P).eval ((N : ℝ) * s)) ∂(volume : Measure ℝ) = 0 := by
    intro s
    rw [lintegral_sub_right_eq_self (fun z : ℝ => t.indicator (fun _ => (1 : ℝ≥0∞)) z)
      ((toRealPoly P).eval ((N : ℝ) * s))]
    rw [MeasureTheory.lintegral_indicator_const htmeas (1 : ℝ≥0∞), one_mul]
    exact ht0
  have hFae : AEMeasurable (fun x : ℝ => ∫⁻ s, t.indicator (fun _ => (1 : ℝ≥0∞))
      (x - (toRealPoly P).eval ((N : ℝ) * s)) ∂tslpNu) volume :=
    hmeas.aemeasurable.lintegral_prod_right
  have hzero : ∫⁻ x, (∫⁻ s, t.indicator (fun _ => (1 : ℝ≥0∞))
      (x - (toRealPoly P).eval ((N : ℝ) * s)) ∂tslpNu) ∂(volume : Measure ℝ) = 0 := by
    rw [hswap]
    simp only [hinner, lintegral_zero]
  filter_upwards [(MeasureTheory.lintegral_eq_zero_iff' hFae).mp hzero] with x hx
  have hx' : (fun s : ℝ => t.indicator (fun _ => (1 : ℝ≥0∞))
      (x - (toRealPoly P).eval ((N : ℝ) * s))) =ᵐ[tslpNu] 0 :=
    (MeasureTheory.lintegral_eq_zero_iff' (hmeas.comp (measurable_const.prodMk measurable_id)).aemeasurable).mp hx
  filter_upwards [hx'] with s hs
  rw [Pi.zero_apply] at hs
  by_contra hmem
  rw [Set.indicator_of_mem hmem] at hs
  exact one_ne_zero hs

/-- The curve average only depends on the a.e. class of the input. -/
lemma curveSigma_congr (P : Polynomial ℤ) (N : ℕ) {g g' : ℝ → ℂ} (h : g =ᵐ[volume] g') :
    curveSigma P N g =ᵐ[volume] curveSigma P N g' := by
  obtain ⟨t, ht, htmeas, ht0⟩ :=
    exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp h)
  have hgt : ∀ x : ℝ, x ∉ t → g x = g' x := by
    intro x hx
    by_contra hne
    exact hx (ht hne)
  filter_upwards [ae_curve_compl_of_null P N htmeas ht0] with x hx
  rw [curveSigma_eq_tslpNu, curveSigma_eq_tslpNu]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hx] with s hs
  rw [hgt _ hs]

/-- The projection of the zero function is zero. -/
lemma dyadicProj_zero (ψ : ℝ → ℝ) (m : ℤ) :
    dyadicProj ψ m (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
  funext x
  simp only [dyadicProj]
  have h : FourierTransform.fourier (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
    funext ξ
    rw [Real.fourier_eq]
    simp
  rw [show (fun ξ : ℝ => (ψ ((2 : ℝ) ^ m * ξ) : ℂ)
        * FourierTransform.fourier (fun _ : ℝ => (0 : ℂ)) ξ) = fun _ => 0 from by
      funext ξ; rw [h]; simp]
  rw [Real.fourierInv_eq']
  simp

/-- The annulus convolution of a measurable function is measurable. -/
lemma measurable_annulusConv (l : ℤ) {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (annulusConv psiFam l g) := by
  have hjoint : StronglyMeasurable (fun p : ℝ × ℝ => annulusK psiFam l (p.1 - p.2) * g p.2) :=
    (((continuous_kappa l).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).mul
      (hg.comp measurable_snd).stronglyMeasurable
  exact (hjoint.integral_prod_right (ν := volume)).measurable

/-- The annulus convolution maps `L^p` into `L^p` (`p ≥ 1`). -/
lemma memLp_annulusConv (l : ℤ) {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℂ}
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    MemLp (annulusConv psiFam l g) (ENNReal.ofReal p) volume := by
  have hK : MemLp (kappa l) 1 volume := memLp_one_iff_integrable.mpr (integrable_kappa l)
  have hbound := Commons.Analysis.Convolution.eLpNorm_convolution_le_complex (kappa l) g p hp hK hg
  rw [show (fun x : ℝ => ∫ y, kappa l (x - y) * g y) = annulusConv psiFam l g from rfl] at hbound
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hK.eLpNorm_lt_top hg.eLpNorm_lt_top)

/-- The dyadic difference of curve averages is in `L^p` for an `L^p` input. -/
lemma memLp_dyadD (P : Polynomial ℤ) (k : ℕ) {p : ℝ} (hp : 1 ≤ p) {h : ℝ → ℂ}
    (hh : MemLp h (ENNReal.ofReal p) volume) : MemLp (dyadD P k h) (ENNReal.ofReal p) volume := by
  rw [show dyadD P k h = fun x => curveSigma P (2 ^ k) h x - curveSigma P (2 ^ (k + 1)) h x
      from rfl]
  exact (memLp_curveSigma' P (2 ^ k) hp hh).1.sub (memLp_curveSigma' P (2 ^ (k + 1)) hp hh).1


/-- For an integrable input, the Littlewood--Paley projection is the annulus convolution. -/
lemma dyadicProj_eq_annulusConv {m : ℤ} {G : ℝ → ℂ} (hG : Integrable G) :
    dyadicProj dyadPsi m G = annulusConv psiFam m G := by
  funext y
  rw [dyadicProj_eq_convolution hG]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show G z * kappa m (y - z) = annulusK psiFam m (y - z) * G z
  rw [mul_comm]
  rfl

/-! ## The uniform `L^{p₁}` bound on the Littlewood--Paley blocks `T_s` (step 4(c) of
`Maximal/DRDF_ROUTE.md`) -/

/-- **The uniform `L^{p₁}` bound on the block `T_s`.**  For `p₁ > 2` there is `B > 0` such that for
every `K`, every sequence of signs `ε` with `‖ε k‖ ≤ 1`, every shift `s ∈ ℤ` and every
`h ∈ L^{p₁}(ℝ)`,

`‖Σ_{k<K} S̃_{dk+s}(ε_k · S_{dk+s}(D_k h))‖_{p₁} ≤ B ‖h‖_{p₁}`,

where `d = P.natDegree ≥ 2`, `D_k = σ_{2^k} − σ_{2^{k+1}}` is the dyadic difference of the curve
averages and `S_l`, `S̃_l` are the Littlewood--Paley multipliers with symbols `ψ(2^l·)`,
`ψ̃(2^l·)`. -/
theorem Ts_lp_uniform (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff)
    (p₁ : ℝ) (hp₁ : 2 < p₁) :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (h : ℝ → ℂ),
      MeasureTheory.MemLp h (ENNReal.ofReal p₁) MeasureTheory.volume →
      MeasureTheory.eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K, Work.BourgainPlan.Maximal.dyadicProj Work.BourgainPlan.Maximal.dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s) (fun y : ℝ => ε k * Work.BourgainPlan.Maximal.dyadicProj Work.BourgainPlan.Maximal.dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (Work.BourgainPlan.Maximal.dyadD P k h) y) x) (ENNReal.ofReal p₁) MeasureTheory.volume ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm h (ENNReal.ofReal p₁) MeasureTheory.volume := by
  classical
  have hp1' : (1 : ℝ) < p₁ := lt_trans one_lt_two hp₁
  set q : ℝ := p₁ / (p₁ - 1) with hqdef
  have hpq : p₁.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp1', by
    rw [hqdef]; field_simp; ring⟩
  obtain ⟨C_rev, hC_rev, hrev⟩ := reverseLP_of_band (p := p₁) hp1'
  obtain ⟨C_d, hC_d, hvd⟩ := dyadD_vec_eLpNorm P hdeg hlc (le_of_lt hp₁)
  obtain ⟨C_s, hC_s, hsq⟩ := squareFunction_psiFam_eLpNorm (p := p₁) hp1'
  refine ⟨C_rev * C_d * C_s, by positivity, fun K ε hε s h hh => ?_⟩
  -- replace `h` by a measurable representative
  set h' : ℝ → ℂ := hh.aemeasurable.mk h with hh'def
  have hh'meas : Measurable h' := hh.aemeasurable.measurable_mk
  have hh'ae : h =ᵐ[volume] h' := hh.aemeasurable.ae_eq_mk
  have hh'mem : MemLp h' (ENNReal.ofReal p₁) volume := (memLp_congr_ae hh'ae).mp hh
  have hheLp : eLpNorm h' (ENNReal.ofReal p₁) volume = eLpNorm h (ENNReal.ofReal p₁) volume :=
    eLpNorm_congr_ae hh'ae.symm
  -- the `LHS` is unchanged under a.e. equal inputs
  have hLHS : (fun x : ℝ => ∑ k ∈ Finset.range K,
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
            (dyadD P k h) y) x)
      = (fun x : ℝ => ∑ k ∈ Finset.range K,
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y : ℝ => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
            (dyadD P k h') y) x) := by
    funext x
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hD : dyadD P k h =ᵐ[volume] dyadD P k h' := by
      have h1 := curveSigma_congr P (2 ^ k) hh'ae
      have h2 := curveSigma_congr P (2 ^ (k + 1)) hh'ae
      rw [show dyadD P k h
            = fun x => curveSigma P (2 ^ k) h x - curveSigma P (2 ^ (k + 1)) h x from rfl,
        show dyadD P k h'
            = fun x => curveSigma P (2 ^ k) h' x - curveSigma P (2 ^ (k + 1)) h' x from rfl]
      exact h1.sub h2
    simp only [dyadicProj, fourier_congr_ae hD]
  rw [hLHS]
  -- the pieces
  set w : ℕ → ℝ → ℂ := fun k =>
    dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k h') with hw
  set a : ℕ → ℝ → ℂ := fun k =>
    annulusConv psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) h' with ha
  set v : ℕ → ℝ → ℂ := fun k =>
    if Integrable (dyadD P k h') volume then (fun x => ε k * w k x) else 0 with hv
  have hw_eq : ∀ k, w k = dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s)
      (dyadD P k h') := fun k => rfl
  have ha_eq : ∀ k, a k = annulusConv psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) h' :=
    fun k => rfl
  have hv_eq : ∀ k, v k = if Integrable (dyadD P k h') volume then (fun x => ε k * w k x)
      else 0 := fun k => rfl
  have hv_apply : ∀ (k : ℕ) (x : ℝ),
      v k x = if Integrable (dyadD P k h') volume then ε k * w k x else 0 := by
    intro k x
    rw [hv_eq k]
    split <;> simp
  -- Step 0: the pointwise domination `‖v k‖ ≤ ‖D_k (a k)‖`
  have hpt : ∀ (k : ℕ) (x : ℝ), ‖v k x‖ₑ ≤ ‖dyadD P k (a k) x‖ₑ := by
    intro k x
    rw [ha_eq k, hv_apply k x]
    by_cases hk : Integrable (dyadD P k h') volume
    · rw [if_pos hk, enorm_mul]
      have hw_conv : w k = annulusConv psiFam ((P.natDegree : ℤ) * (k : ℤ) + s)
          (dyadD P k h') := by
        exact (hw_eq k).trans (dyadicProj_eq_annulusConv hk)
      have hcomm := annulusConv_dyadD P k ((P.natDegree : ℤ) * (k : ℤ) + s) hp1' hpq hh'mem x
      rw [hw_conv, ← hcomm]
      calc ‖ε k‖ₑ * ‖annulusConv psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k h') x‖ₑ
          ≤ 1 * ‖annulusConv psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k h') x‖ₑ :=
            mul_le_mul_of_nonneg_right (by
              calc ‖ε k‖ₑ = ENNReal.ofReal ‖ε k‖ := enorm_ofReal_eq_cplx (ε k)
                _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hε k)
                _ = 1 := ENNReal.ofReal_one) zero_le
        _ = ‖annulusConv psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k h') x‖ₑ :=
            one_mul _
    · rw [if_neg hk, enorm_zero]
      exact bot_le
  -- Step 1: absorption of the wider bump
  have hstep1 : (fun x : ℝ => ∑ k ∈ Finset.range K,
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y : ℝ => ε k * w k y) x) =ᵐ[volume]
      fun x => ∑ k ∈ Finset.range K, v k x := by
    have hterm : ∀ k ∈ Finset.range K, (fun x : ℝ =>
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y : ℝ => ε k * w k y) x) =ᵐ[volume] v k := by
      intro k _
      by_cases hk : Integrable (dyadD P k h') volume
      · rw [hv_eq k, if_pos hk]
        exact dyadicProj_tilde_absorption (m := (P.natDegree : ℤ) * (k : ℤ) + s)
          (G := dyadD P k h') hk (ε k)
      · have hw0 : w k = 0 := by
          rw [hw_eq k]
          exact dyadicProj_eq_zero_of_not_integrable hk
        rw [hv_eq k, if_neg hk, hw0]
        have hzero : (fun y : ℝ => ε k * (0 : ℝ → ℂ) y) = fun _ => 0 := by
          funext y; simp
        rw [hzero, dyadicProj_zero]
        exact Filter.EventuallyEq.rfl
    have hall := (Finset.eventually_all (Finset.range K)).2 hterm
    filter_upwards [hall] with x hx
    exact Finset.sum_congr rfl (fun k hk => hx k hk)
  -- Step 2: the reverse Littlewood--Paley bound
  have hv_int : ∀ k < K, Integrable (v k) volume := by
    intro k _
    by_cases hk : Integrable (dyadD P k h') volume
    · rw [hv_eq k, if_pos hk]
      rw [hw_eq k]
      exact (integrable_dyadicProj hk).const_mul (ε k)
    · rw [hv_eq k, if_neg hk]
      exact integrable_zero _ _ _
  have hv_cont : ∀ k < K, Continuous (v k) := by
    intro k _
    by_cases hk : Integrable (dyadD P k h') volume
    · rw [hv_eq k, if_pos hk]
      rw [hw_eq k]
      exact (continuous_dyadicProj hk).const_mul (ε k)
    · rw [hv_eq k, if_neg hk]
      exact continuous_const
  have hfourier_eq : ∀ k, Integrable (dyadD P k h') volume →
      FourierTransform.fourier (fun x => ε k * w k x)
        = fun ξ => ε k * (psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ
            * FourierTransform.fourier (dyadD P k h') ξ) := by
    intro k hk
    funext ξ
    rw [fourier_const_mul]
    rw [hw_eq k, fourier_dyadicProj hk]
  have hz : FourierTransform.fourier (0 : ℝ → ℂ) = 0 := by
    funext ξ
    rw [Real.fourier_eq]
    simp
  have hv_fourier : ∀ k < K, Integrable (FourierTransform.fourier (v k)) volume := by
    intro k _
    by_cases hk : Integrable (dyadD P k h') volume
    · rw [hv_eq k, if_pos hk, hfourier_eq k hk]
      exact (integrable_psiFam_mul_fourier hk).const_mul (ε k)
    · rw [hv_eq k, if_neg hk, hz]
      exact integrable_zero _ _ _
  have hv_band : ∀ k < K, ∀ ξ : ℝ, FourierTransform.fourier (v k) ξ ≠ 0 →
      dyadPsi ((2 : ℝ) ^ (s + (P.natDegree : ℤ) * (k : ℤ)) * ξ) ≠ 0 := by
    intro k _ ξ hξ
    by_cases hk : Integrable (dyadD P k h') volume
    · rw [hv_eq k, if_pos hk, hfourier_eq k hk] at hξ
      have hξ1 : ε k * (psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ
          * FourierTransform.fourier (dyadD P k h') ξ) ≠ 0 := hξ
      have hψ : psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ ≠ 0 := by
        intro h0
        simp only [h0, mul_zero, zero_mul] at hξ1
        exact hξ1 rfl
      have hψ' : ((dyadPsi ((2 : ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * ξ) : ℝ) : ℂ) ≠ 0 := hψ
      rw [show (2 : ℝ) ^ (s + (P.natDegree : ℤ) * (k : ℤ)) * ξ
          = (2 : ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * ξ from by
        rw [show s + (P.natDegree : ℤ) * (k : ℤ) = (P.natDegree : ℤ) * (k : ℤ) + s from by ring]]
      exact Complex.ofReal_ne_zero.mp hψ'
    · rw [hv_eq k, if_neg hk, hz] at hξ
      exact absurd rfl hξ
  have hv_mem : ∀ k < K, MemLp (v k) (ENNReal.ofReal p₁) volume := by
    intro k _
    by_cases hk : Integrable (dyadD P k h') volume
    · rw [hv_eq k, if_pos hk]
      refine MemLp.const_mul ?_ (ε k)
      have hwn : w k = annulusConv psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k h') :=
        (hw_eq k).trans (dyadicProj_eq_annulusConv hk)
      rw [hwn]
      exact memLp_annulusConv _ (le_of_lt hp1') (memLp_dyadD P k (le_of_lt hp1') hh'mem)
    · rw [hv_eq k, if_neg hk]
      exact MemLp.zero
  have ha_meas : ∀ k : ℕ, Measurable (a k) := by
    intro k
    rw [ha_eq k]
    exact measurable_annulusConv _ hh'meas
  have ha_mem : ∀ k : ℕ, MemLp (a k) (ENNReal.ofReal p₁) volume := by
    intro k
    rw [ha_eq k]
    exact memLp_annulusConv _ (le_of_lt hp1') hh'mem
  -- Step 3: the square function of `v` is dominated by that of `D_k (a k)`
  have hstep3 : eLpNorm (fun x : ℝ => (∑ k ∈ Finset.range K, ‖v k x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
        (ENNReal.ofReal p₁) volume
      ≤ eLpNorm (fun x : ℝ =>
          (∑ k ∈ Finset.range K, ‖dyadD P k (a k) x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
        (ENNReal.ofReal p₁) volume := by
    refine eLpNorm_mono_enorm_ae (((Finset.aemeasurable_fun_sum _ fun k hk =>
      ((hv_mem k (Finset.mem_range.mp hk)).aestronglyMeasurable.aemeasurable.enorm.pow_const _))
        ).pow_const _).aestronglyMeasurable ?_
    filter_upwards with x
    rw [enorm_eq_self, enorm_eq_self]
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum (fun k _ => ?_)) (by norm_num)
    exact ENNReal.rpow_le_rpow (hpt k x) (by norm_num)
  -- Step 4: the vector-valued maximal bound
  have hstep4 : eLpNorm (fun x : ℝ =>
        (∑ k ∈ Finset.range K, ‖dyadD P k (a k) x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
        (ENNReal.ofReal p₁) volume
      ≤ ENNReal.ofReal C_d * eLpNorm (fun x : ℝ =>
          (∑ k ∈ Finset.range K, ‖a k x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
        (ENNReal.ofReal p₁) volume :=
    hvd K a ha_meas ha_mem
  -- Step 5: the forward square function, reindexed
  have hsq_eq : (fun x : ℝ => (∑ k ∈ Finset.range K, ‖a k x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
      = fun x : ℝ => (∑ n ∈ (Finset.range K).image (fun k : ℕ => (P.natDegree : ℤ) * (k : ℤ)),
            ‖annulusConv psiFam (s + n) h' x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2) := by
    funext x
    congr 1
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [ha_eq k, show (P.natDegree : ℤ) * (k : ℤ) + s
          = s + (P.natDegree : ℤ) * (k : ℤ) from by ring]
    · intro a' _ b _ hab
      have hne : ((P.natDegree : ℕ) : ℤ) ≠ 0 := by
        have : (0 : ℕ) < P.natDegree := lt_of_lt_of_le (by norm_num) hdeg
        exact_mod_cast this.ne'
      have h1 : (a' : ℤ) = (b : ℤ) := mul_left_cancel₀ hne hab
      exact_mod_cast h1
  have hstep5 : eLpNorm (fun x : ℝ => (∑ k ∈ Finset.range K, ‖a k x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
        (ENNReal.ofReal p₁) volume ≤ ENNReal.ofReal C_s * eLpNorm h' (ENNReal.ofReal p₁) volume := by
    rw [hsq_eq]
    exact hsq s ((Finset.range K).image (fun k : ℕ => (P.natDegree : ℤ) * (k : ℤ))) h' hh'mem
  -- the chain
  calc eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K,
        dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
          (fun y : ℝ => ε k * w k y) x) (ENNReal.ofReal p₁) volume
      = eLpNorm (fun x : ℝ => ∑ k ∈ Finset.range K, v k x) (ENNReal.ofReal p₁) volume :=
        eLpNorm_congr_ae hstep1
    _ ≤ ENNReal.ofReal C_rev * eLpNorm (fun x : ℝ =>
          (∑ k ∈ Finset.range K, ‖v k x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
          (ENNReal.ofReal p₁) volume :=
        hrev P.natDegree s K v hdeg hv_int hv_cont hv_fourier hv_band hv_mem
    _ ≤ ENNReal.ofReal C_rev * eLpNorm (fun x : ℝ =>
          (∑ k ∈ Finset.range K, ‖dyadD P k (a k) x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
          (ENNReal.ofReal p₁) volume :=
        mul_le_mul_of_nonneg_left hstep3 zero_le
    _ ≤ ENNReal.ofReal C_rev * (ENNReal.ofReal C_d * eLpNorm (fun x : ℝ =>
          (∑ k ∈ Finset.range K, ‖a k x‖ₑ ^ (2 : ℝ)) ^ ((1:ℝ)/2))
          (ENNReal.ofReal p₁) volume) :=
        mul_le_mul_of_nonneg_left hstep4 zero_le
    _ ≤ ENNReal.ofReal C_rev * (ENNReal.ofReal C_d *
          (ENNReal.ofReal C_s * eLpNorm h' (ENNReal.ofReal p₁) volume)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep5 zero_le) zero_le
    _ = ENNReal.ofReal (C_rev * C_d * C_s) * eLpNorm h (ENNReal.ofReal p₁) volume := by
        rw [hheLp, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C_rev * C_d),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C_rev)]
        ring

end

end Work.BourgainPlan.Maximal
