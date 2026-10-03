/-
# The rescaled `η`-cutoffs are uniformly `L^q` Fourier multipliers

This file proves `Work.KMTAreas.A7.EtaMult`: there is a single constant `M` such that for every
`k : ℤ` and every exponent `q ≥ 1` (including `q = ⊤`) the rescaled cutoff
`η_{≤k}(θ) = η(θ / 2^k)` (`Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k`) is an
`L^q` Fourier multiplier on `ℝ` with bound `M`.

## The mathematics

`η_{≤k}` is the Fourier transform of the rescaled approximate identity
`K_k(x) = 2^k ψ(2^k x)`, where `ψ = 𝓕⁻ η`; the factor `2^k` from the dilation exactly compensates
the Jacobian of `x ↦ 2^k x`, so `‖K_k‖_{L¹} = ‖ψ‖_{L¹}` for every `k`.  Hence
`T_{η_{≤k}} f = f ⋆ K_k` satisfies `‖T_{η_{≤k}} f‖_{L^q} ≤ ‖ψ‖_{L¹} ‖f‖_{L^q}` by Young's
inequality, with a constant independent of `k` and `q`.

## Layout

* `Work.KMTAreas.A7.contMulOp_eq_convolution` (`EtaMultAux.lean`) — `T_φ f = f ⋆ 𝓕⁻φ`;
* `Work.KMTAreas.A7.isLqMultiplierBound_of_schwartzKernel_top` (`q = ⊤`) — Young's inequality at
  the endpoint, a pointwise estimate; the finite-`q` case is `etaMult_lqBound_finite` below;
* `Work.KMTAreas.A7.fourierInv_comp_div` — the dilation rule for `𝓕⁻`;
* `Work.KMTAreas.A7.eLpNorm_comp_smul_mul` — the `L¹` norm is invariant under the dilation;
* below, the assembly: the Schwartz maps for `kmtEta` and `η_{≤k}`, the kernel `K_k`, and the
  single constant `M`.
-/
import Mathlib
import Submission.Work.KMTContract.etaCutRegular
import Submission.Work.KMTAreas.A7.fourierInv_comp_div
import Submission.Work.KMTAreas.A7.eLpNorm_comp_smul_mul
import Submission.Work.KMTAreas.A7.isLqMultiplierBound_of_schwartzKernel_top
import Submission.Port.Aesm

set_option autoImplicit false
open scoped FourierTransform ENNReal NNReal
open MeasureTheory Filter

namespace Work.KMTAreas.A7

open Work.KMTContract
open Work.Analysis.IonescuWainger (etaCut)
open Work.Analysis.IWMultiplier (IsLqMultiplierBound contMulOp)

/-! ## `kmtEta` as a Schwartz function and its inverse Fourier transform -/

theorem etaMult_kmtEta_supp : Function.support kmtEta ⊆ Metric.closedBall (0:ℝ) 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h
  exact hx (kmtEta_zero (le_of_lt (not_le.mp h)))

theorem etaMult_kmtEta_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) kmtEta :=
  (ContinuousLinearMap.contDiff (n := (↑(⊤ : ℕ∞))) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)).comp
    (ContDiffBump.contDiff kmtBump (n := ⊤))

/-- The cutoff `η = kmtEta` as a Schwartz function. -/
noncomputable def etaMult_kmtEtaSch : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℝ) 1)
    etaMult_kmtEta_supp).toSchwartzMap etaMult_kmtEta_contDiff

theorem etaMult_kmtEtaSch_coe (x : ℝ) : etaMult_kmtEtaSch x = kmtEta x :=
  HasCompactSupport.toSchwartzMap_toFun _ _ x

/-- The convolution kernel `ψ = 𝓕⁻ η` of the cutoff `η`, as a Schwartz function. -/
noncomputable def etaMult_psiSch : SchwartzMap ℝ ℂ :=
  FourierTransformInv.fourierInv etaMult_kmtEtaSch

theorem etaMult_psiSch_coe : ⇑etaMult_psiSch = FourierTransformInv.fourierInv kmtEta := by
  rw [show ⇑etaMult_psiSch = FourierTransformInv.fourierInv (⇑etaMult_kmtEtaSch) from
    SchwartzMap.fourierInv_coe etaMult_kmtEtaSch]
  exact congrArg FourierTransformInv.fourierInv (funext etaMult_kmtEtaSch_coe)

theorem etaMult_psiSch_measurable : Measurable (FourierTransformInv.fourierInv kmtEta) := by
  rw [← etaMult_psiSch_coe]
  exact etaMult_psiSch.continuous.measurable

theorem etaMult_psiSch_ne_top : eLpNorm (⇑etaMult_psiSch) 1 volume ≠ ⊤ :=
  ne_of_lt ((memLp_one_iff_integrable.mpr etaMult_psiSch.integrable).eLpNorm_lt_top)

/-- **The constant of the estimate**: `1` or the `L¹` norm of the kernel `ψ = 𝓕⁻ η`. -/
noncomputable def etaMult_M : NNReal := max 1 (eLpNorm (⇑etaMult_psiSch) 1 volume).toNNReal

theorem etaMult_M_pos : 0 < etaMult_M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem etaMult_coe_M :
    (etaMult_M : ENNReal) = max 1 (eLpNorm (⇑etaMult_psiSch) 1 volume) := by
  rw [etaMult_M, ENNReal.coe_max, ENNReal.coe_toNNReal etaMult_psiSch_ne_top, ENNReal.coe_one]

theorem etaMult_psiSch_le_M :
    eLpNorm (⇑etaMult_psiSch) 1 volume ≤ ENNReal.ofReal (etaMult_M : ℝ) := by
  rw [ENNReal.ofReal_coe_nnreal, etaMult_coe_M]
  exact le_max_right _ _

/-! ## The rescaled cutoffs `η_{≤k}` and their kernels -/

theorem etaMult_etaCut_compact (k : ℤ) : HasCompactSupport (etaCut kmtEta k) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0:ℝ) ((2:ℝ)^k)) ?_
  intro θ hθ
  rw [Function.mem_support] at hθ
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h
  exact hθ ((etaCutRegular k).2.2 θ (le_of_lt (not_le.mp h)))

/-- The rescaled cutoff `η_{≤k}` as a Schwartz function. -/
noncomputable def etaMult_etaCutSch (k : ℤ) : SchwartzMap ℝ ℂ :=
  (etaMult_etaCut_compact k).toSchwartzMap (etaCutRegular k).1

theorem etaMult_etaCutSch_coe (k : ℤ) (x : ℝ) : etaMult_etaCutSch k x = etaCut kmtEta k x :=
  HasCompactSupport.toSchwartzMap_toFun _ _ x

/-- The kernel `K_k = 𝓕⁻ η_{≤k}` of the rescaled cutoff. -/
noncomputable def etaMult_K (k : ℤ) : SchwartzMap ℝ ℂ :=
  FourierTransformInv.fourierInv (etaMult_etaCutSch k)

theorem etaMult_K_fourier (k : ℤ) :
    ∀ ξ : ℝ, FourierTransform.fourier (⇑(etaMult_K k)) ξ = etaCut kmtEta k ξ := by
  intro ξ
  have hcoe : ⇑(etaMult_etaCutSch k) = etaCut kmtEta k := funext (etaMult_etaCutSch_coe k)
  have h1 : FourierTransform.fourier (⇑(etaMult_K k)) = ⇑(etaMult_etaCutSch k) := by
    rw [← SchwartzMap.fourier_coe (etaMult_K k),
      show FourierTransform.fourier (etaMult_K k) = etaMult_etaCutSch k from
        FourierInvPair.fourier_fourierInv_eq (etaMult_etaCutSch k)]
  rw [h1, hcoe]

theorem etaMult_K_norm (k : ℤ) :
    eLpNorm (⇑(etaMult_K k)) 1 volume ≤ ENNReal.ofReal (etaMult_M : ℝ) := by
  have hc : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
  have hcoe : ⇑(etaMult_K k) = fun x : ℝ =>
      (((2:ℝ)^k : ℝ) : ℂ) • FourierTransformInv.fourierInv kmtEta ((2:ℝ)^k * x) := by
    rw [show ⇑(etaMult_K k) = FourierTransformInv.fourierInv (⇑(etaMult_etaCutSch k)) from
      SchwartzMap.fourierInv_coe (etaMult_etaCutSch k)]
    rw [show ⇑(etaMult_etaCutSch k) = (fun θ : ℝ => kmtEta (θ / (2:ℝ)^k)) from
      funext (etaMult_etaCutSch_coe k)]
    exact fourierInv_comp_div kmtEta hc
  rw [hcoe, eLpNorm_comp_smul_mul etaMult_psiSch_measurable hc, ← etaMult_psiSch_coe]
  exact etaMult_psiSch_le_M

/-! ## The multiplier bounds (Young's inequality)

For a symbol `φ` which is the Fourier transform of an `L¹` kernel `K`, Young's inequality for
convolutions gives `‖T_φ f‖_{L^q} ≤ ‖K‖_{L¹} ‖f‖_{L^q}` for every `1 ≤ q ≤ ∞`.  The finite range
`1 ≤ q < ∞` is `etaMult_lqBound_finite`; the endpoint `q = ⊤` is the delegated lemma
`Work.KMTAreas.A7.isLqMultiplierBound_of_schwartzKernel_top`. -/

theorem etaMult_lqBound_finite {K : SchwartzMap ℝ ℂ} {φ : ℝ → ℂ} {M : NNReal} {q : ENNReal}
    (hφ : ∀ ξ : ℝ, FourierTransform.fourier (K : ℝ → ℂ) ξ = φ ξ)
    (hKM : eLpNorm (K : ℝ → ℂ) 1 volume ≤ ENNReal.ofReal (M : ℝ))
    (hq : 1 ≤ q) (hqt : q ≠ ⊤) : IsLqMultiplierBound q φ M := by
  intro f
  set p : ℝ := q.toReal with hpdef
  have hp1 : 1 ≤ p := by
    rw [hpdef, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hqt hq
  have hqeq : ENNReal.ofReal p = q := by rw [hpdef]; exact ENNReal.ofReal_toReal hqt
  have hconv := contMulOp_eq_convolution K φ hφ f
  rw [hconv]
  set K' : ℝ → ℝ≥0∞ := fun z => ‖(K : ℝ → ℂ) z‖ₑ with hK'
  set Φ : ℝ → ℝ≥0∞ := fun y => ‖(f : ℝ → ℂ) y‖ₑ with hΦ
  have hKae : AEMeasurable K' volume := by
    rw [hK']; exact (continuous_enorm.comp K.continuous).aemeasurable
  have hΦae : AEMeasurable Φ volume := by
    rw [hΦ]; exact (continuous_enorm.comp f.continuous).aemeasurable
  have hpt : ∀ x : ℝ,
      ‖MeasureTheory.convolution (f : ℝ → ℂ) (K : ℝ → ℂ) (ContinuousLinearMap.lsmul ℂ ℂ)
          volume x‖ₑ ≤ ∫⁻ t : ℝ, K' (x - t) * Φ t := by
    intro x
    rw [MeasureTheory.convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    apply lintegral_congr
    intro t
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul, hK', hΦ]
    rw [mul_comm]
  calc eLpNorm (fun x => MeasureTheory.convolution (f : ℝ → ℂ) (K : ℝ → ℂ)
          (ContinuousLinearMap.lsmul ℂ ℂ) volume x) q volume
      ≤ eLpNorm (fun x => ∫⁻ t : ℝ, K' (x - t) * Φ t) q volume :=
        eLpNorm_mono_enorm_ae (hf := by pw_aesm) (Eventually.of_forall hpt)
    _ = eLpNorm (fun x => ∫⁻ t : ℝ, K' (x - t) * Φ t) (ENNReal.ofReal p) volume := by rw [hqeq]
    _ ≤ eLpNorm K' (ENNReal.ofReal 1) volume * eLpNorm Φ (ENNReal.ofReal p) volume :=
        Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (p := p) (q := p) (r := 1)
          hp1 le_rfl (by ring) hKae hΦae
    _ = eLpNorm (K : ℝ → ℂ) 1 volume * eLpNorm (f : ℝ → ℂ) q volume := by
        rw [hK', hΦ, eLpNorm_enorm (hf := by pw_aesm), eLpNorm_enorm (hf := by pw_aesm), ENNReal.ofReal_one, hqeq]
    _ ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) q volume := by
        gcongr

/-! ## The multiplier bound -/

theorem EtaMult :
    ∃ M : NNReal, 0 < M ∧ ∀ (k : ℤ) (q : ENNReal), 1 ≤ q →
      Work.Analysis.IWMultiplier.IsLqMultiplierBound q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) M := by
  refine ⟨etaMult_M, etaMult_M_pos, ?_⟩
  intro k q hq
  rcases eq_or_ne q ⊤ with hqtop | hqt
  · subst hqtop
    exact isLqMultiplierBound_of_schwartzKernel_top (etaMult_K_fourier k) (etaMult_K_norm k)
  · exact etaMult_lqBound_finite (etaMult_K_fourier k) (etaMult_K_norm k) hq hqt

end Work.KMTAreas.A7
