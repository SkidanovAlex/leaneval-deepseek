import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Asymptotics.norm_Eisenstein_imagAxis_atZero
import Submission.Work.Asymptotics.MFix.KXiDefs

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-!
# The CKMRV kernel on the `E`-region of the contour at a coincidence

The target `Kaxis_Kfun_coincidence_E` bounds `‖Kaxis (Kfun ℓ d) w t‖` polynomially in
`scale w` on the cusp-`0` neighbourhood `E = KEpsilon` of CKMRV, under the coincidence
hypothesis `j(w) = j(it)`.

* For `d = 8` the kernel `Kfun` vanishes on every coincidence
  (`MiddleRange.KPlus_eight_eq_zero`, `MiddleRange.KMinus_eq_zero_of_coincidence`).
* For `d = 24` the coincidence forces `w = it` (`MiddleRange.eq_or_eq_S_of_re_eq_zero`),
  so the value is the *diagonal* value of the kernel on the imaginary axis.  That value is
  the explicit expression `τ²·Ξ(τ)/(c₀Δ(τ))` (`c0_mul_DeltaFun_mul_KPlus24_diag`), and each
  atom `E₄, E₆, E₂, (E₂|₂S), φ₀, φ₂` is bounded by a power of `(Im τ)⁻¹` near the cusp `0`
  (`norm_Eisenstein_imagAxis_atZero`, `MFix.E2Fun_bound`, `MFix.delta1_isBigOq`,
  `MFix.DeltaFun_lower`).
-/

/-! ## Auxiliary: the point `it` of the imaginary axis -/

private lemma kd_imagAxis_coe (s : ℝ) (hs : 0 < s) :
    ((Work.Kernels.imagAxis s hs : ℍ) : ℂ) = (s : ℂ) * Complex.I := rfl

private lemma kd_imagAxis_im (s : ℝ) (hs : 0 < s) :
    (Work.Kernels.imagAxis s hs : ℍ).im = s := by simp [Work.Kernels.imagAxis]

private lemma kd_imagAxis_norm (s : ℝ) (hs : 0 < s) :
    ‖((Work.Kernels.imagAxis s hs : ℍ) : ℂ)‖ = s := by
  rw [kd_imagAxis_coe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs]

private lemma kd_S_imagAxis (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) :=
  Work.Asymptotics.imagAxis_smul_S t ht

private lemma kd_Pi_norm : ‖(Real.pi : ℂ)‖ = Real.pi := by
  rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- `(t⁻¹) ^ (n+1) * t = (t⁻¹) ^ n`, i.e. the power identity behind every estimate below. -/
private lemma kd_inv_pow_mul (t : ℝ) (ht : 0 < t) (n : ℕ) :
    (t⁻¹) ^ (n + 1) * t = (t⁻¹) ^ n := by
  rw [pow_succ, mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), mul_one]

private lemma kd_u_le (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ t⁻¹ :=
  (one_le_inv₀ ht).mpr ht1

/-! ## Auxiliary: boundedness of `E₂` at the cusp `0` -/

private lemma kd_E2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ ≤ C * (t⁻¹) ^ 2 := by
  obtain ⟨A2E, hA2Epos, hA2E⟩ := Work.Asymptotics.MFix.E2Fun_bound
  refine ⟨A2E + 6 / Real.pi, by positivity, fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := kd_u_le t ht ht1
  set σ : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hσ
  have hσn : ‖(σ : ℂ)‖ = t⁻¹ := by rw [hσ]; exact kd_imagAxis_norm _ _
  have hσim : 1 ≤ σ.im := by rw [hσ, kd_imagAxis_im]; exact hu
  have hb : ‖Work.Kernels.E2Fun σ‖ ≤ A2E := hA2E σ hσim
  have hτ : Work.Kernels.imagAxis t ht = ModularGroup.S • σ := by
    rw [hσ, ← kd_S_imagAxis t ht]
    exact (S_smul_S_smul _).symm
  have heq : Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)
      = (σ : ℂ) ^ 2 * Work.Kernels.E2Fun σ
        - 6 * Complex.I * (σ : ℂ) / (Real.pi : ℂ) := by
    rw [hτ]; exact Work.Kernels.E2Fun_S_smul σ
  have hA : ‖(σ : ℂ) ^ 2 * Work.Kernels.E2Fun σ‖
      = ‖(σ : ℂ)‖ ^ 2 * ‖Work.Kernels.E2Fun σ‖ := by rw [norm_mul, norm_pow]
  have hB : ‖(6 : ℂ) * Complex.I * (σ : ℂ) / (Real.pi : ℂ)‖ = 6 * ‖(σ : ℂ)‖ / Real.pi := by
    rw [norm_div, kd_Pi_norm, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat]
  rw [heq]
  calc ‖(σ : ℂ) ^ 2 * Work.Kernels.E2Fun σ
          - 6 * Complex.I * (σ : ℂ) / (Real.pi : ℂ)‖
      ≤ ‖(σ : ℂ) ^ 2 * Work.Kernels.E2Fun σ‖
          + ‖(6 : ℂ) * Complex.I * (σ : ℂ) / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ = ‖(σ : ℂ)‖ ^ 2 * ‖Work.Kernels.E2Fun σ‖ + 6 * ‖(σ : ℂ)‖ / Real.pi := by rw [hA, hB]
    _ ≤ (t⁻¹) ^ 2 * A2E + 6 * (t⁻¹) / Real.pi := by
        rw [hσn]
        exact add_le_add (mul_le_mul_of_nonneg_left hb (by positivity)) le_rfl
    _ ≤ (A2E + 6 / Real.pi) * (t⁻¹) ^ 2 := by
        have h6 : (6 / Real.pi) * t⁻¹ ≤ (6 / Real.pi) * (t⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hu, sq_nonneg t⁻¹]) (by positivity)
        have h2 : 6 * (t⁻¹) / Real.pi = (6 / Real.pi) * t⁻¹ := by ring
        rw [h2]
        nlinarith [h6]

/-! ## Auxiliary: `φ₀` and `φ₂` at the cusp `0` -/

private lemma kd_phi0_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)‖ ≤ C * (t⁻¹) := by
  obtain ⟨CE, hCEpos, hCE⟩ := kd_E2_bound
  refine ⟨CE + 3 / Real.pi, by positivity, fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := kd_u_le t ht ht1
  have hb : ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ ≤ CE * (t⁻¹) ^ 2 := hCE t ht ht1
  have hc : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ = t := kd_imagAxis_norm t ht
  have hτn : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖
      = t * ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ := by rw [norm_mul, hc]
  have h3n : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, kd_Pi_norm]
  have hphi0 : Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)
      = ((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
          * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)
        - 3 * Complex.I / (Real.pi : ℂ) := rfl
  rw [hphi0]
  calc ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)
          - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖
          + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ = t * ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ + 3 / Real.pi := by rw [hτn, h3n]
    _ ≤ t * (CE * (t⁻¹) ^ 2) + 3 / Real.pi := by
        have := mul_le_mul_of_nonneg_left hb (le_of_lt ht)
        linarith
    _ ≤ (CE + 3 / Real.pi) * t⁻¹ := by
        have hEq : t * (CE * (t⁻¹) ^ 2) = CE * t⁻¹ := by
          have h1 : t * (CE * (t⁻¹) ^ 2) = CE * ((t⁻¹) ^ 2 * t) := by ring
          rw [h1, kd_inv_pow_mul t ht 1, pow_one]
        rw [hEq]
        have h3' : 3 / Real.pi ≤ (3 / Real.pi) * t⁻¹ := by
          have := mul_le_mul_of_nonneg_left hu (show (0:ℝ) ≤ 3 / Real.pi by positivity)
          simpa using this
        nlinarith [h3']

private lemma kd_phi2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)‖ ≤ C * (t⁻¹) ^ 3 := by
  obtain ⟨CE, hCEpos, hCE⟩ := kd_E2_bound
  refine ⟨CE ^ 2 + 6 * CE / Real.pi, by positivity, fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := kd_u_le t ht ht1
  have hb : ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ ≤ CE * (t⁻¹) ^ 2 := hCE t ht ht1
  have hc : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ = t := kd_imagAxis_norm t ht
  have h6n : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, kd_Pi_norm]
  have hphi2 : Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)
      = ((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
          * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht) ^ 2
        - ((6 : ℂ) * Complex.I / (Real.pi : ℂ))
          * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht) := rfl
  rw [hphi2]
  have hn : (0:ℝ) ≤ ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ := norm_nonneg _
  calc ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
          * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht) ^ 2
        - ((6 : ℂ) * Complex.I / (Real.pi : ℂ))
          * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖
      ≤ ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht) ^ 2‖
          + ‖((6 : ℂ) * Complex.I / (Real.pi : ℂ))
            * Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ := norm_sub_le _ _
    _ = t * ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ ^ 2
          + 6 / Real.pi * ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ := by
        rw [norm_mul, norm_mul, norm_pow, hc, h6n]
    _ ≤ t * (CE * (t⁻¹) ^ 2) ^ 2 + 6 / Real.pi * (CE * (t⁻¹) ^ 2) := by
        have h1 : ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ ^ 2
            ≤ (CE * (t⁻¹) ^ 2) ^ 2 := pow_le_pow_left₀ hn hb 2
        have h2 : t * ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖ ^ 2
            ≤ t * (CE * (t⁻¹) ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
        have h3 : 6 / Real.pi * ‖Work.Kernels.E2Fun (Work.Kernels.imagAxis t ht)‖
            ≤ 6 / Real.pi * (CE * (t⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hb (by positivity)
        linarith
    _ ≤ (CE ^ 2 + 6 * CE / Real.pi) * (t⁻¹) ^ 3 := by
        have hEq1 : t * (CE * (t⁻¹) ^ 2) ^ 2 = CE ^ 2 * (t⁻¹) ^ 3 := by
          have h1 : (CE * (t⁻¹) ^ 2) ^ 2 = CE ^ 2 * (t⁻¹) ^ 4 := by ring
          rw [h1, mul_comm t (CE ^ 2 * (t⁻¹) ^ 4), mul_assoc, kd_inv_pow_mul t ht 3]
        have hEq2 : 6 / Real.pi * (CE * (t⁻¹) ^ 2) = 6 * CE / Real.pi * (t⁻¹) ^ 2 := by ring
        rw [hEq1, hEq2]
        have hu3 : (t⁻¹) ^ 2 ≤ (t⁻¹) ^ 3 := by
          calc (t⁻¹) ^ 2 = (t⁻¹) ^ 2 * 1 := (mul_one _).symm
            _ ≤ (t⁻¹) ^ 2 * t⁻¹ := mul_le_mul_of_nonneg_left hu (by positivity)
            _ = (t⁻¹) ^ 3 := by ring
        have h6c : 6 * CE / Real.pi * (t⁻¹) ^ 2 ≤ 6 * CE / Real.pi * (t⁻¹) ^ 3 :=
          mul_le_mul_of_nonneg_left hu3 (by positivity)
        have hexp : (CE ^ 2 + 6 * CE / Real.pi) * (t⁻¹) ^ 3
            = CE ^ 2 * (t⁻¹) ^ 3 + (6 * CE / Real.pi) * (t⁻¹) ^ 3 := by ring
        rw [hexp]
        linarith

/-! ## Auxiliary: the difference `E₄ − (E₂|₂S)²` versus `Δ` at the cusp -/

private lemma kd_diff_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
          - Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2‖
        ≤ C * (t⁻¹) ^ 4 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨cΔ, hcΔpos, hcΔ⟩ := Work.Asymptotics.MFix.DeltaFun_lower
  obtain ⟨Cd, hCdpos, hCd⟩ := Work.Asymptotics.MFix.delta1_isBigOq
  refine ⟨Cd / cΔ, by positivity, fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := kd_u_le t ht ht1
  set σ : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hσ
  have hσn : ‖(σ : ℂ)‖ = t⁻¹ := by rw [hσ]; exact kd_imagAxis_norm _ _
  have hσim : 1 ≤ σ.im := by rw [hσ, kd_imagAxis_im]; exact hu
  have hτ : Work.Kernels.imagAxis t ht = ModularGroup.S • σ := by
    rw [hσ, ← kd_S_imagAxis t ht]
    exact (S_smul_S_smul _).symm
  have hb1 : ‖Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2‖
      ≤ Cd * ‖Work.Kernels.qParamFun σ‖ := by
    simpa using hCd σ hσim
  have hb2 : cΔ * ‖Work.Kernels.qParamFun σ‖ ≤ ‖Work.Kernels.DeltaFun σ‖ := hcΔ σ hσim
  have hE4 : Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
      = (σ : ℂ) ^ 4 * Work.Kernels.E4Fun σ := by
    rw [hτ]
    exact Work.Kernels.KernelFacts.kpc_smul_S_of_slash
      Work.Kernels.KernelFacts.kpc_E4_slash_S σ
  have hE2S : Work.Kernels.E2S (Work.Kernels.imagAxis t ht)
      = (σ : ℂ) ^ 2 * Work.Kernels.E2Fun σ := by
    rw [hτ]; exact Work.Kernels.TildeFacts.E2S_S_smul σ
  have hD : Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
      = (σ : ℂ) ^ 12 * Work.Kernels.DeltaFun σ := by
    rw [hτ]
    exact Work.Kernels.KernelFacts.kpc_smul_S_of_slash
      Work.Kernels.KernelFacts.kpc_Delta_slash_S σ
  have hfact : Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
      - Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2
      = (σ : ℂ) ^ 4 * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2) := by
    rw [hE4, hE2S]; ring
  have hDlow : cΔ * (t⁻¹) ^ 12 * ‖Work.Kernels.qParamFun σ‖
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
    rw [hD, norm_mul, norm_pow, hσn]
    calc cΔ * (t⁻¹) ^ 12 * ‖Work.Kernels.qParamFun σ‖
        = (t⁻¹) ^ 12 * (cΔ * ‖Work.Kernels.qParamFun σ‖) := by ring
      _ ≤ (t⁻¹) ^ 12 * ‖Work.Kernels.DeltaFun σ‖ :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
  rw [hfact, norm_mul, norm_pow, hσn]
  have step1 : (t⁻¹) ^ 4 * ‖Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2‖
      ≤ (t⁻¹) ^ 4 * (Cd * ‖Work.Kernels.qParamFun σ‖) :=
    mul_le_mul_of_nonneg_left hb1 (by positivity)
  have hqle : ‖Work.Kernels.qParamFun σ‖
      ≤ t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ / cΔ := by
    rw [le_div_iff₀ hcΔpos]
    have huu : (t⁻¹) ^ 12 * t ^ 12 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt ht), one_pow]
    have h3 : cΔ * (t⁻¹) ^ 12 * ‖Work.Kernels.qParamFun σ‖ * t ^ 12
        = cΔ * ‖Work.Kernels.qParamFun σ‖ := by
      calc cΔ * (t⁻¹) ^ 12 * ‖Work.Kernels.qParamFun σ‖ * t ^ 12
          = cΔ * ‖Work.Kernels.qParamFun σ‖ * ((t⁻¹) ^ 12 * t ^ 12) := by ring
        _ = cΔ * ‖Work.Kernels.qParamFun σ‖ * 1 := by rw [huu]
        _ = cΔ * ‖Work.Kernels.qParamFun σ‖ := by ring
    calc ‖Work.Kernels.qParamFun σ‖ * cΔ
        = cΔ * (t⁻¹) ^ 12 * ‖Work.Kernels.qParamFun σ‖ * t ^ 12 := by
          rw [h3]; ring
      _ ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ * t ^ 12 :=
          mul_le_mul_of_nonneg_right hDlow (by positivity)
      _ = t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by ring
  calc (t⁻¹) ^ 4 * ‖Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2‖
      ≤ (t⁻¹) ^ 4 * (Cd * ‖Work.Kernels.qParamFun σ‖) := step1
    _ ≤ (t⁻¹) ^ 4 * (Cd * (t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ / cΔ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hqle hCdpos.le
    _ ≤ (Cd / cΔ) * (t⁻¹) ^ 4 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
        have ht12 : t ^ 12 ≤ 1 := pow_le_one₀ (le_of_lt ht) ht1
        have hu4 : (0:ℝ) ≤ (t⁻¹) ^ 4 := by positivity
        have hDn : (0:ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := norm_nonneg _
        have hEq : (t⁻¹) ^ 4 * (Cd * (t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ / cΔ))
            = (Cd / cΔ) * (t⁻¹) ^ 4 * t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
          ring
        rw [hEq]
        have hmono : (t⁻¹) ^ 4 * t ^ 12 ≤ (t⁻¹) ^ 4 := by
          simpa using mul_le_mul_of_nonneg_left ht12 hu4
        have hK : (0:ℝ) ≤ Cd / cΔ := by positivity
        nlinarith [hmono, hK, mul_nonneg (mul_nonneg hK hu4) hDn, hDn]

/-! ## Auxiliary: the numerator `Ξ = diagX` at the cusp -/

private lemma kd_W_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Asymptotics.diagW (Work.Kernels.imagAxis t ht)‖ ≤ C * (t⁻¹) ^ 9 := by
  obtain ⟨A4, hA4pos, hA4⟩ := (Work.Asymptotics.norm_Eisenstein_imagAxis_atZero).1
  obtain ⟨A6, hA6pos, hA6⟩ := (Work.Asymptotics.norm_Eisenstein_imagAxis_atZero).2.1
  obtain ⟨C1, hC1pos, hC1⟩ := kd_phi0_bound
  obtain ⟨C2, hC2pos, hC2⟩ := kd_phi2_bound
  refine ⟨A6 * (A4 + C2) + 2 * A4 ^ 2 * C1, by positivity, fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := kd_u_le t ht ht1
  have hE4 : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ≤ A4 * (t⁻¹) ^ 4 := by
    simpa only [inv_pow] using hA4 t ht ht1
  have hE6 : ‖Work.Kernels.E6Fun (Work.Kernels.imagAxis t ht)‖ ≤ A6 * (t⁻¹) ^ 6 := by
    simpa only [inv_pow] using hA6 t ht ht1
  have hp0 : ‖Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)‖ ≤ C1 * t⁻¹ := hC1 t ht ht1
  have hp2 : ‖Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)‖ ≤ C2 * (t⁻¹) ^ 3 := hC2 t ht ht1
  have hpm2 : ‖Work.Kernels.phiNeg2 (Work.Kernels.imagAxis t ht)‖ = t := by
    simp only [Work.Kernels.phiNeg2]
    exact kd_imagAxis_norm t ht
  rw [Work.Asymptotics.diagW]
  have hA : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
        * Work.Kernels.phiNeg2 (Work.Kernels.imagAxis t ht)
      + Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)‖
      ≤ A4 * (t⁻¹) ^ 4 * t + C2 * (t⁻¹) ^ 3 := by
    calc ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
          * Work.Kernels.phiNeg2 (Work.Kernels.imagAxis t ht)
        + Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)‖
        ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
            * Work.Kernels.phiNeg2 (Work.Kernels.imagAxis t ht)‖
          + ‖Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)‖ := norm_add_le _ _
      _ = ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ * t
          + ‖Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)‖ := by rw [norm_mul, hpm2]
      _ ≤ A4 * (t⁻¹) ^ 4 * t + C2 * (t⁻¹) ^ 3 :=
          add_le_add (mul_le_mul_of_nonneg_right hE4 (le_of_lt ht)) hp2
  refine le_trans (norm_sub_le (Work.Kernels.E6Fun (Work.Kernels.imagAxis t ht)
      * (Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
          * Work.Kernels.phiNeg2 (Work.Kernels.imagAxis t ht)
        + Work.Kernels.phi2 (Work.Kernels.imagAxis t ht)))
      (2 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 2
        * Work.Kernels.phi0 (Work.Kernels.imagAxis t ht))) ?_
  have hB : ‖Work.Kernels.E6Fun (Work.Kernels.imagAxis t ht)
        * (Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
            * Work.Kernels.phiNeg2 (Work.Kernels.imagAxis t ht)
          + Work.Kernels.phi2 (Work.Kernels.imagAxis t ht))‖
      ≤ A6 * (t⁻¹) ^ 6 * (A4 * (t⁻¹) ^ 4 * t + C2 * (t⁻¹) ^ 3) :=
    le_trans (le_of_eq (by rw [norm_mul]))
      (mul_le_mul hE6 hA (norm_nonneg _) (by positivity))
  have hC : ‖2 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 2
        * Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)‖
      ≤ 2 * (A4 * (t⁻¹) ^ 4) ^ 2 * (C1 * t⁻¹) := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hE4 2)
      (by norm_num)) hp0 (norm_nonneg _) (by positivity)
  refine le_trans (add_le_add hB hC) ?_
  rw [show A4 * (t⁻¹) ^ 4 * t = A4 * (t⁻¹) ^ 3 from by
    rw [mul_assoc, kd_inv_pow_mul t ht 3]]
  have hEq : A6 * (t⁻¹) ^ 6 * (A4 * (t⁻¹) ^ 3 + C2 * (t⁻¹) ^ 3)
        + 2 * (A4 * (t⁻¹) ^ 4) ^ 2 * (C1 * t⁻¹)
      = (A6 * (A4 + C2)) * (t⁻¹) ^ 9 + (2 * A4 ^ 2 * C1) * (t⁻¹) ^ 9 := by ring
  rw [hEq, add_mul]

/-! ## Auxiliary: the numerator `Ξ = diagX` versus `Δ` at the cusp -/

private lemma kd_pow_le {u : ℝ} (hu : 1 ≤ u) {a b : ℕ} (hab : a ≤ b) : u ^ a ≤ u ^ b :=
  pow_le_pow_right₀ hu hab

private lemma kd_X_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Asymptotics.diagX (Work.Kernels.imagAxis t ht)‖
        ≤ C * (t⁻¹) ^ 17 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨A4, hA4pos, hA4⟩ := (Work.Asymptotics.norm_Eisenstein_imagAxis_atZero).1
  obtain ⟨A2S, hA2Spos, hA2S⟩ := (Work.Asymptotics.norm_Eisenstein_imagAxis_atZero).2.2
  obtain ⟨C1, hC1pos, hC1⟩ := kd_phi0_bound
  obtain ⟨CD, hCDpos, hCD⟩ := kd_diff_bound
  obtain ⟨CW, hCWpos, hCW⟩ := kd_W_bound
  refine ⟨6 * A4 * CD * CW + 1728 * C1 * (5 * A4 + 7 * A2S ^ 2), by positivity,
    fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := kd_u_le t ht ht1
  have hE4 : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ≤ A4 * (t⁻¹) ^ 4 := by
    simpa only [inv_pow] using hA4 t ht ht1
  have hE2S : ‖Work.Kernels.E2S (Work.Kernels.imagAxis t ht)‖ ≤ A2S * (t⁻¹) ^ 2 := by
    simpa only [inv_pow] using hA2S t ht ht1
  have hp0 : ‖Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)‖ ≤ C1 * t⁻¹ := hC1 t ht ht1
  have hD : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
        - Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2‖
      ≤ CD * (t⁻¹) ^ 4 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := hCD t ht ht1
  have hW : ‖Work.Asymptotics.diagW (Work.Kernels.imagAxis t ht)‖ ≤ CW * (t⁻¹) ^ 9 :=
    hCW t ht ht1
  have hDn : (0:ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := norm_nonneg _
  have h5 : ‖5 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
        - 7 * Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2‖
      ≤ (5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 4 := by
    have hnn : (0:ℝ) ≤ ‖Work.Kernels.E2S (Work.Kernels.imagAxis t ht)‖ := norm_nonneg _
    calc ‖5 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
          - 7 * Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2‖
        ≤ ‖5 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖
          + ‖7 * Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2‖ := norm_sub_le _ _
      _ = 5 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖
          + 7 * ‖Work.Kernels.E2S (Work.Kernels.imagAxis t ht)‖ ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_ofNat]
      _ ≤ 5 * (A4 * (t⁻¹) ^ 4) + 7 * (A2S * (t⁻¹) ^ 2) ^ 2 := by
          refine add_le_add (mul_le_mul_of_nonneg_left hE4 (by norm_num)) ?_
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hE2S 2) (by norm_num)
      _ = (5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 4 := by ring
  rw [Work.Asymptotics.diagX]
  refine le_trans (norm_add_le
    (6 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
      * (Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
        - Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2)
      * Work.Asymptotics.diagW (Work.Kernels.imagAxis t ht))
    (1728 * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
      * Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)
      * (5 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
        - 7 * Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2))) ?_
  have hP1 : ‖6 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
        * (Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
          - Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2)
        * Work.Asymptotics.diagW (Work.Kernels.imagAxis t ht)‖
      ≤ 6 * A4 * CD * CW * (t⁻¹) ^ 17
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    calc 6 * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖
          * ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
            - Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2‖
          * ‖Work.Asymptotics.diagW (Work.Kernels.imagAxis t ht)‖
        ≤ 6 * (A4 * (t⁻¹) ^ 4) * (CD * (t⁻¹) ^ 4
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖)
          * (CW * (t⁻¹) ^ 9) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hE4 (by norm_num)) hD
            (norm_nonneg _) (by positivity)) hW (norm_nonneg _) (by positivity)
      _ = 6 * A4 * CD * CW * (t⁻¹) ^ 17
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by ring
  have hP2 : ‖1728 * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
        * Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)
        * (5 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
          - 7 * Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2)‖
      ≤ 1728 * C1 * (5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 5
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    calc 1728 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
          * ‖Work.Kernels.phi0 (Work.Kernels.imagAxis t ht)‖
          * ‖5 * Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)
            - 7 * Work.Kernels.E2S (Work.Kernels.imagAxis t ht) ^ 2‖
        ≤ 1728 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ * (C1 * t⁻¹)
          * ((5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 4) := by
          refine mul_le_mul (mul_le_mul (le_refl _) hp0 (norm_nonneg _) (by positivity)) h5
            (norm_nonneg _) (by positivity)
      _ = 1728 * C1 * (5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 5
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by ring
  refine le_trans (add_le_add hP1 hP2) ?_
  have hu5 : (t⁻¹) ^ 5 ≤ (t⁻¹) ^ 17 := kd_pow_le hu (by norm_num)
  have hK1 : (0:ℝ) ≤ 6 * A4 * CD * CW := by positivity
  have hK2 : (0:ℝ) ≤ 1728 * C1 * (5 * A4 + 7 * A2S ^ 2) := by positivity
  have hcomb : 6 * A4 * CD * CW * (t⁻¹) ^ 17
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      + 1728 * C1 * (5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 5
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      = (6 * A4 * CD * CW * (t⁻¹) ^ 17
          + 1728 * C1 * (5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 5)
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by ring
  rw [hcomb]
  have hexp : (6 * A4 * CD * CW + 1728 * C1 * (5 * A4 + 7 * A2S ^ 2)) * (t⁻¹) ^ 17
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      = (6 * A4 * CD * CW * (t⁻¹) ^ 17
          + 1728 * C1 * (5 * A4 + 7 * A2S ^ 2) * (t⁻¹) ^ 17)
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by ring
  rw [hexp]
  refine mul_le_mul_of_nonneg_right (add_le_add (le_refl _) ?_) hDn
  exact mul_le_mul_of_nonneg_left hu5 hK2

/-! ## Auxiliary: `K₊^{(24)}` and `K^{(24)}` on the diagonal at the cusp -/

private lemma kd_c0_ne : Work.Asymptotics.c0 ≠ 0 := by
  rw [Work.Asymptotics.c0, show Work.Kernels.c1728 = (1728 : ℂ) from rfl]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
      (zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    Complex.I_ne_zero

private lemma kd_KPlus_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.KPlus 24 (Work.Kernels.imagAxis t ht) (Work.Kernels.imagAxis t ht)‖
        ≤ C * (t⁻¹) ^ 17 := by
  obtain ⟨CX, hCXpos, hCX⟩ := kd_X_bound
  have hc0pos : 0 < ‖Work.Asymptotics.c0‖ := norm_pos_iff.mpr kd_c0_ne
  refine ⟨CX / ‖Work.Asymptotics.c0‖, by positivity, fun t ht ht1 => ?_⟩
  set τ : ℍ := Work.Kernels.imagAxis t ht with hτ
  have hDne : ‖Work.Kernels.DeltaFun τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  have hid := Work.Asymptotics.c0_mul_DeltaFun_mul_KPlus24_diag τ
  have hnorm : ‖Work.Kernels.KPlus 24 τ τ‖ * (‖Work.Asymptotics.c0‖ * ‖Work.Kernels.DeltaFun τ‖)
      = ‖(τ : ℂ)‖ ^ 2 * ‖Work.Asymptotics.diagX τ‖ := by
    have h1 : ‖Work.Asymptotics.c0 * (Work.Kernels.DeltaFun τ * Work.Kernels.KPlus 24 τ τ)‖
        = ‖(τ : ℂ) ^ 2 * Work.Asymptotics.diagX τ‖ := by rw [hid]
    have h2 : ‖Work.Asymptotics.c0 * (Work.Kernels.DeltaFun τ * Work.Kernels.KPlus 24 τ τ)‖
        = ‖Work.Asymptotics.c0‖ * (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.KPlus 24 τ τ‖) := by
      rw [norm_mul (Work.Asymptotics.c0) (Work.Kernels.DeltaFun τ * Work.Kernels.KPlus 24 τ τ),
        norm_mul (Work.Kernels.DeltaFun τ) (Work.Kernels.KPlus 24 τ τ)]
    have h3 : ‖(τ : ℂ) ^ 2 * Work.Asymptotics.diagX τ‖
        = ‖(τ : ℂ)‖ ^ 2 * ‖Work.Asymptotics.diagX τ‖ := by
      rw [norm_mul ((τ : ℂ) ^ 2) (Work.Asymptotics.diagX τ), norm_pow]
    rw [show ‖Work.Kernels.KPlus 24 τ τ‖ * (‖Work.Asymptotics.c0‖ * ‖Work.Kernels.DeltaFun τ‖)
        = ‖Work.Asymptotics.c0‖ * (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.KPlus 24 τ τ‖)
        from by ring,
      ← h2, h1, h3]
  have hτn : ‖(τ : ℂ)‖ = t := by rw [hτ]; exact kd_imagAxis_norm t ht
  have hX := hCX t ht ht1
  rw [← hτ] at hX
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt ht) ht1
  have hmain : ‖Work.Kernels.KPlus 24 τ τ‖ * (‖Work.Asymptotics.c0‖ * ‖Work.Kernels.DeltaFun τ‖)
      ≤ CX * (t⁻¹) ^ 17 * ‖Work.Kernels.DeltaFun τ‖ := by
    rw [hnorm, hτn]
    calc t ^ 2 * ‖Work.Asymptotics.diagX τ‖
        ≤ 1 * (CX * (t⁻¹) ^ 17 * ‖Work.Kernels.DeltaFun τ‖) := by
          rw [one_mul]
          calc t ^ 2 * ‖Work.Asymptotics.diagX τ‖ ≤ 1 * ‖Work.Asymptotics.diagX τ‖ :=
                mul_le_mul_of_nonneg_right ht2 (norm_nonneg _)
            _ = ‖Work.Asymptotics.diagX τ‖ := one_mul _
            _ ≤ CX * (t⁻¹) ^ 17 * ‖Work.Kernels.DeltaFun τ‖ := hX
      _ = CX * (t⁻¹) ^ 17 * ‖Work.Kernels.DeltaFun τ‖ := one_mul _
  have hrhs : (CX / ‖Work.Asymptotics.c0‖) * (t⁻¹) ^ 17
        * (‖Work.Asymptotics.c0‖ * ‖Work.Kernels.DeltaFun τ‖)
      = CX * (t⁻¹) ^ 17 * ‖Work.Kernels.DeltaFun τ‖ := by
    field_simp [hc0pos.ne']
  rw [← hrhs] at hmain
  exact le_of_mul_le_mul_right hmain (mul_pos hc0pos (norm_pos_iff.mpr
    (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)))

private lemma kd_key (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.Kfun ℓ 24 (Work.Kernels.imagAxis t ht) (Work.Kernels.imagAxis t ht)‖
        ≤ C * (t⁻¹) ^ 17 := by
  obtain ⟨CK, hCKpos, hCK⟩ := kd_KPlus_bound ℓ
  refine ⟨CK / 2, by positivity, fun t ht ht1 => ?_⟩
  have hK : Work.Kernels.Kfun ℓ 24 (Work.Kernels.imagAxis t ht) (Work.Kernels.imagAxis t ht)
      = Work.Kernels.KPlus 24 (Work.Kernels.imagAxis t ht) (Work.Kernels.imagAxis t ht) / 2 := by
    rw [Work.Kernels.Kfun,
      Work.Asymptotics.MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inr rfl) rfl, add_zero]
  rw [hK, norm_div, Complex.norm_ofNat]
  have h := hCK t ht ht1
  linarith

theorem Kaxis_Kfun_coincidence_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ c N' : ℝ, 0 ≤ c ∧ 0 ≤ N' ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c * (Work.Kernels.scale w) ^ N' := by
  rcases hd with rfl | rfl
  · refine ⟨1, 0, zero_le_one, le_rfl, ?_⟩
    intro w t ht hw ht1 hcoin
    have hz : Work.Kernels.Kfun ℓ 8 w (Work.Kernels.imagAxis t ht) = 0 := by
      rw [Work.Kernels.Kfun, Work.Asymptotics.MiddleRange.KPlus_eight_eq_zero hcoin,
        Work.Asymptotics.MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inl rfl) hcoin,
        add_zero, zero_div]
    rw [Work.Kernels.Kaxis, dif_pos ht, hz, norm_zero]
    simp
  · obtain ⟨C, hCpos, hC⟩ := kd_key ℓ
    refine ⟨C, ((17 : ℕ) : ℝ), hCpos.le, by norm_num, ?_⟩
    intro w t ht hw ht1 hcoin
    have hw_eq : w = Work.Kernels.imagAxis t ht := by
      have hzre : (((Work.Kernels.imagAxis t ht : ℍ) : ℂ)).re = 0 := by
        simp [Work.Kernels.imagAxis]
      rcases Work.Asymptotics.eq_or_eq_S_of_re_eq_zero hw.1 hzre hcoin with h | h
      · exact h.symm
      · exfalso
        have h2 : 2 ≤ (Work.Kernels.imagAxis t ht).im := by rw [h]; exact hw.2
        simp [Work.Kernels.imagAxis] at h2
        linarith
    rw [Work.Kernels.Kaxis, dif_pos ht, hw_eq]
    refine le_trans (hC t ht ht1) ?_
    have hscale : t⁻¹ ≤ Work.Kernels.scale (Work.Kernels.imagAxis t ht) := by
      rw [Work.Kernels.scale]
      have him : (Work.Kernels.imagAxis t ht).im = t := kd_imagAxis_im t ht
      rw [him]
      have hnn : (0:ℝ) ≤ ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ := norm_nonneg _
      linarith
    have h17 : (t⁻¹) ^ 17 ≤ (Work.Kernels.scale (Work.Kernels.imagAxis t ht)) ^ 17 :=
      pow_le_pow_left₀ (by positivity) hscale 17
    calc C * (t⁻¹) ^ 17
        ≤ C * (Work.Kernels.scale (Work.Kernels.imagAxis t ht)) ^ 17 :=
          mul_le_mul_of_nonneg_left h17 hCpos.le
      _ = C * (Work.Kernels.scale (Work.Kernels.imagAxis t ht)) ^ ((17 : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]

end

end Work.Asymptotics
