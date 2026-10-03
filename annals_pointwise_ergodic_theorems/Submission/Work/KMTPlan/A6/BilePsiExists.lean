import Mathlib
import Submission.Work.Analysis.InverseTheory.Basic
import Submission.Work.KMTPlan.A6.ELpNormTwoEqOfRealSqrtIntegral

/-!
# Existence of the window `ψ` of the `bile` lifting argument (target `BilePsiExists`)

The paper's Proposition `bile-2` needs a fixed Schwartz window `ψ : 𝒮(ℝ, ℂ)` whose Fourier
transform is supported in `[-1, 1]`, normalised so that `‖ψ‖_{L²} = 1`.

The construction is the classical one: take a smooth bump `g` supported in the closed unit ball
with `g 0 = 1`, and let `ψ` be the *inverse* Fourier transform of `g`, rescaled by the inverse of
its `L²` norm.  Then

* `𝓕 ψ = c · g` by Fourier inversion (`𝓕 ∘ 𝓕⁻ = id` on `𝒮(ℝ, ℂ)`), hence `𝓕 ψ` vanishes for
  `|ξ| > 1`;
* the rescaling makes `∫ ‖ψ‖² = 1`, whence `eLpNorm ψ 2 volume = 1` by
  `ELpNormTwoEqOfRealSqrtIntegral`.

The two `ℝ`-calculus inputs are isolated below: `schwartz_integral_normSq_pos` (a nonzero
Schwartz function has a positive `L²` mass) and `integral_normSq_const_smul` (the `L²` mass
scales quadratically).
-/

open scoped FourierTransform Topology
open Filter MeasureTheory

namespace Work.KMTPlan.A6

/-! ## Two `L²`-calculus lemmas -/

/-- A Schwarz function which is not identically zero has strictly positive `L²` mass. -/
lemma schwartz_integral_normSq_pos (f : SchwartzMap ℝ ℂ)
    (hf : ∃ x : ℝ, (f : ℝ → ℂ) x ≠ 0) :
    0 < ∫ t : ℝ, ‖(f : ℝ → ℂ) t‖ ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := hf
  set F : ℝ → ℝ := fun t => ‖(f : ℝ → ℂ) t‖ ^ 2 with hF
  have hFapply : ∀ t : ℝ, F t = ‖(f : ℝ → ℂ) t‖ ^ 2 := fun t => congrFun hF t
  have hcont : Continuous F := by
    rw [hF]
    exact (f.continuous.norm).pow 2
  have hint : Integrable F volume := by
    rw [hF]
    exact (f.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hnn : 0 ≤ᵐ[volume] F := Filter.Eventually.of_forall fun t => by positivity
  have hx₀pos : 0 < F x₀ := by
    rw [hFapply x₀]
    exact pow_pos (norm_pos_iff.mpr hx₀) 2
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnn hint]
  -- `F` is positive on a ball around `x₀`, and that ball has positive measure.
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε > 0, ∀ y : ℝ, dist y x₀ < ε → 0 < F y := by
    have hcontAt : ContinuousAt F x₀ := hcont.continuousAt
    have hmem : F ⁻¹' (Set.Ioi 0) ∈ 𝓝 x₀ :=
      hcontAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx₀pos)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨ε, hεpos, fun y hy => hε (Metric.mem_ball.mpr hy)⟩
  have hball : Metric.ball x₀ ε ⊆ Function.support F := by
    intro y hy
    rw [Function.mem_support]
    exact ne_of_gt (hε y (Metric.mem_ball.mp hy))
  have hbpos : 0 < volume (Metric.ball x₀ ε) := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact lt_of_lt_of_le hbpos (MeasureTheory.measure_mono hball)

/-- The `L²` mass of a Schwarz function scales by the square of the real scalar. -/
lemma integral_normSq_const_smul (c : ℝ) (f : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, ‖(c : ℂ) * (f : ℝ → ℂ) t‖ ^ 2) = c ^ 2 * ∫ t : ℝ, ‖(f : ℝ → ℂ) t‖ ^ 2 := by
  have hpt : ∀ t : ℝ, ‖(c : ℂ) * (f : ℝ → ℂ) t‖ ^ 2 = c ^ 2 * ‖(f : ℝ → ℂ) t‖ ^ 2 := by
    intro t
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul]

/-! ## A smooth bump supported in the closed unit ball -/

/-- A fixed smooth bump: `1` on `[-1/2, 1/2]`, `0` outside `(-1, 1)`. -/
noncomputable def psiBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

lemma psiBump_rOut : psiBump.rOut = 1 := rfl

/-- The bump as a `ℂ`-valued function. -/
noncomputable def psiBumpFun : ℝ → ℂ := fun x => ((psiBump x : ℝ) : ℂ)

lemma psiBumpFun_zero_of_one_le_abs {x : ℝ} (h : 1 ≤ |x|) : psiBumpFun x = 0 := by
  have hd : psiBump.rOut ≤ dist x 0 := by
    rw [psiBump_rOut, dist_zero_right, Real.norm_eq_abs]
    exact h
  simp [psiBumpFun, ContDiffBump.zero_of_le_dist psiBump hd]

lemma psiBumpFun_one : psiBumpFun 0 = 1 := by
  have h : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) psiBump.rIn := by
    rw [Metric.mem_closedBall, dist_self]
    exact psiBump.rIn_pos.le
  simp [psiBumpFun, ContDiffBump.one_of_mem_closedBall psiBump h]

lemma psiBumpFun_cs : HasCompactSupport psiBumpFun :=
  psiBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)

lemma psiBumpFun_cd : ContDiff ℝ (⊤ : ℕ∞) psiBumpFun :=
  Complex.ofRealCLM.contDiff.comp (ContDiffBump.contDiff psiBump (n := ⊤))

/-- The bump, bundled as a Schwartz function. -/
noncomputable def psiG : SchwartzMap ℝ ℂ := psiBumpFun_cs.toSchwartzMap psiBumpFun_cd

lemma psiG_coe : (psiG : ℝ → ℂ) = psiBumpFun :=
  funext fun x => HasCompactSupport.toSchwartzMap_toFun _ _ x

lemma psiG_zero_of_one_le_abs {x : ℝ} (h : 1 ≤ |x|) : (psiG : ℝ → ℂ) x = 0 := by
  rw [psiG_coe, psiBumpFun_zero_of_one_le_abs h]

lemma psiG_zero_of_one_lt_abs {x : ℝ} (h : 1 < |x|) : (psiG : ℝ → ℂ) x = 0 :=
  psiG_zero_of_one_le_abs h.le

lemma psiG_zero_zero : (psiG : ℝ → ℂ) 0 = 1 := by
  rw [psiG_coe, psiBumpFun_one]

lemma psiG_ne_zero : psiG ≠ 0 := by
  intro h
  have h0 : (psiG : ℝ → ℂ) 0 = 0 := by simp [h]
  rw [psiG_zero_zero] at h0
  exact one_ne_zero h0

/-! ## The inverse Fourier transform, rescaled -/

/-- The inverse Fourier transform of the bump. -/
noncomputable def psi0 : SchwartzMap ℝ ℂ := 𝓕⁻ psiG

lemma fourier_psi0 : 𝓕 psi0 = psiG := FourierTransform.fourier_fourierInv_eq psiG

/-- `psi0` is not the zero function (its Fourier transform is the bump, which is `1` at `0`). -/
lemma psi0_exists_ne : ∃ x : ℝ, (psi0 : ℝ → ℂ) x ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have h0 : psi0 = 0 := SchwartzMap.ext fun x => h x
  have hF : 𝓕 psi0 = (0 : SchwartzMap ℝ ℂ) := by
    rw [h0]
    exact FourierTransform.fourier_zero
  rw [fourier_psi0] at hF
  exact psiG_ne_zero hF

lemma psi0_integral_pos : 0 < ∫ t : ℝ, ‖(psi0 : ℝ → ℂ) t‖ ^ 2 :=
  schwartz_integral_normSq_pos psi0 psi0_exists_ne

/-- The normalising scalar: the inverse of the `L²` norm of `psi0`. -/
noncomputable def psiScale : ℝ := (Real.sqrt (∫ t : ℝ, ‖(psi0 : ℝ → ℂ) t‖ ^ 2))⁻¹

/-- The normalised window. -/
noncomputable def psiFinal : SchwartzMap ℝ ℂ := (psiScale : ℂ) • psi0

lemma psiFinal_coe : (psiFinal : ℝ → ℂ) = fun t => (psiScale : ℂ) * (psi0 : ℝ → ℂ) t := by
  funext t
  rw [psiFinal, IsSMulApply.smul_apply, smul_eq_mul]

lemma psiFinal_integral : (∫ t : ℝ, ‖(psiFinal : ℝ → ℂ) t‖ ^ 2) = 1 := by
  rw [psiFinal_coe, integral_normSq_const_smul]
  have hI : 0 < ∫ t : ℝ, ‖(psi0 : ℝ → ℂ) t‖ ^ 2 := psi0_integral_pos
  rw [psiScale, inv_pow, Real.sq_sqrt hI.le, inv_mul_cancel₀ (ne_of_gt hI)]

lemma psiFinal_eLpNorm : MeasureTheory.eLpNorm (psiFinal : ℝ → ℂ) 2 MeasureTheory.volume = 1 := by
  rw [ELpNormTwoEqOfRealSqrtIntegral psiFinal, psiFinal_integral]
  simp

lemma psiFinal_fourier_zero {ξ : ℝ} (hξ : 1 < |ξ|) :
    Work.Analysis.InverseTheory.realFourier (psiFinal : ℝ → ℂ) ξ = 0 := by
  rw [Work.Analysis.InverseTheory.realFourier_coe]
  have hsmul : 𝓕 psiFinal = (psiScale : ℂ) • psiG := by
    rw [psiFinal, FourierTransform.fourier_smul, fourier_psi0]
  rw [hsmul, IsSMulApply.smul_apply, smul_eq_mul, psiG_zero_of_one_lt_abs hξ, mul_zero]

/-! ## The target -/

theorem BilePsiExists :
    ∃ ψ : SchwartzMap ℝ ℂ,
      (∀ ξ : ℝ, 1 < |ξ| → Work.Analysis.InverseTheory.realFourier (ψ : ℝ → ℂ) ξ = 0) ∧
      MeasureTheory.eLpNorm (ψ : ℝ → ℂ) 2 MeasureTheory.volume = 1 ∧
      (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖ ^ 2 = 1) :=
  ⟨psiFinal, fun _ hξ => psiFinal_fourier_zero hξ, psiFinal_eLpNorm, psiFinal_integral⟩

end Work.KMTPlan.A6
