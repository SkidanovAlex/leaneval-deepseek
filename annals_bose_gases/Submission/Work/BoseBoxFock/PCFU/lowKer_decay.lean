import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.BoseBoxFock.PCFU.lowKer_regular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.lowKer_decay`

The position-space low-momentum kernel
`lowKer fc κ z = (2π)^{-3}∫_p f(‖p‖/κ)·cos⟪p,z⟫` (`PCFU/dictBricks.lean`) is the inverse Fourier
transform of the *smooth, compactly supported* symbol `p ↦ f(‖p‖/κ)`
(`Work.BoseBoxFix.LowCut`: `f` is `C^∞`, `f = 1` on `(-∞,1]`, `f = 0` on `[2,∞)`).  Hence it
decays faster than any polynomial: for every `N` it is `O((1+‖z‖)^{-2N})`.

The proof goes through Mathlib's Fourier analysis.  Writing `g p = (f(‖p‖/κ) : ℂ)`,

* `lowKer fc κ z = (2π)^{-3}·Re (𝓕 g ((2π)^{-1}•z))` (`lowKer_eq_re_fourier`), because the Fourier
  kernel `exp(-2πi⟪v,w⟫)` has real part `cos` and the symbol is radial and real;
* `‖w‖^{2N}‖𝓕 g w‖ ≤ 2^{2N}Σ_{j≤2N}∫_v ‖D^j g v‖` for all `w`
  (`Real.pow_mul_norm_iteratedFDeriv_fourier_le`, Mathlib): the Fourier transform of a `C^{2N}`
  compactly supported function decays like `‖w‖^{-2N}`;
* `lowKer` is bounded (`PCFU/lowKer_regular.lean`).

The only analytic input is that `g` is `C^∞` with compact support: `f(‖p‖/κ) = 1` for `‖p‖ < κ`
(so there is no singularity at the origin) while `p ↦ ‖p‖/κ` is smooth for `p ≠ 0`.
-/

noncomputable section
open MeasureTheory
open scoped Topology BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The complexified low-momentum symbol `p ↦ f(‖p‖/κ)`, whose Fourier transform is `lowKer`. -/
def lowCutComplex (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (p : E3) : ℂ := (fc.f (‖p‖ / κ) : ℂ)

lemma lowCutComplex_apply (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (p : E3) :
    lowCutComplex fc κ p = (fc.f (‖p‖ / κ) : ℂ) := rfl

/-- **`g = f(‖·‖/κ)` is smooth.**  Near the origin it is the constant `1` (`f = 1` on `(-∞,1]`);
away from the origin `‖·‖` is smooth, and `f` is smooth everywhere. -/
lemma contDiff_lowCutComplex (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ (⊤ : ℕ∞) (lowCutComplex fc κ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  rcases lt_or_ge (‖p‖) κ with hp | hp
  · -- `p` lies in the open ball of radius `κ`, where `f(‖·‖/κ) ≡ 1`
    have hmem : p ∈ Metric.ball (0 : E3) κ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hp
    have hev : lowCutComplex fc κ =ᶠ[nhds p] fun _ => (1 : ℂ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with q hq
      have hq' : ‖q‖ < κ := by simpa [Metric.mem_ball, dist_eq_norm] using hq
      have hq1 : ‖q‖ / κ ≤ 1 := by
        have h : ‖q‖ / κ < 1 := by rw [div_lt_one hκ]; exact hq'
        exact h.le
      rw [lowCutComplex, fc.one (‖q‖ / κ) hq1]
      simp
    exact (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq hev
  · -- `‖p‖ ≥ κ > 0`, so `p ≠ 0` and `‖·‖` is smooth near `p`
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, norm_zero] at hp
      linarith
    have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : E3 => ‖q‖) p := contDiffAt_norm ℝ hp0
    have hdiv : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : E3 => ‖q‖ / κ) p := hnorm.div_const κ
    have hf : ContDiffAt ℝ (⊤ : ℕ∞) fc.f (‖p‖ / κ) := fc.smooth.contDiffAt
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : E3 => fc.f (‖q‖ / κ)) p := hf.comp p hdiv
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : E3 => ((fc.f (‖q‖ / κ) : ℝ) : ℂ)) p :=
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).contDiffAt.comp p h1
    exact h2

/-- `g = f(‖·‖/κ)` vanishes outside the closed ball of radius `2κ`. -/
lemma support_lowCutComplex_subset (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    Function.support (lowCutComplex fc κ) ⊆ Metric.closedBall (0 : E3) (2 * κ) := by
  intro p hp
  have hp' : fc.f (‖p‖ / κ) ≠ 0 := by
    intro h
    exact hp (by simp [lowCutComplex, h])
  have h2 : ‖p‖ / κ < 2 := by
    by_contra h
    exact hp' (fc.zero _ (not_lt.mp h))
  have h3 : ‖p‖ < 2 * κ := (div_lt_iff₀ hκ).mp h2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  linarith

lemma hasCompactSupport_lowCutComplex (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (lowCutComplex fc κ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (2 * κ))
    (support_lowCutComplex_subset fc hκ)

lemma integrable_lowCutComplex (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    Integrable (lowCutComplex fc κ) :=
  (contDiff_lowCutComplex fc hκ).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_lowCutComplex fc hκ)

/-- Every iterated derivative of `g` is integrable: it is continuous with compact support. -/
lemma integrable_iteratedFDeriv_lowCutComplex (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ)
    (n : ℕ) :
    Integrable (fun v : E3 => ‖iteratedFDeriv ℝ n (lowCutComplex fc κ) v‖) := by
  have hle : (↑(↑n : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have hcd : ContDiff ℝ (↑(↑n : ℕ∞)) (lowCutComplex fc κ) :=
    (contDiff_lowCutComplex fc hκ).of_le hle
  exact ((hcd.continuous_iteratedFDeriv' (m := n)).integrable_of_hasCompactSupport
    ((hasCompactSupport_lowCutComplex fc hκ).iteratedFDeriv n)).norm

/-- Pointwise form of the Fourier dictionary: the Fourier kernel `𝕖(-⟪v,w⟫)` against the radial real
symbol has real part `f(‖v‖/κ)·cos⟪v,z⟫` at `w = (2π)^{-1}z`. -/
private lemma fourierChar_smul_re_lowCutComplex (fc : Work.BoseBoxFix.LowCut) (κ : ℝ)
    (z v : E3) :
    (Real.fourierChar (-inner ℝ v ((2 * Real.pi)⁻¹ • z)) • lowCutComplex fc κ v).re
      = fc.f (‖v‖ / κ) * Real.cos (inner ℝ v z) := by
  have h2π : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hinner : 2 * Real.pi * (-inner ℝ v ((2 * Real.pi)⁻¹ • z)) = -inner ℝ v z := by
    rw [real_inner_smul_right]
    field_simp
  rw [Circle.smul_def, Real.fourierChar_apply, lowCutComplex, smul_eq_mul, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im, hinner, Real.cos_neg]
  ring

/-- **`lowKer` is `(2π)^{-3}` times the real part of the Fourier transform of `f(‖·‖/κ)`.** -/
lemma lowKer_eq_re_fourier (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (z : E3) :
    lowKer fc κ z
      = ((2 * Real.pi) ^ 3)⁻¹
          * (FourierTransform.fourier (lowCutComplex fc κ) ((2 * Real.pi)⁻¹ • z)).re := by
  have hIntF : Integrable
      (fun v : E3 => Real.fourierChar (-inner ℝ v ((2 * Real.pi)⁻¹ • z))
        • lowCutComplex fc κ v) :=
    (Real.fourierIntegral_convergent_iff (f := lowCutComplex fc κ) ((2 * Real.pi)⁻¹ • z)).mpr
      (integrable_lowCutComplex fc hκ)
  have hre : (∫ v : E3,
      Real.fourierChar (-inner ℝ v ((2 * Real.pi)⁻¹ • z)) • lowCutComplex fc κ v).re
      = ∫ v : E3,
        (Real.fourierChar (-inner ℝ v ((2 * Real.pi)⁻¹ • z)) • lowCutComplex fc κ v).re := by
    have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hIntF
    simpa [Complex.reCLM_apply] using h.symm
  rw [lowKer, Real.fourier_eq, hre]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  exact (fourierChar_smul_re_lowCutComplex fc κ z v).symm

theorem lowKer_decay (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
      (1 + ‖z‖) ^ (2 * N) * ‖Work.BoseBoxFock.PCFU.lowKer fc κ z‖ ≤ C := by
  obtain ⟨-, C₀, hC₀0, hC₀⟩ := lowKer_regular fc hκ
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (lowCutComplex fc κ) := contDiff_lowCutComplex fc hκ
  -- the finite sum of `L¹`-norms of the iterated derivatives of the symbol
  set Bsum : ℝ := ∑ j ∈ Finset.range (2 * N + 1),
    ∫ v : E3, ‖iteratedFDeriv ℝ j (lowCutComplex fc κ) v‖ with hBsumdef
  have hBsum_nonneg : 0 ≤ Bsum := by
    rw [hBsumdef]
    exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun v => norm_nonneg _))
  -- the decay of the Fourier transform
  have hdec : ∀ w : E3,
      ‖w‖ ^ (2 * N) * ‖FourierTransform.fourier (lowCutComplex fc κ) w‖
        ≤ (2 : ℝ) ^ (2 * N) * Bsum := by
    intro w
    have h'f : ∀ (k n : ℕ), ↑k ≤ (0 : ℕ∞) → ↑n ≤ (⊤ : ℕ∞) →
        Integrable (fun v : E3 => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (lowCutComplex fc κ) v‖) := by
      intro k n hk _
      have hk0 : k = 0 := by
        have : k ≤ 0 := by exact_mod_cast hk
        omega
      subst hk0
      simpa using integrable_iteratedFDeriv_lowCutComplex fc hκ n
    have hmain := Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (f := lowCutComplex fc κ) (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
      hcd h'f (k := 0) (n := 2 * N) le_rfl le_top w
    rw [norm_iteratedFDeriv_zero] at hmain
    have hsum : (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (2 * N + 1),
        ∫ v : E3, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (lowCutComplex fc κ) v‖) = Bsum := by
      rw [hBsumdef, Finset.sum_product]
      simp only [zero_add, Finset.sum_range_one]
      exact Finset.sum_congr rfl (fun j _ => by simp)
    rw [hsum] at hmain
    simpa using hmain
  refine ⟨max ((2 : ℝ) ^ (2 * N) * C₀)
    ((2 : ℝ) ^ (2 * N) * (2 * Real.pi) ^ (2 * N) * ((2 * Real.pi) ^ 3)⁻¹
      * ((2 : ℝ) ^ (2 * N) * Bsum)), ?_, ?_⟩
  · exact le_trans (mul_nonneg (by positivity) hC₀0) (le_max_left _ _)
  · intro z
    rw [Real.norm_eq_abs, lowKer_eq_re_fourier fc hκ z]
    rcases le_or_gt ‖z‖ 1 with hz | hz
    · -- low frequencies: boundedness of `lowKer`
      have h1 : (1 + ‖z‖) ^ (2 * N) ≤ (2 : ℝ) ^ (2 * N) :=
        pow_le_pow_left₀ (by positivity) (by linarith) (2 * N)
      have hle := hC₀ z
      rw [lowKer_eq_re_fourier fc hκ z] at hle
      exact le_trans (mul_le_mul h1 hle (abs_nonneg _) (by positivity)) (le_max_left _ _)
    · -- high frequencies: `(1+‖z‖)^{2N} ≤ 2^{2N}‖z‖^{2N}` and the decay of `𝓕 g`
      set w : E3 := (2 * Real.pi)⁻¹ • z with hwdef
      have hwnorm : (2 * Real.pi) * ‖w‖ = ‖z‖ := by
        rw [hwdef, norm_smul, Real.norm_of_nonneg (by positivity)]
        field_simp
      have hrew : ‖z‖ ^ (2 * N) = (2 * Real.pi) ^ (2 * N) * ‖w‖ ^ (2 * N) := by
        rw [← hwnorm, mul_pow]
      have hple : (1 + ‖z‖) ≤ 2 * ‖z‖ := by linarith
      have hpow : (1 + ‖z‖) ^ (2 * N) ≤ 2 ^ (2 * N) * ‖z‖ ^ (2 * N) := by
        have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ‖z‖) hple (2 * N)
        rwa [mul_pow] at h
      have hc0 : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
      have h1 : |((2 * Real.pi) ^ 3)⁻¹
            * (FourierTransform.fourier (lowCutComplex fc κ) w).re|
          ≤ ((2 * Real.pi) ^ 3)⁻¹ * ‖FourierTransform.fourier (lowCutComplex fc κ) w‖ := by
        rw [abs_mul, abs_of_pos hc0]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (le_of_lt hc0)
      have h2 : (1 + ‖z‖) ^ (2 * N) * |((2 * Real.pi) ^ 3)⁻¹
            * (FourierTransform.fourier (lowCutComplex fc κ) w).re|
          ≤ (2 ^ (2 * N) * ‖z‖ ^ (2 * N))
              * (((2 * Real.pi) ^ 3)⁻¹
                * ‖FourierTransform.fourier (lowCutComplex fc κ) w‖) :=
        mul_le_mul hpow h1 (abs_nonneg _) (by positivity)
      have hb : (2 ^ (2 * N) * ‖z‖ ^ (2 * N))
            * (((2 * Real.pi) ^ 3)⁻¹ * ‖FourierTransform.fourier (lowCutComplex fc κ) w‖)
          = ((2 ^ (2 * N) * (2 * Real.pi) ^ (2 * N)) * ((2 * Real.pi) ^ 3)⁻¹)
              * (‖w‖ ^ (2 * N) * ‖FourierTransform.fourier (lowCutComplex fc κ) w‖) := by
        rw [hrew]
        ac_rfl
      have hd : ((2 ^ (2 * N) * (2 * Real.pi) ^ (2 * N)) * ((2 * Real.pi) ^ 3)⁻¹)
            * (‖w‖ ^ (2 * N) * ‖FourierTransform.fourier (lowCutComplex fc κ) w‖)
          ≤ ((2 ^ (2 * N) * (2 * Real.pi) ^ (2 * N)) * ((2 * Real.pi) ^ 3)⁻¹)
              * ((2 : ℝ) ^ (2 * N) * Bsum) :=
        mul_le_mul_of_nonneg_left (hdec w) (by positivity)
      exact le_trans (le_trans h2 (le_of_eq hb)) (le_trans hd (le_max_right _ _))

end Work.BoseBoxFock.PCFU
