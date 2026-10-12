import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Commons.Analysis.Calculus.contDiff_update_apply
import Submission.Commons.Analysis.Calculus.norm_iteratedFDeriv_update_le
import Submission.Commons.Analysis.Fourier.fourier_decay_of_bounded_support
import Submission.Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow
import Submission.Work.SmallBoxD1KinIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-282 — decay of the D1 KINETIC integrand

`SmallBoxD1KinIntegrable` reduced the integrability of the D1 kinetic half to a uniform
(in `x ∈ abox`) Fourier-decay bound for the family `z ↦ χ_s(z)·Φ(x_{i↦z})`.  This module
supplies it.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Submission
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## 1 Derivative bounds for `chi` and `chiScale` -/

/-- `tsupport chiBase` is the closed ball of radius `1/2`. -/
lemma tsupport_chiBase : tsupport chiBase = Metric.closedBall (0 : ℝ³) (1 / 2) := by
  show tsupport chiBump = _
  rw [ContDiffBump.tsupport_eq]
  norm_num [chiBump]

/-- `ContDiff ℝ k chi` for every natural `k` (from `ContDiff ℝ ∞ chi`). -/
lemma chi_contDiff_nat (k : ℕ) : ContDiff ℝ k chi :=
  chi_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)

/-- `chi` is smooth with compact support, so every iterated derivative is bounded. -/
lemma exists_iteratedFDeriv_chi_le :
    ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧ ∀ k (z : ℝ³), ‖iteratedFDeriv ℝ k chi z‖ ≤ A k := by
  have hK : IsCompact (tsupport chi) := chi_hasCompactSupport.isCompact
  have key : ∀ k : ℕ, ∃ A : ℝ, ∀ z : ℝ³, ‖iteratedFDeriv ℝ k chi z‖ ≤ A := by
    intro k
    have hcont : Continuous (iteratedFDeriv ℝ k chi) :=
      ContDiff.continuous_iteratedFDeriv' (m := k) (chi_contDiff_nat k)
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max A 0, fun z => ?_⟩
    by_cases hz : z ∈ tsupport chi
    · exact le_trans (hA z hz) (le_max_left _ _)
    · have hz' : z ∉ Function.support (iteratedFDeriv ℝ k chi) :=
        fun h => hz (support_iteratedFDeriv_subset (𝕜 := ℝ) k h)
      simp only [Function.mem_support, not_not] at hz'
      rw [hz', norm_zero]
      exact le_max_right _ _
  choose A hA using key
  exact ⟨fun k => max (A k) 0, fun k => le_max_right _ _, fun k z =>
    le_trans (hA k z) (le_max_left _ _)⟩

/-- **Uniform derivative bounds for the rescaled window `chiScale s`.**
`chiScale s z = chi (s⁻¹ • z)`, so the chain rule with the dilation `s⁻¹ • id` gives
`‖D^k chiScale s z‖ ≤ ‖D^k chi (s⁻¹ z)‖ · (s⁻¹)^k`. -/
lemma exists_iteratedFDeriv_chiScale_le {s : ℝ} (hs : 0 < s) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ k (z : ℝ³), ‖iteratedFDeriv ℝ k (chiScale s) z‖ ≤ B k := by
  obtain ⟨A, hA0, hA⟩ := exists_iteratedFDeriv_chi_le
  refine ⟨fun k => A k * s⁻¹ ^ k, fun k => by have := hA0 k; positivity, fun k z => ?_⟩
  have hcd : ContDiff ℝ k chi := chi_contDiff_nat k
  have hshape : chiScale s = chi ∘ ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³) := by
    ext w
    simp [chiScale]
  have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (g := (s⁻¹) • ContinuousLinearMap.id ℝ ℝ³) (f := chi) hcd z (i := k) (hi := le_rfl)
  rw [hshape, hcomp]
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (g := iteratedFDeriv ℝ k chi ((s⁻¹) • z))
    (f := fun _ : Fin k => ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →L[ℝ] ℝ³))
  have h3 : ‖((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →L[ℝ] ℝ³)‖ = s⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ContinuousLinearMap.norm_id]
    ring
  refine le_trans h2 ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, h3]
  have := hA k ((s⁻¹) • z)
  have h4 : (0:ℝ) ≤ s⁻¹ ^ k := by positivity
  calc ‖iteratedFDeriv ℝ k chi (s⁻¹ • z)‖ * s⁻¹ ^ k ≤ A k * s⁻¹ ^ k := by
        exact mul_le_mul_of_nonneg_right this h4

/-- **Uniform derivative bounds for the complexified window `(chiScale s : ℂ)`.** -/
lemma exists_iteratedFDeriv_chiScaleC_le {s : ℝ} (hs : 0 < s) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ k (z : ℝ³), ‖iteratedFDeriv ℝ k (fun z : ℝ³ => (chiScale s z : ℂ)) z‖ ≤ B k := by
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_chiScale_le hs
  refine ⟨B, hB0, fun k z => ?_⟩
  have hcomp : (fun z : ℝ³ => (chiScale s z : ℂ)) = Complex.ofRealCLM ∘ (chiScale s) := by
    ext w; rfl
  rw [hcomp]
  have hshape : chiScale s = chi ∘ ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³) := by
    ext w; simp [chiScale]
  have hcd : ContDiffAt ℝ k (chiScale s) z := by
    rw [hshape]
    exact ((chi_contDiff_nat k).comp
      ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³).contDiff).contDiffAt
  have hcle := ContinuousLinearMap.iteratedFDeriv_comp_left
    (g := Complex.ofRealCLM) (f := chiScale s) hcd (i := k) (hi := le_rfl)
  rw [hcle]
  refine le_trans (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _) ?_
  have hnorm : ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ = 1 := Complex.ofRealCLM_norm
  rw [hnorm]
  simp only [one_mul]
  exact hB k z

/-! ## 2 The Fourier decay of the window `chiScale s` -/

/-- The complexified window `chiScale s`. -/
noncomputable def chiScaleC (s : ℝ) : ℝ³ → ℂ := fun z => Complex.ofReal (chiScale s z)

lemma chiScaleC_apply (s : ℝ) (z : ℝ³) : chiScaleC s z = Complex.ofReal (chiScale s z) := rfl

/-- `chiScale s` (complexified) has compact support. -/
lemma chiScaleC_ne_zero_iff (s : ℝ) (z : ℝ³) : chiScaleC s z ≠ 0 ↔ chiScale s z ≠ 0 := by
  refine not_congr ?_
  simp only [chiScaleC]
  exact Complex.ofReal_eq_zero

lemma hasCompactSupport_chiScaleC (s : ℝ) (hs : 0 < s) : HasCompactSupport (chiScaleC s) := by
  have key : ∀ z : ℝ³, chiScaleC s z ≠ 0 → ‖z‖ ≤ s / 2 := by
    intro z hz
    exact chiScale_support_le hs ((chiScaleC_ne_zero_iff s z).mp hz)
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ³) (s / 2))
    (fun z hz => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact key z (Function.mem_support.mp hz))

/-- `ContDiff ℝ 3` of the complexified window. -/
lemma contDiff_chiScaleC (s : ℝ) (hs : 0 < s) : ContDiff ℝ 3 (chiScaleC s) := by
  have hshape : chiScale s = chi ∘ ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³) := by
    ext w; simp [chiScale]
  have h1 : chiScaleC s = Complex.ofRealCLM ∘ chiScale s := rfl
  rw [h1, hshape]
  exact (chi_contDiff_nat 3).comp ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³).contDiff
    |>.continuousLinearMap_comp Complex.ofRealCLM

/-- **The Fourier decay of the window**: there is `C ≥ 0` with
`‖𝓕(chiScale s : ℂ)(ξ)‖ ≤ C(1+‖ξ‖)^{-3}`. -/
lemma exists_fourier_decay_chiScaleC {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ³,
      ‖FourierTransform.fourier (chiScaleC s) ξ‖ ≤ C / (1 + ‖ξ‖) ^ 3 := by
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_chiScaleC_le hs
  set M : ℝ := max (B 0) (max (B 1) (max (B 2) (B 3))) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact le_trans (hB0 0) (le_max_left _ _)
  have hMk : ∀ k, k ≤ 3 → ∀ z : ℝ³, ‖iteratedFDeriv ℝ k (chiScaleC s) z‖ ≤ M := by
    intro k hk z
    have h1 : B k ≤ M := by
      rw [hM]
      interval_cases k <;> simp
    exact le_trans (hB k z) h1
  obtain ⟨C, hC0, hC⟩ :=
    Commons.Analysis.Fourier.fourier_decay_of_bounded_support M (s / 2) hM0 (by positivity)
  refine ⟨C, hC0, fun ξ => ?_⟩
  have hb0 : ∀ x : ℝ³, ‖chiScaleC s x‖ ≤ M := by
    intro x; simpa only [norm_iteratedFDeriv_zero] using hMk 0 (by norm_num) x
  have hb1 : ∀ x : ℝ³, ‖iteratedFDeriv ℝ 1 (chiScaleC s) x‖ ≤ M := hMk 1 (by norm_num)
  have hb2 : ∀ x : ℝ³, ‖iteratedFDeriv ℝ 2 (chiScaleC s) x‖ ≤ M := hMk 2 (by norm_num)
  have hb3 : ∀ x : ℝ³, ‖iteratedFDeriv ℝ 3 (chiScaleC s) x‖ ≤ M := hMk 3 (by norm_num)
  exact hC (chiScaleC s) (contDiff_chiScaleC s hs) (hasCompactSupport_chiScaleC s hs)
    (fun z hz => chiScale_support_le hs ((chiScaleC_ne_zero_iff s z).mp hz)) hb0 hb1 hb2 hb3 ξ

/-! ## 3 The decay of `modeChat` -/

/-- `modeChat ℓ p` is the Fourier transform of the window at `(2π)⁻¹ p`. -/
lemma modeChat_eq_fourier {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    modeChat ℓ p = FourierTransform.fourier (chiScaleC ℓ) ((2 * π)⁻¹ • p) := by
  have hoff : ∀ y : ℝ³, y ∉ acube ℓ → chiScaleC ℓ y = 0 := by
    intro y hy
    have h : chiScale ℓ y = 0 := not_ne_iff.mp (fun hh => hy (chiScale_mem_acube hℓ hh))
    simp only [chiScaleC, h, Complex.ofReal_zero]
  have hcube : (∫ y : ℝ³,
        Complex.exp (↑(-2 * Real.pi * inner ℝ y ((2 * π)⁻¹ • p)) * Complex.I)
          • chiScaleC ℓ y)
      = ∫ y in acube ℓ,
        Complex.exp (↑(-2 * Real.pi * inner ℝ y ((2 * π)⁻¹ • p)) * Complex.I)
          • chiScaleC ℓ y :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun y : ℝ³ => Complex.exp (↑(-2 * Real.pi * inner ℝ y ((2 * π)⁻¹ • p)) * Complex.I)
          • chiScaleC ℓ y) (fun y hy => by rw [hoff y hy, smul_zero])).symm
  rw [Real.fourier_eq', hcube]
  refine setIntegral_congr_fun (acube_measurable ℓ) (fun y _ => ?_)
  have harg : (↑(-2 * Real.pi * inner ℝ y ((2 * π)⁻¹ • p)) : ℂ) * Complex.I
      = -(Complex.I * ((inner ℝ p y : ℝ) : ℂ)) := by
    have hinner : inner ℝ y ((2 * π)⁻¹ • p) = (2 * π)⁻¹ * inner ℝ p y := by
      rw [real_inner_smul_right, real_inner_comm y p]
    have hreal : -2 * Real.pi * inner ℝ y ((2 * π)⁻¹ • p) = - inner ℝ p y := by
      rw [hinner]
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hreal]
    push_cast
    ring
  rw [smul_eq_mul, harg]
  rw [show chiScaleC ℓ y = ((chiScale ℓ y : ℝ) : ℂ) from rfl]
  ring

/-- **The decay of the box mode amplitude**: `c_p = modeChat ℓ p` decays like `‖p‖^{-3}`. -/
lemma exists_modeChat_decay {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ³, ‖modeChat ℓ p‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := exists_fourier_decay_chiScaleC hℓ
  refine ⟨C * (2 * π) ^ 3, by positivity, fun p => ?_⟩
  rw [modeChat_eq_fourier hℓ p]
  refine le_trans (hC ((2 * π)⁻¹ • p)) ?_
  have hnorm : ‖(2 * π)⁻¹ • p‖ = (2 * π)⁻¹ * ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [hnorm]
  have h1 : 1 + ‖p‖ ≤ 2 * π * (1 + (2 * π)⁻¹ * ‖p‖) := by
    have h2 : (1:ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have h3 : 2 * π * (2 * π)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hexp : 2 * π * (1 + (2 * π)⁻¹ * ‖p‖) = 2 * π + ‖p‖ := by
      rw [mul_add, mul_one, ← mul_assoc, h3, one_mul]
    rw [hexp]; linarith [norm_nonneg p, h2]
  have hkey : (1:ℝ) / (1 + (2 * π)⁻¹ * ‖p‖) ^ 3 ≤ (2 * π) ^ 3 / (1 + ‖p‖) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : (1 + ‖p‖) ^ 3 ≤ (2 * π) ^ 3 * (1 + (2 * π)⁻¹ * ‖p‖) ^ 3 := by
      have h5 := pow_le_pow_left₀ (by positivity) h1 3
      rwa [mul_pow] at h5
    linarith [h4]
  calc C / (1 + (2 * π)⁻¹ * ‖p‖) ^ 3
      = C * (1 / (1 + (2 * π)⁻¹ * ‖p‖) ^ 3) := by ring
    _ ≤ C * ((2 * π) ^ 3 / (1 + ‖p‖) ^ 3) := mul_le_mul_of_nonneg_left hkey hC0
    _ = C * (2 * π) ^ 3 / (1 + ‖p‖) ^ 3 := by ring

/-! ## 4 Continuity of the D1 kinetic integrand in `p` -/

/-- joint continuity of `(p, y) ↦ (chiScale ℓ y : ℂ) * exp(-I⟨p,y⟩)`. -/
lemma continuous_chiMode_pair (ℓ : ℝ) :
    Continuous (fun q : ℝ³ × ℝ³ => Complex.ofReal (chiScale ℓ q.2) *
      Complex.exp (-(Complex.I * ((inner ℝ q.1 q.2 : ℝ) : ℂ)))) := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp ((chiScale_continuous ℓ).comp continuous_snd)
  · exact Complex.continuous_exp.comp (Continuous.neg (Continuous.mul continuous_const
      (Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_fst.prodMk continuous_snd)))))

/-- **`modeChat ℓ` is continuous in `p`** (parametric integral over the compact box). -/
lemma continuous_modeChat {ℓ : ℝ} (hℓ : 0 < ℓ) : Continuous (modeChat ℓ) := by
  have hcont : Continuous (Function.uncurry
      (fun p y : ℝ³ => Complex.ofReal (chiScale ℓ y) *
        Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))))) := by
    rw [show (Function.uncurry (fun p y : ℝ³ => Complex.ofReal (chiScale ℓ y) *
        Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))))
        = (fun q : ℝ³ × ℝ³ => Complex.ofReal (chiScale ℓ q.2) *
            Complex.exp (-(Complex.I * ((inner ℝ q.1 q.2 : ℝ) : ℂ)))) from by
      funext q; rfl]
    exact continuous_chiMode_pair ℓ
  have h := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ³)) (s := acube ℓ) (f := fun p y : ℝ³ =>
      Complex.ofReal (chiScale ℓ y) *
        Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) hcont (acube_compact hℓ)
  have key : (fun p : ℝ³ => ∫ y in acube ℓ, (chiScale ℓ y : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) = modeChat ℓ := by
    funext p; simp only [modeChat]
  rw [← key]
  exact h

/-- joint continuity of `(p, y) ↦ qMode ℓ p y`. -/
lemma continuous_qMode_pair {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun q : ℝ³ × ℝ³ => qMode ℓ q.1 q.2) := by
  have h2 : Continuous (fun q : ℝ³ × ℝ³ => ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ q.1) :=
    ((continuous_modeChat hℓ).comp continuous_fst).const_mul _
  rw [show (fun q : ℝ³ × ℝ³ => qMode ℓ q.1 q.2)
      = (fun q : ℝ³ × ℝ³ => Complex.ofReal (chiScale ℓ q.2) *
          Complex.exp (-(Complex.I * ((inner ℝ q.1 q.2 : ℝ) : ℂ))))
        - (fun q : ℝ³ × ℝ³ => ((ℓ ^ 3)⁻¹ : ℂ) * modeChat ℓ q.1) from by
    funext q; simp only [qMode, Pi.sub_apply]]
  exact (continuous_chiMode_pair ℓ).sub h2

/-- joint continuity of the real part `(p, y) ↦ qModeRe ℓ p y`. -/
lemma continuous_qModeRe_pair {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun q : ℝ³ × ℝ³ => qModeRe ℓ q.1 q.2) := by
  rw [show (fun q : ℝ³ × ℝ³ => qModeRe ℓ q.1 q.2)
      = fun q => (qMode ℓ q.1 q.2).re from by funext q; rfl]
  exact Complex.continuous_re.comp (continuous_qMode_pair hℓ)

/-- the `z`-integrand of `boxOp` is jointly continuous in `(q, z)`. -/
lemma continuous_boxOpIntegrand_aux {s : ℝ} (hs : 0 < s) {n : ℕ} (Φ : X (n + 1) → ℝ)
    (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    Continuous (fun r : (X (n + 1) × ℝ³) × ℝ³ =>
      qModeRe s r.1.2 r.2 * Φ (Function.update r.1.1 i r.2)) := by
  have hfun : (fun q : ℝ³ × ℝ³ => qModeRe s q.1 q.2) ∘
      (fun r : (X (n + 1) × ℝ³) × ℝ³ => (r.1.2, r.2))
      = (fun r : (X (n + 1) × ℝ³) × ℝ³ => qModeRe s r.1.2 r.2) := by
    funext r; rfl
  have hq : Continuous (fun r : (X (n + 1) × ℝ³) × ℝ³ => qModeRe s r.1.2 r.2) := by
    rw [← hfun]
    exact (continuous_qModeRe_pair (ℓ := s) hs).comp
      (((continuous_snd.comp continuous_fst :
        Continuous (fun r : (X (n + 1) × ℝ³) × ℝ³ => r.1.2))).prodMk continuous_snd)
  have hupd : Continuous (fun r : (X (n + 1) × ℝ³) × ℝ³ => Function.update r.1.1 i r.2) :=
    ((continuous_fst.comp continuous_fst :
      Continuous (fun r : (X (n + 1) × ℝ³) × ℝ³ => r.1.1))).update i continuous_snd
  exact hq.mul (hΦ.comp hupd)

/-- **the continuity of `boxOp` in `(x, p)`** -/
lemma continuous_boxOp_qModeRe {s : ℝ} (hs : 0 < s) {n : ℕ} (Φ : X (n + 1) → ℝ)
    (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    Continuous (fun q : X (n + 1) × ℝ³ =>
      ∫ z in acube s, qModeRe s q.2 z * Φ (Function.update q.1 i z)) := by
  refine continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ³)) (s := acube s)
    (f := fun q : X (n + 1) × ℝ³ => fun z : ℝ³ =>
      qModeRe s q.2 z * Φ (Function.update q.1 i z)) ?_ (acube_compact hs)
  change Continuous (fun r : (X (n + 1) × ℝ³) × ℝ³ =>
      qModeRe s r.1.2 r.2 * Φ (Function.update r.1.1 i r.2))
  exact continuous_boxOpIntegrand_aux hs Φ hΦ i

/-- **continuity of `p ↦ modeP s (p ↦ G(p,·)) Φ`** for a jointly continuous mode family `G`. -/
lemma continuous_modeP_of_pair {s : ℝ} (hs : 0 < s) (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ) {G : ℝ³ × ℝ³ → ℝ} (hG : Continuous G) :
    Continuous (fun p : ℝ³ => modeP s (fun z => G (p, z)) Φ) := by
  have hbox : Continuous (fun q : X (n + 1) × ℝ³ =>
      boxOp s (fun _ => (1 : ℝ)) (fun z => G (q.2, z)) Φ q.1) := by
    rw [show (fun q : X (n + 1) × ℝ³ =>
          boxOp s (fun _ => (1 : ℝ)) (fun z => G (q.2, z)) Φ q.1)
        = fun q => ∑ i : Fin (n + 1),
            ∫ z in acube s, G (q.2, z) * Φ (Function.update q.1 i z) from by
      funext q; simp only [boxOp, one_mul]]
    refine continuous_finsetSum _ (fun i _ => ?_)
    refine continuous_parametric_integral_of_continuous
      (μ := (volume : Measure ℝ³)) (s := acube s)
      (f := fun q : X (n + 1) × ℝ³ => fun z : ℝ³ =>
        G (q.2, z) * Φ (Function.update q.1 i z)) ?_ (acube_compact hs)
    rw [show Function.uncurry (fun q : X (n + 1) × ℝ³ => fun z : ℝ³ =>
          G (q.2, z) * Φ (Function.update q.1 i z))
        = (fun r : (X (n + 1) × ℝ³) × ℝ³ =>
            G (r.1.2, r.2) * Φ (Function.update r.1.1 i r.2)) from by
      funext r; rfl]
    exact (hG.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).mul
      (hΦ.comp (((continuous_fst.comp continuous_fst : Continuous
        (fun r : (X (n + 1) × ℝ³) × ℝ³ => r.1.1))).update i continuous_snd))
  have hjoint : Continuous (fun r : ℝ³ × X (n + 1) =>
      (boxOp s (fun _ => (1 : ℝ)) (fun z => G (r.1, z)) Φ r.2) ^ 2) := by
    have hfun : (fun q : X (n + 1) × ℝ³ =>
          boxOp s (fun _ => (1 : ℝ)) (fun z => G (q.2, z)) Φ q.1) ∘ Prod.swap
        = (fun r : ℝ³ × X (n + 1) =>
          boxOp s (fun _ => (1 : ℝ)) (fun z => G (r.1, z)) Φ r.2) := by
      funext r; rfl
    have h1 : Continuous (fun r : ℝ³ × X (n + 1) =>
        boxOp s (fun _ => (1 : ℝ)) (fun z => G (r.1, z)) Φ r.2) := by
      rw [← hfun]; exact hbox.comp continuous_swap
    exact h1.pow 2
  have hmain : Continuous (fun p : ℝ³ => ∫ x in abox (n + 1) s,
      (boxOp s (fun _ => (1 : ℝ)) (fun z => G (p, z)) Φ x) ^ 2) := by
    refine continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (X (n + 1)))) (s := abox (n + 1) s)
      (f := fun p : ℝ³ => fun x : X (n + 1) =>
        (boxOp s (fun _ => (1 : ℝ)) (fun z => G (p, z)) Φ x) ^ 2) ?_
      (abox_compact (n + 1) hs)
    change Continuous (fun r : ℝ³ × X (n + 1) =>
      (boxOp s (fun _ => (1 : ℝ)) (fun z => G (r.1, z)) Φ r.2) ^ 2)
    exact hjoint
  rw [show (fun p : ℝ³ => modeP s (fun z => G (p, z)) Φ)
      = fun p => (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s,
          (boxOp s (fun _ => (1 : ℝ)) (fun z => G (p, z)) Φ x) ^ 2 from by
    funext p; rfl]
  exact hmain.const_mul _

/-- **continuity of `p ↦ modeP s (qModeRe s p) Φ`** -/
lemma continuous_modeP_qModeRe {s : ℝ} (hs : 0 < s) (n : ℕ) (Φ : X (n + 1) → ℝ)
    (hΦ : Continuous Φ) :
    Continuous (fun p : ℝ³ => modeP s (qModeRe s p) Φ) :=
  continuous_modeP_of_pair hs n hΦ (continuous_qModeRe_pair hs)

/-- **continuity of `p ↦ modeP s (qModeIm s p) Φ`** -/
lemma continuous_modeP_qModeIm {s : ℝ} (hs : 0 < s) (n : ℕ) (Φ : X (n + 1) → ℝ)
    (hΦ : Continuous Φ) :
    Continuous (fun p : ℝ³ => modeP s (qModeIm s p) Φ) := by
  have hG : Continuous (fun q : ℝ³ × ℝ³ => (qMode s q.1 q.2).im) :=
    Complex.continuous_im.comp (continuous_qMode_pair hs)
  have h := continuous_modeP_of_pair hs n hΦ hG
  rw [show (fun p : ℝ³ => modeP s (fun z => (qMode s p z).im) Φ)
      = (fun p : ℝ³ => modeP s (qModeIm s p) Φ) from by
    funext p; rfl] at h
  exact h

/-! ## 5 The uniform Fourier decay of the `χ`-cosine overlap -/

/-- complexification does not increase the norm of an iterated derivative. -/
lemma norm_iteratedFDeriv_ofReal_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (k : ℕ) {z : E} (hf : ContDiffAt ℝ k f z) :
    ‖iteratedFDeriv ℝ k (fun y => (f y : ℂ)) z‖ ≤ ‖iteratedFDeriv ℝ k f z‖ := by
  have hcomp : (fun y : E => (f y : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left (g := Complex.ofRealCLM) hf (i := k) le_rfl]
  refine le_trans (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _) ?_
  rw [Complex.ofRealCLM_norm, one_mul]

/-- `ContDiff ℝ 3` of the complexified substituted `Φ`. -/
lemma contDiff_update_ofReal_C {n : ℕ} (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (x : X (n + 1)) (i : Fin (n + 1)) :
    ContDiff ℝ 3 (fun w : ℝ³ => ((Φ (Function.update x i w) : ℝ) : ℂ)) := by
  have hu : ContDiff ℝ 3 (fun w : ℝ³ => Φ (Function.update x i w)) :=
    hΦ.comp (Commons.Analysis.Calculus.contDiff_update_apply 3 x i)
  exact hu.continuousLinearMap_comp Complex.ofRealCLM

/-- **The Leibniz seminorm bound** for the product `chiScaleC s · (Φ ∘ update)`. -/
lemma norm_iteratedFDeriv_chiScaleC_mul_update_le {s : ℝ} (hs : 0 < s) {n : ℕ}
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ 3 Φ) (Q : ℕ → ℝ)
    (hQ : ∀ k ≤ 3, ∀ y ∈ abox (n + 1) s, ‖iteratedFDeriv ℝ k Φ y‖ ≤ Q k)
    (B : ℕ → ℝ) (hB : ∀ k, (0:ℝ) ≤ B k ∧ ∀ z : ℝ³,
      ‖iteratedFDeriv ℝ k (chiScaleC s) z‖ ≤ B k)
    {x : X (n + 1)} (hx : x ∈ abox (n + 1) s) (i : Fin (n + 1)) {z : ℝ³} (hz : z ∈ acube s)
    {k : ℕ} (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun w : ℝ³ => chiScaleC s w * ((Φ (Function.update x i w) : ℝ) : ℂ)) z‖
      ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j * Q (k - j) := by
  have hg : ContDiff ℝ 3 (fun w : ℝ³ => ((Φ (Function.update x i w) : ℝ) : ℂ)) :=
    contDiff_update_ofReal_C Φ hΦ x i
  have hmain := norm_iteratedFDeriv_mul_le (f := chiScaleC s)
    (g := fun w : ℝ³ => ((Φ (Function.update x i w) : ℝ) : ℂ))
    (contDiff_chiScaleC s hs) hg z (by exact_mod_cast hk)
  refine hmain.trans (Finset.sum_le_sum (fun j hj => ?_))
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hkj : k - j ≤ 3 := by omega
  have hupd : Function.update x i z ∈ abox (n + 1) s := update_mem_abox_of_mem i hx hz
  have h1 : ‖iteratedFDeriv ℝ j (chiScaleC s) z‖ ≤ B j := (hB j).2 z
  have huv : ContDiff ℝ 3 (fun w : ℝ³ => Φ (Function.update x i w)) :=
    hΦ.comp (Commons.Analysis.Calculus.contDiff_update_apply 3 x i)
  have hreal : ‖iteratedFDeriv ℝ (k - j) (fun w : ℝ³ => Φ (Function.update x i w)) z‖
      ≤ Q (k - j) := by
    refine le_trans ?_ (hQ (k - j) hkj _ hupd)
    have hΦkj : ContDiff ℝ (((k - j : ℕ)) : ℕ∞ω) Φ := hΦ.of_le (by exact_mod_cast hkj)
    exact Commons.Analysis.Calculus.norm_iteratedFDeriv_update_le Φ hΦkj x i z
  have h2 : ‖iteratedFDeriv ℝ (k - j) (fun w : ℝ³ => ((Φ (Function.update x i w) : ℝ) : ℂ)) z‖
      ≤ Q (k - j) := by
    have hca : ContDiffAt ℝ (((k - j : ℕ)) : ℕ∞ω) (fun w : ℝ³ => Φ (Function.update x i w)) z :=
      huv.contDiffAt.of_le (by exact_mod_cast hkj)
    exact le_trans (norm_iteratedFDeriv_ofReal_le (k - j)
      (f := fun w : ℝ³ => Φ (Function.update x i w)) hca) hreal
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _)
    (mul_nonneg (by positivity) ((hB j).1.trans' (by positivity)))

/-- **THE UNIFORM FOURIER DECAY OF THE WINDOWED SUBSTITUTED `Φ`.**  For `Φ : X (N+1) → ℝ`
of class `C³`, there is `C ≥ 0` with
`‖𝓕(χ_s·(Φ∘update_i))(ξ)‖ ≤ C/(1+‖ξ‖)^3`
for all `x ∈ abox (N+1) s`, all slots `i` and all `ξ`.

The transformed function is `C³`, compactly supported in `closedBall 0 (s/2)`, and its iterated
derivatives are bounded uniformly in `x` (Leibniz + the affine-isometry bound
`norm_iteratedFDeriv_update_le` + the compactness of `abox`); apply
`fourier_decay_of_bounded_support`. -/
lemma exists_modeFourier_decay {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∀ (Φ : X (n + 1) → ℝ), ContDiff ℝ 3 Φ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : X (n + 1)), x ∈ abox (n + 1) s → ∀ (i : Fin (n + 1)) (ξ : ℝ³),
        ‖FourierTransform.fourier (fun z : ℝ³ =>
          ((chiScale s z * Φ (Function.update x i z) : ℝ) : ℂ)) ξ‖ ≤ C / (1 + ‖ξ‖) ^ 3 := by
  intro Φ hΦ
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_chiScaleC_le hs
  have hQu : ∀ k : ℕ, ∃ Q : ℝ, 0 ≤ Q ∧ (k ≤ 3 → ∀ y ∈ abox (n + 1) s,
      ‖iteratedFDeriv ℝ k Φ y‖ ≤ Q) := by
    intro k
    by_cases hk : k ≤ 3
    · obtain ⟨Q, hQ⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn
        (ContDiff.continuous_iteratedFDeriv' (m := k) (hΦ.of_le (by exact_mod_cast hk))).continuousOn
      exact ⟨max Q 0, le_max_right _ _, fun _ y hy => le_trans (hQ y hy) (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose Q hQ0 hQ using hQu
  have hBnn : ∀ k, (0:ℝ) ≤ B k ∧ ∀ z : ℝ³, ‖iteratedFDeriv ℝ k (chiScaleC s) z‖ ≤ B k :=
    fun k => ⟨hB0 k, hB k⟩
  set Leib : ℕ → ℝ := fun k => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j * Q (k - j) with hLeib
  set Mf : ℝ := max 1 (max (Leib 0) (max (Leib 1) (max (Leib 2) (Leib 3)))) with hMf
  have hMf0 : (0:ℝ) ≤ Mf := le_trans zero_le_one (le_max_left _ _)
  have hMfk : ∀ k, k ≤ 3 → Leib k ≤ Mf := by
    intro k hk
    interval_cases k <;> simp [hMf]
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    Commons.Analysis.Fourier.fourier_decay_of_bounded_support Mf (s / 2) hMf0 (by positivity)
  refine ⟨C₀, hC₀0, ?_⟩
  intro x hx i ξ
  set F : ℝ³ → ℂ := fun z => chiScaleC s z * ((Φ (Function.update x i z) : ℝ) : ℂ) with hF
  have hFeq : (fun z : ℝ³ => ((chiScale s z * Φ (Function.update x i z) : ℝ) : ℂ)) = F := by
    funext z; simp only [hF, chiScaleC]; push_cast; ring
  have hsuppF : Function.support F ⊆ Metric.closedBall (0 : ℝ³) (s / 2) := by
    intro w hw
    rw [Function.mem_support] at hw
    have hne : chiScaleC s w ≠ 0 := by
      intro h
      refine hw ?_
      rw [hF]
      simp only [h, zero_mul]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact chiScale_support_le hs ((chiScaleC_ne_zero_iff s w).mp hne)
  have hclos : closure (Function.support F) ⊆ Metric.closedBall (0 : ℝ³) (s / 2) :=
    closure_minimal hsuppF Metric.isClosed_closedBall
  have hsub : ∀ k, Function.support (iteratedFDeriv ℝ k F) ⊆ Metric.closedBall (0 : ℝ³) (s / 2) :=
    fun k => (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := F) k).trans hclos
  have hFb : ∀ k ≤ 3, ∀ z : ℝ³, ‖iteratedFDeriv ℝ k F z‖ ≤ Mf := by
    intro k hk z
    by_cases hz : ‖z‖ ≤ s / 2
    · have hzc : z ∈ acube s := by
        intro m
        have h1 : |z m| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le (p := 2) (x := z) m
        rw [Set.mem_Icc]
        exact ⟨by linarith [abs_le.mp h1], by linarith [abs_le.mp h1]⟩
      have hleib := norm_iteratedFDeriv_chiScaleC_mul_update_le hs Φ hΦ Q
        (fun k hk y hy => hQ k hk y hy) B hBnn hx i hzc hk
      exact le_trans (by simpa only [hF] using hleib) (hMfk k hk)
    · have hznot : z ∉ Function.support (iteratedFDeriv ℝ k F) := fun h =>
        absurd (hsub k h) (by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
          exact hz)
      rw [Function.mem_support, not_not] at hznot
      rw [hznot, norm_zero]
      exact hMf0
  have hFcd : ContDiff ℝ 3 F := by
    rw [hF]
    exact (contDiff_chiScaleC s hs).mul (contDiff_update_ofReal_C Φ hΦ x i)
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ³) (s / 2)) hsuppF
  have hFsupp : ∀ z : ℝ³, F z ≠ 0 → ‖z‖ ≤ s / 2 := by
    intro z hz
    have hne : chiScaleC s z ≠ 0 := by
      intro h
      refine hz ?_
      rw [hF]
      simp only [h, zero_mul]
    exact chiScale_support_le hs ((chiScaleC_ne_zero_iff s z).mp hne)
  have hb0 : ∀ z : ℝ³, ‖F z‖ ≤ Mf := fun z => by
    simpa only [norm_iteratedFDeriv_zero] using hFb 0 (by norm_num) z
  have hdec := hC₀ F hFcd hFcs hFsupp hb0 (hFb 1 (by norm_num)) (hFb 2 (by norm_num))
    (hFb 3 (by norm_num)) ξ
  rw [hFeq]
  exact hdec

/-- **THE UNIFORM DECAY OF THE `χ`-COSINE OVERLAP** (the real part of the previous bound). -/
lemma exists_modeOverlap_decay {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∀ (Φ : X (n + 1) → ℝ), ContDiff ℝ 3 Φ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : X (n + 1)), x ∈ abox (n + 1) s → ∀ (i : Fin (n + 1)) (ξ : ℝ³),
        |∫ z in acube s, chiScale s z * Real.cos (-2 * Real.pi * inner ℝ z ξ) *
          Φ (Function.update x i z)| ≤ C / (1 + ‖ξ‖) ^ 3 := by
  intro Φ hΦ
  obtain ⟨C, hC0, hC⟩ := exists_modeFourier_decay hs n Φ hΦ
  refine ⟨C, hC0, fun x hx i ξ => ?_⟩
  have hΨc : Continuous (fun z : ℝ³ => Φ (Function.update x i z)) :=
    hΦ.continuous.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id)
  rw [cosCoeff_eq_re_fourier hs ξ hΨc]
  exact le_trans (Complex.abs_re_le_norm _) (hC x hx i ξ)

/-! ## 6 The per-slot bound on the `boxOp` integrand -/

/-- a rescaling helper: `1 + ‖(2π)^{-1}p‖ ≥ (2π)^{-1}(1+‖p‖)`. -/
lemma one_add_norm_inv_smul (p : ℝ³) :
    (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3 ≥ ((2 * π)⁻¹ * (1 + ‖p‖)) ^ 3 := by
  have hnorm : ‖((2 * π)⁻¹ : ℝ) • p‖ = (2 * π)⁻¹ * ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [hnorm]
  have h2 : (1:ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  have h3 : (2 * π)⁻¹ * (1 + ‖p‖) = (2 * π)⁻¹ + (2 * π)⁻¹ * ‖p‖ := by ring
  rw [h3]
  apply pow_le_pow_left₀ (by positivity)
  have : (0:ℝ) < 2 * π := by positivity
  nlinarith [norm_nonneg p, h2, inv_nonneg.mpr (le_of_lt this), inv_le_one_of_one_le₀ h2]

/-- **THE PER-SLOT DECAY BOUND** for the `boxOp` integrand
`∫_{acube s} qModeRe s p z · Φ(x_{i↦z})dz`. -/
lemma exists_qModeRe_mode_bound {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∀ (Φ : X (n + 1) → ℝ), ContDiff ℝ 3 Φ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : X (n + 1)), x ∈ abox (n + 1) s → ∀ (i : Fin (n + 1)) (p : ℝ³),
        |∫ z in acube s, qModeRe s p z * Φ (Function.update x i z)| ≤ K / (1 + ‖p‖) ^ 3 := by
  intro Φ hΦ
  obtain ⟨C, hC0, hC⟩ := exists_modeOverlap_decay hs n Φ hΦ
  obtain ⟨C', hC'0, hC'⟩ := exists_modeChat_decay hs
  obtain ⟨M0, hM0⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn hΦ.continuous.continuousOn
  set M : ℝ := max M0 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMb : ∀ y ∈ abox (n + 1) s, ‖Φ y‖ ≤ M := fun y hy => le_trans (hM0 y hy) (le_max_left _ _)
  refine ⟨max 1 ((2 * π) ^ 3 * C + C' * M), by positivity, fun x hx i p => ?_⟩
  -- the two pieces
  set A : ℝ := ∫ z in acube s, chiScale s z * Real.cos (inner ℝ p z) * Φ (Function.update x i z) with hA
  set Bv : ℝ := ∫ z in acube s, Φ (Function.update x i z) with hBv
  set cc : ℝ := (s ^ 3)⁻¹ * (modeChat s p).re with hcc
  have hsplit : (∫ z in acube s, qModeRe s p z * Φ (Function.update x i z)) = A - cc * Bv := by
    rw [hA, hBv, hcc]
    have hint : (∫ z in acube s, qModeRe s p z * Φ (Function.update x i z))
        = ∫ z in acube s, (chiScale s z * Real.cos (inner ℝ p z) * Φ (Function.update x i z)
            - ((s ^ 3)⁻¹ * (modeChat s p).re) * Φ (Function.update x i z)) := by
      refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
      rw [qModeRe_eq]; ring
    rw [hint]
    have hcont1 : Continuous (fun z : ℝ³ =>
        chiScale s z * Real.cos (inner ℝ p z) * Φ (Function.update x i z)) :=
      ((chiScale_continuous s).mul (Real.continuous_cos.comp
        (continuous_const.inner continuous_id))).mul
        (hΦ.continuous.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))
    have hcont2 : Continuous (fun z : ℝ³ =>
        ((s ^ 3)⁻¹ * (modeChat s p).re) * Φ (Function.update x i z)) :=
      continuous_const.mul
        (hΦ.continuous.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))
    rw [MeasureTheory.integral_sub
      (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
      (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)]
    rw [MeasureTheory.integral_const_mul]
  rw [hsplit]
  -- bound on |A|
  have hAb : |A| ≤ C * (2 * π) ^ 3 / (1 + ‖p‖) ^ 3 := by
    have h1 : |A| ≤ C / (1 + ‖(-((2 * π)⁻¹ : ℝ)) • p‖) ^ 3 := by
      have hraw := hC x hx i ((-((2 * π)⁻¹ : ℝ)) • p)
      have harg : ∀ z : ℝ³, Real.cos (-2 * Real.pi * inner ℝ z ((-((2 * π)⁻¹ : ℝ)) • p))
          = Real.cos (inner ℝ p z) := by
        intro z
        have he : -2 * Real.pi * inner ℝ z ((-((2 * π)⁻¹ : ℝ)) • p) = inner ℝ p z := by
          rw [real_inner_smul_right, real_inner_comm z p]
          have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          field_simp
        rw [he]
      have hEq : (∫ z in acube s, chiScale s z * Real.cos (-2 * Real.pi *
            inner ℝ z ((-((2 * π)⁻¹ : ℝ)) • p)) * Φ (Function.update x i z)) = A := by
        rw [hA]
        refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
        rw [harg z]
      rw [hEq] at hraw
      exact hraw
    have hnorm : ‖(-((2 * π)⁻¹ : ℝ)) • p‖ = ‖((2 * π)⁻¹ : ℝ) • p‖ := by
      rw [norm_smul, norm_smul, norm_neg]
    rw [hnorm] at h1
    refine le_trans h1 ?_
    have hle := one_add_norm_inv_smul p
    have hpos : (0:ℝ) < 2 * π := by positivity
    have h4 : (1 + ‖p‖) ^ 3 ≤ (2 * π) ^ 3 * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3 := by
      have h5 : ((2 * π)⁻¹ * (1 + ‖p‖)) ^ 3 ≤ (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3 := hle
      have h6 : (2 * π) ^ 3 * ((2 * π)⁻¹ * (1 + ‖p‖)) ^ 3 = (1 + ‖p‖) ^ 3 := by
        rw [← mul_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
      rw [← h6]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc C * (1 + ‖p‖) ^ 3
        ≤ C * ((2 * π) ^ 3 * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3) :=
          mul_le_mul_of_nonneg_left h4 hC0
      _ = C * (2 * π) ^ 3 * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3 := by ring
  -- bound on |Bv|
  have hBb : |Bv| ≤ M * s ^ 3 := by
    rw [hBv]
    have hvol : volume.real (acube s) = s ^ 3 := by
      rw [MeasureTheory.measureReal_def, acube_volume s hs.le]
      exact ENNReal.toReal_ofReal (pow_nonneg hs.le 3)
    have hb := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³))
      (f := fun z : ℝ³ => Φ (Function.update x i z)) (s := acube s) (C := M)
      (acube_lt_top s hs.le) (fun z hz => hMb _ (update_mem_abox_of_mem i hx hz))
    rw [hvol] at hb
    simpa using hb
  -- bound on |cc|
  have hcb : |cc| ≤ (s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3 := by
    rw [hcc, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (s ^ 3)⁻¹ from by positivity)]
    have h1 : |(modeChat s p).re| ≤ C' / (1 + ‖p‖) ^ 3 :=
      le_trans (Complex.abs_re_le_norm _) (hC' p)
    calc (s ^ 3)⁻¹ * |(modeChat s p).re| ≤ (s ^ 3)⁻¹ * (C' / (1 + ‖p‖) ^ 3) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3 := by ring
  have hspos : (0:ℝ) < s ^ 3 := pow_pos hs 3
  have hden : (0:ℝ) < (1 + ‖p‖) ^ 3 := by positivity
  have htri : |A - cc * Bv| ≤ |A| + ((s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3) * (M * s ^ 3) := by
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul]
    have h := mul_le_mul hcb hBb (abs_nonneg _) (by positivity)
    linarith [h]
  have hsimp : (s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3 * (M * s ^ 3) = C' * M / (1 + ‖p‖) ^ 3 := by
    field_simp
  rw [hsimp] at htri
  have hA2 : |A| ≤ (2 * π) ^ 3 * C / (1 + ‖p‖) ^ 3 := by
    have h' := hAb
    rw [show C * (2 * π) ^ 3 / (1 + ‖p‖) ^ 3 = (2 * π) ^ 3 * C / (1 + ‖p‖) ^ 3 from by
      ring] at h'
    exact h'
  refine le_trans htri ?_
  calc |A| + C' * M / (1 + ‖p‖) ^ 3
      ≤ (2 * π) ^ 3 * C / (1 + ‖p‖) ^ 3 + C' * M / (1 + ‖p‖) ^ 3 := by linarith [hA2]
    _ = ((2 * π) ^ 3 * C + C' * M) / (1 + ‖p‖) ^ 3 := by rw [← add_div]
    _ ≤ max 1 ((2 * π) ^ 3 * C + C' * M) / (1 + ‖p‖) ^ 3 := by
        rw [div_le_div_iff₀ hden hden]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hden.le

/-! ## 7 The sine overlap, and the `qModeIm` per-slot bound -/

/-- **The Fourier identification of the chi-sine overlap** (the imaginary-part companion of
`cosCoeff_eq_re_fourier`). -/
lemma sinCoeff_eq_im_fourier {s : ℝ} (hs : 0 < s) (ξ : ℝ³) {Ψ : ℝ³ → ℝ}
    (hΨ : Continuous Ψ) :
    (∫ z in acube s, chiScale s z * Real.sin (-2 * Real.pi * inner ℝ z ξ) * Ψ z)
      = (FourierTransform.fourier (fun z => ((chiScale s z * Ψ z : ℝ) : ℂ)) ξ).im := by
  set F : ℝ³ → ℂ := fun z => ((chiScale s z * Ψ z : ℝ) : ℂ) with hFdef
  have hsupp : ∀ v, v ∉ acube s → F v = 0 := by
    intro v hv
    have hχ : chiScale s v = 0 := not_ne_iff.mp (fun hh => hv (chiScale_mem_acube hs hh))
    simp only [hFdef]
    rw [show chiScale s v * Ψ v = 0 from by rw [hχ, zero_mul], Complex.ofReal_zero]
  have hcube : (∫ v : ℝ³,
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v)
      = ∫ v in acube s,
          Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun v : ℝ³ =>
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v)
      (fun v hv => by rw [hsupp v hv, smul_zero])).symm
  have hFcont : Continuous F := Complex.continuous_ofReal.comp ((chiScale_continuous s).mul hΨ)
  have hcont : Continuous fun v : ℝ³ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v := by
    rw [show (fun v : ℝ³ => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v)
        = (fun v : ℝ³ => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) * F v) from by
      funext v; rw [smul_eq_mul]]
    exact Complex.continuous_exp.comp (Continuous.mul
      (Complex.continuous_ofReal.comp (Continuous.mul continuous_const
        (continuous_inner.comp (continuous_id.prodMk continuous_const)))) continuous_const) |>.mul hFcont
  have hint : IntegrableOn (fun v : ℝ³ =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v) (acube s) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hs) hcont.continuousOn
  have hpt : ∀ z ∈ acube s,
      chiScale s z * Real.sin (-2 * Real.pi * inner ℝ z ξ) * Ψ z
        = (Complex.exp (↑(-2 * Real.pi * inner ℝ z ξ) * Complex.I) • F z).im := by
    intro z _
    have him : (F z).im = 0 := by simp [hFdef]
    have hre : (F z).re = chiScale s z * Ψ z := by simp [hFdef]
    rw [smul_eq_mul, Complex.mul_im, hre, him, mul_zero, zero_add]
    rw [Complex.exp_ofReal_mul_I_im]
    ring
  have hmain : (FourierTransform.fourier F ξ).im
      = (∫ v in acube s,
          Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).im := by
    rw [Real.fourier_eq', ← hcube]
  have hswap : (∫ v in acube s,
        Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).im
      = ∫ v in acube s,
          (Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v).im :=
    (Complex.imCLM.integral_comp_comm (μ := (volume : Measure ℝ³).restrict (acube s))
      (φ := fun v : ℝ³ => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • F v)
      hint).symm
  rw [hmain, hswap]
  exact setIntegral_congr_fun (acube_measurable s) hpt

/-- **THE UNIFORM DECAY OF THE `χ`-SINE OVERLAP.** -/
lemma exists_modeSine_decay {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∀ (Φ : X (n + 1) → ℝ), ContDiff ℝ 3 Φ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : X (n + 1)), x ∈ abox (n + 1) s → ∀ (i : Fin (n + 1)) (ξ : ℝ³),
        |∫ z in acube s, chiScale s z * Real.sin (-2 * Real.pi * inner ℝ z ξ) *
          Φ (Function.update x i z)| ≤ C / (1 + ‖ξ‖) ^ 3 := by
  intro Φ hΦ
  obtain ⟨C, hC0, hC⟩ := exists_modeFourier_decay hs n Φ hΦ
  refine ⟨C, hC0, fun x hx i ξ => ?_⟩
  have hΨc : Continuous (fun z : ℝ³ => Φ (Function.update x i z)) :=
    hΦ.continuous.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id)
  rw [sinCoeff_eq_im_fourier hs ξ hΨc]
  exact le_trans (Complex.abs_im_le_norm _) (hC x hx i ξ)

/-- **THE PER-SLOT DECAY BOUND** for `∫_{acube s} qModeIm s p z·Φ(x_{i↦z})dz`
(the companion of `exists_qModeRe_mode_bound`). -/
lemma exists_qModeIm_mode_bound {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∀ (Φ : X (n + 1) → ℝ), ContDiff ℝ 3 Φ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : X (n + 1)), x ∈ abox (n + 1) s → ∀ (i : Fin (n + 1)) (p : ℝ³),
        |∫ z in acube s, qModeIm s p z * Φ (Function.update x i z)| ≤ K / (1 + ‖p‖) ^ 3 := by
  intro Φ hΦ
  obtain ⟨C, hC0, hC⟩ := exists_modeSine_decay hs n Φ hΦ
  obtain ⟨C', hC'0, hC'⟩ := exists_modeChat_decay hs
  obtain ⟨M0, hM0⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn hΦ.continuous.continuousOn
  set M : ℝ := max M0 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMb : ∀ y ∈ abox (n + 1) s, ‖Φ y‖ ≤ M := fun y hy => le_trans (hM0 y hy) (le_max_left _ _)
  refine ⟨max 1 ((2 * π) ^ 3 * C + C' * M), by positivity, fun x hx i p => ?_⟩
  set A : ℝ := ∫ z in acube s, chiScale s z * Real.sin (inner ℝ p z) * Φ (Function.update x i z) with hA
  set Bv : ℝ := ∫ z in acube s, Φ (Function.update x i z) with hBv
  set cc : ℝ := (s ^ 3)⁻¹ * (modeChat s p).im with hcc
  have hsplit : (∫ z in acube s, qModeIm s p z * Φ (Function.update x i z)) = -(A + cc * Bv) := by
    rw [hA, hBv, hcc]
    have hint : (∫ z in acube s, qModeIm s p z * Φ (Function.update x i z))
        = ∫ z in acube s, (-(chiScale s z * Real.sin (inner ℝ p z) * Φ (Function.update x i z))
            - ((s ^ 3)⁻¹ * (modeChat s p).im) * Φ (Function.update x i z)) := by
      refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
      rw [qModeIm_eq]; ring
    rw [hint]
    have hcont1 : Continuous (fun z : ℝ³ =>
        -(chiScale s z * Real.sin (inner ℝ p z) * Φ (Function.update x i z))) :=
      (((chiScale_continuous s).mul (Real.continuous_sin.comp
        (continuous_const.inner continuous_id))).mul
        (hΦ.continuous.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))).neg
    have hcont2 : Continuous (fun z : ℝ³ =>
        ((s ^ 3)⁻¹ * (modeChat s p).im) * Φ (Function.update x i z)) :=
      continuous_const.mul
        (hΦ.continuous.comp (((continuous_const : Continuous fun _ : ℝ³ => x)).update i continuous_id))
    rw [MeasureTheory.integral_sub
      (ContinuousOn.integrableOn_compact (acube_compact hs) hcont1.continuousOn)
      (ContinuousOn.integrableOn_compact (acube_compact hs) hcont2.continuousOn)]
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
    ring
  rw [hsplit, abs_neg]
  have hAb : |A| ≤ C * (2 * π) ^ 3 / (1 + ‖p‖) ^ 3 := by
    have h1 : |A| ≤ C / (1 + ‖-((2 * π)⁻¹ : ℝ) • p‖) ^ 3 := by
      have hraw := hC x hx i (-((2 * π)⁻¹ : ℝ) • p)
      have harg : ∀ z : ℝ³, Real.sin (-2 * Real.pi * inner ℝ z ((-((2 * π)⁻¹ : ℝ)) • p))
          = Real.sin (inner ℝ p z) := by
        intro z
        have he : -2 * Real.pi * inner ℝ z ((-((2 * π)⁻¹ : ℝ)) • p) = inner ℝ p z := by
          rw [real_inner_smul_right, real_inner_comm z p]
          have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          field_simp
        rw [he]
      have hEq : (∫ z in acube s, chiScale s z * Real.sin (-2 * Real.pi *
            inner ℝ z ((-((2 * π)⁻¹ : ℝ)) • p)) * Φ (Function.update x i z)) = A := by
        rw [hA]
        refine setIntegral_congr_fun (acube_measurable s) (fun z _ => ?_)
        rw [harg z]
      rw [hEq] at hraw
      exact hraw
    have hnorm : ‖(-((2 * π)⁻¹ : ℝ)) • p‖ = ‖((2 * π)⁻¹ : ℝ) • p‖ := by
      rw [norm_smul, norm_smul, norm_neg]
    rw [hnorm] at h1
    refine le_trans h1 ?_
    have hle := one_add_norm_inv_smul p
    have hpos : (0:ℝ) < 2 * π := by positivity
    have h4 : (1 + ‖p‖) ^ 3 ≤ (2 * π) ^ 3 * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3 := by
      have h5 : ((2 * π)⁻¹ * (1 + ‖p‖)) ^ 3 ≤ (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3 := hle
      have h6 : (2 * π) ^ 3 * ((2 * π)⁻¹ * (1 + ‖p‖)) ^ 3 = (1 + ‖p‖) ^ 3 := by
        rw [← mul_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
      rw [← h6]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc C * (1 + ‖p‖) ^ 3
        ≤ C * ((2 * π) ^ 3 * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3) :=
          mul_le_mul_of_nonneg_left h4 hC0
      _ = C * (2 * π) ^ 3 * (1 + ‖((2 * π)⁻¹ : ℝ) • p‖) ^ 3 := by ring
  have hBb : |Bv| ≤ M * s ^ 3 := by
    rw [hBv]
    have hvol : volume.real (acube s) = s ^ 3 := by
      rw [MeasureTheory.measureReal_def, acube_volume s hs.le]
      exact ENNReal.toReal_ofReal (pow_nonneg hs.le 3)
    have hb := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³))
      (f := fun z : ℝ³ => Φ (Function.update x i z)) (s := acube s) (C := M)
      (acube_lt_top s hs.le) (fun z hz => hMb _ (update_mem_abox_of_mem i hx hz))
    rw [hvol] at hb
    simpa using hb
  have hcb : |cc| ≤ (s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3 := by
    rw [hcc, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (s ^ 3)⁻¹ from by positivity)]
    have h1 : |(modeChat s p).im| ≤ C' / (1 + ‖p‖) ^ 3 :=
      le_trans (Complex.abs_im_le_norm _) (hC' p)
    calc (s ^ 3)⁻¹ * |(modeChat s p).im| ≤ (s ^ 3)⁻¹ * (C' / (1 + ‖p‖) ^ 3) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3 := by ring
  have hspos : (0:ℝ) < s ^ 3 := pow_pos hs 3
  have hden : (0:ℝ) < (1 + ‖p‖) ^ 3 := by positivity
  have htri : |A + cc * Bv| ≤ |A| + ((s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3) * (M * s ^ 3) := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul]
    have h := mul_le_mul hcb hBb (abs_nonneg _) (by positivity)
    linarith [h]
  have hsimp : (s ^ 3)⁻¹ * C' / (1 + ‖p‖) ^ 3 * (M * s ^ 3) = C' * M / (1 + ‖p‖) ^ 3 := by
    field_simp
  rw [hsimp] at htri
  have hA2 : |A| ≤ (2 * π) ^ 3 * C / (1 + ‖p‖) ^ 3 := by
    have h' := hAb
    rw [show C * (2 * π) ^ 3 / (1 + ‖p‖) ^ 3 = (2 * π) ^ 3 * C / (1 + ‖p‖) ^ 3 from by
      ring] at h'
    exact h'
  refine le_trans htri ?_
  calc |A| + C' * M / (1 + ‖p‖) ^ 3
      ≤ (2 * π) ^ 3 * C / (1 + ‖p‖) ^ 3 + C' * M / (1 + ‖p‖) ^ 3 := by linarith [hA2]
    _ = ((2 * π) ^ 3 * C + C' * M) / (1 + ‖p‖) ^ 3 := by rw [← add_div]
    _ ≤ max 1 ((2 * π) ^ 3 * C + C' * M) / (1 + ‖p‖) ^ 3 := by
        rw [div_le_div_iff₀ hden hden]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hden.le

/-! ## 8 The `modeP` decay and the integrability of the D1 kinetic integrand -/

/-- continuity of a general `boxOp` slot integral. -/
lemma continuous_boxOp_gen {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    Continuous (fun x : X (n + 1) => ∫ z in acube s, g z * Φ (Function.update x i z)) := by
  refine continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ³)) (s := acube s)
    (f := fun x : X (n + 1) => fun z : ℝ³ => g z * Φ (Function.update x i z))
    ?_ (acube_compact hs)
  rw [show Function.uncurry (fun x : X (n + 1) => fun z : ℝ³ => g z * Φ (Function.update x i z))
      = (fun r : X (n + 1) × ℝ³ => g r.2 * Φ (Function.update r.1 i r.2)) from by
    funext r; rfl]
  exact (hg.comp continuous_snd).mul
    (hΦ.comp (((continuous_fst : Continuous (fun r : X (n + 1) × ℝ³ => r.1))).update i continuous_snd))

/-- continuity of the full `boxOp` in the configuration. -/
lemma continuous_boxOp_one {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) :
    Continuous (fun x : X (n + 1) => boxOp s (fun _ => (1 : ℝ)) g Φ x) := by
  rw [show (fun x : X (n + 1) => boxOp s (fun _ => (1 : ℝ)) g Φ x)
      = fun x => ∑ i : Fin (n + 1), ∫ z in acube s, g z * Φ (Function.update x i z) from by
    funext x; simp only [boxOp, one_mul]]
  exact continuous_finsetSum _ (fun i _ => continuous_boxOp_gen hs hg hΦ i)

/-- **`modeP` bound from a per-slot bound.**  If the slot integrals `∫_{acube s}g z Φ(x_{i↦z})dz`
are bounded by `K/(1+‖p‖)³` uniformly in `x, i`, then
`modeP s g Φ ≤ K²(n+1)²(s³)ⁿ/(1+‖p‖)⁶`. -/
lemma modeP_le_of_slot_bound {s : ℝ} (hs : 0 < s) {n : ℕ} {g : ℝ³ → ℝ} (hg : Continuous g)
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) {K : ℝ} (hK : 0 ≤ K) (p : ℝ³)
    (hb : ∀ (x : X (n + 1)), x ∈ abox (n + 1) s → ∀ (i : Fin (n + 1)),
      |∫ z in acube s, g z * Φ (Function.update x i z)| ≤ K / (1 + ‖p‖) ^ 3) :
    modeP s g Φ ≤ K ^ 2 * ((n : ℝ) + 1) ^ 2 * (s ^ 3) ^ n / (1 + ‖p‖) ^ 6 := by
  have hD : (0:ℝ) < (1 + ‖p‖) ^ 3 := by positivity
  have hKp : (0:ℝ) ≤ K / (1 + ‖p‖) ^ 3 := by positivity
  have hvolabox : volume.real (abox (n + 1) s) = (s ^ 3) ^ (n + 1) := by
    rw [MeasureTheory.measureReal_def, abox_volume (n + 1) s hs.le]
    exact ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg hs.le 3) (n + 1))
  have hpt : ∀ x ∈ abox (n + 1) s,
      (boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2
        ≤ (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2 := by
    intro x hx
    have hsum : boxOp s (fun _ => (1 : ℝ)) g Φ x
        = ∑ i : Fin (n + 1), ∫ z in acube s, g z * Φ (Function.update x i z) := by
      simp only [boxOp, one_mul]
    rw [hsum]
    have h1 := sq_sum_fin_le (n := n)
      (fun i : Fin (n + 1) => ∫ z in acube s, g z * Φ (Function.update x i z))
    have h2 : ∑ i : Fin (n + 1), (∫ z in acube s, g z * Φ (Function.update x i z)) ^ 2
        ≤ ∑ _i : Fin (n + 1), (K / (1 + ‖p‖) ^ 3) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hij : |∫ z in acube s, g z * Φ (Function.update x i z)| ≤ K / (1 + ‖p‖) ^ 3 :=
        hb x hx i
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hij 2
    have h3 : ∑ _i : Fin (n + 1), (K / (1 + ‖p‖) ^ 3) ^ 2
        = ((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    have h4 : ((n : ℝ) + 1) * (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3) ^ 2)
        = (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2 := by ring
    calc (∑ i : Fin (n + 1), ∫ z in acube s, g z * Φ (Function.update x i z)) ^ 2
        ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1),
            (∫ z in acube s, g z * Φ (Function.update x i z)) ^ 2 := h1
      _ ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [h3] at h2; exact h2
      _ = (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2 := h4
  have hint : ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2
      ≤ (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2 * (s ^ 3) ^ (n + 1) := by
    have hg1 : IntegrableOn (fun x : X (n + 1) => (boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2)
        (abox (n + 1) s) volume :=
      ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
        (((continuous_boxOp_one hs hg hΦ).pow 2).continuousOn)
    have hg2 : IntegrableOn (fun _ : X (n + 1) => (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2)
        (abox (n + 1) s) volume :=
      integrableOn_const (abox_lt_top (n + 1) s hs.le).ne
    calc ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2
        ≤ ∫ _x in abox (n + 1) s, (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2 :=
          setIntegral_mono_on (hf := hg1) (hg := hg2) (abox_measurable (n + 1) s) hpt
      _ = (((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2 * (s ^ 3) ^ (n + 1) := by
          rw [setIntegral_const, hvolabox, smul_eq_mul, mul_comm]
  rw [modeP]
  calc (s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, (boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2
      ≤ (s ^ 3)⁻¹ * ((((n : ℝ) + 1) * (K / (1 + ‖p‖) ^ 3)) ^ 2 * (s ^ 3) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (pow_nonneg hs.le 3))
    _ = K ^ 2 * ((n : ℝ) + 1) ^ 2 * (s ^ 3) ^ n / (1 + ‖p‖) ^ 6 := by
        rw [pow_succ]
        field_simp
        ring

/-- **THE `modeP` DECAY** for the real and imaginary parts of the mode. -/
lemma exists_modeP_decay {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∀ (Φ : X (n + 1) → ℝ), ContDiff ℝ 3 Φ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ p : ℝ³, modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ ≤ K / (1 + ‖p‖) ^ 6 := by
  intro Φ hΦ
  obtain ⟨K1, hK10, hK1⟩ := exists_qModeRe_mode_bound hs n Φ hΦ
  obtain ⟨K2, hK20, hK2⟩ := exists_qModeIm_mode_bound hs n Φ hΦ
  set K : ℝ := max K1 K2 with hK
  have hK0 : 0 ≤ K := le_trans hK10 (le_max_left _ _)
  refine ⟨2 * (K ^ 2 * ((n : ℝ) + 1) ^ 2 * (s ^ 3) ^ n), by positivity, fun p => ?_⟩
  have h1 := modeP_le_of_slot_bound hs (continuous_qModeRe p) hΦ.continuous hK0 p
    (fun x hx i => le_trans (hK1 x hx i p)
      (div_le_div_of_nonneg_right (le_max_left K1 K2) (by positivity)))
  have h2 := modeP_le_of_slot_bound hs (continuous_qModeIm p) hΦ.continuous hK0 p
    (fun x hx i => le_trans (hK2 x hx i p)
      (div_le_div_of_nonneg_right (le_max_right K1 K2) (by positivity)))
  refine le_trans (add_le_add h1 h2) ?_
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have heq : K ^ 2 * ((n : ℝ) + 1) ^ 2 * (s ^ 3) ^ n
        + K ^ 2 * ((n : ℝ) + 1) ^ 2 * (s ^ 3) ^ n
      = 2 * (K ^ 2 * ((n : ℝ) + 1) ^ 2 * (s ^ 3) ^ n) := by ring
  linarith [heq]

/-- **INTEGRABILITY OF THE D1 KINETIC INTEGRAND.**  For `Φ` smooth on the box and `c ≥ 0`,
`p ↦ [‖p‖−c]₊²·(P_{u_p}+P_{v_p})` is integrable.  The proof is domination by
`max 1 K · ‖p‖²/(1+‖p‖)⁶` (integrable in dimension 3 by
`Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow`), together with the decay
`exists_modeP_decay`. -/
lemma integrable_kinetic_half {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ ∞ Φ) :
    Integrable (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
      (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_modeP_decay hs n Φ
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  set K' : ℝ := max 1 K with hK'
  have hK'0 : 0 ≤ K' := le_trans zero_le_one (le_max_left _ _)
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
      (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)) volume := by
    refine Continuous.aestronglyMeasurable ?_
    refine ((?_ : Continuous (fun p : ℝ³ => fsKinCoeff c ‖p‖))).mul
      ((continuous_modeP_qModeRe hs n Φ hΦ.continuous).add
        (continuous_modeP_qModeIm hs n Φ hΦ.continuous))
    rw [show (fun p : ℝ³ => fsKinCoeff c ‖p‖)
        = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘ (fun p : ℝ³ => ‖p‖) from rfl]
    have hcont : Continuous (fun r : ℝ => max (r - c) 0) :=
      (continuous_id.sub (continuous_const : Continuous (fun _ : ℝ => c))).max
        (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
    exact (hcont.pow 2).comp continuous_norm
  have hbase : Integrable (fun p : ℝ³ => ‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) :=
    Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow 6 le_rfl
  have hg : Integrable (fun p : ℝ³ => K' * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6)) :=
    hbase.const_mul K'
  refine Integrable.mono (μ := volume)
    (f := fun p : ℝ³ => fsKinCoeff c ‖p‖ *
      (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ))
    (g := fun p : ℝ³ => K' * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6)) hg hmeas ?_
  filter_upwards with p
  have h1 : fsKinCoeff c ‖p‖ ≤ ‖p‖ ^ 2 := by
    rw [fsKinCoeff]
    have h2 : max (‖p‖ - c) 0 ≤ ‖p‖ := max_le (by linarith) (norm_nonneg p)
    exact pow_le_pow_left₀ (le_max_right _ _) h2 2
  have h2 : modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ ≤ K' / (1 + ‖p‖) ^ 6 :=
    le_trans (hK p) (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  have h3 : (0:ℝ) ≤ modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ :=
    add_nonneg (modeP_nonneg hs _ Φ) (modeP_nonneg hs _ Φ)
  have hfp : (0:ℝ) ≤ fsKinCoeff c ‖p‖ := fsKinCoeff_nonneg c ‖p‖
  have hgp : (0:ℝ) ≤ K' * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg hfp h3), Real.norm_of_nonneg hgp]
  calc fsKinCoeff c ‖p‖ * (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)
      ≤ ‖p‖ ^ 2 * (K' / (1 + ‖p‖) ^ 6) := mul_le_mul h1 h2 h3 (by positivity)
    _ = K' * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by ring

end BoseGases
end Submission
