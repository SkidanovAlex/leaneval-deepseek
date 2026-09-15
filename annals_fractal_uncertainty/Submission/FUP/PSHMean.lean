import Submission.FUP.ExtensionOperator
import Submission.Commons.Analysis.Calculus.norm_taylor_remainder_le
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators Real

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# Mean values over complex circles

The last step of the proof of `prop:Ew_is_psh` shows the sub-mean-value property at points of
`ℝᵈ` using two elementary estimates: the mean of `Re(e^{iθ}v)` vanishes, and
`⨍_0^{2π} ‖Im(e^{iθ}v)‖ dθ ≥ ‖v‖/2` (`circleMean_imVec_ge`, the main result of this module).
-/

/-- The Euclidean norm of a complex vector, under the identification `ℂᵈ ≃ ℝ^{2d}`. -/
noncomputable def enorm (v : ℂᵈ) : ℝ := Real.sqrt (∑ i : Fin d, ‖v i‖ ^ 2)

lemma enorm_nonneg (v : ℂᵈ) : 0 ≤ enorm v := Real.sqrt_nonneg _

lemma enorm_sq (v : ℂᵈ) : enorm v ^ 2 = ∑ i : Fin d, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- For `z ∈ ℂᵈ` the Euclidean norm of the imaginary part is at most the Euclidean norm of `z`. -/
lemma norm_imVec_le_enorm (z : ℂᵈ) : ‖imVec z‖ ≤ enorm z := by
  have h2 : ∀ i : Fin d, ‖z i‖ ^ 2 = (z i).re ^ 2 + (z i).im ^ 2 := by
    intro i
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h1 : ‖imVec z‖ ^ 2 ≤ enorm z ^ 2 := by
    rw [enorm_sq, EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [imVec_apply, h2 i]
    linarith [sq_nonneg (z i).re]
  calc ‖imVec z‖ = Real.sqrt (‖imVec z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (enorm z ^ 2) := Real.sqrt_le_sqrt h1
    _ = enorm z := Real.sqrt_sq (enorm_nonneg _)

/-- Rotation by a real angle preserves the Euclidean norm on `ℂᵈ`. -/
lemma enorm_circlePt (θ : ℝ) (v : ℂᵈ) : enorm (circlePt θ v) = enorm v := by
  have h2 : ∀ i : Fin d, ‖circlePt θ v i‖ = ‖v i‖ := by
    intro i
    rw [circlePt_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [enorm, enorm]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [h2 i])

lemma imVec_circlePt_apply (θ : ℝ) (v : ℂᵈ) (i : Fin d) :
    imVec (circlePt θ v) i = Real.sin θ * (v i).re + Real.cos θ * (v i).im := by
  have h : circlePt θ v i = (Real.cos θ + Real.sin θ * Complex.I) * v i := by
    rw [circlePt_apply, Complex.exp_ofReal_mul_I]
  rw [imVec_apply, h]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
    zero_add, add_zero]
  ring

/-- The squared coordinates of `e^{iθ}v`. -/
lemma norm_imVec_circlePt_sq (θ : ℝ) (v : ℂᵈ) :
    ‖imVec (circlePt θ v)‖ ^ 2
      = ∑ i : Fin d, (Real.sin θ * (v i).re + Real.cos θ * (v i).im) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl (fun i _ => by rw [imVec_circlePt_apply])

/-- **The circle average of the squared imaginary part.** -/
lemma integral_norm_imVec_circlePt_sq (v : ℂᵈ) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖ ^ 2 = π * enorm v ^ 2 := by
  have hterm : ∀ i : Fin d,
      (∫ θ in (0 : ℝ)..(2 * π),
          (Real.sin θ * (v i).re + Real.cos θ * (v i).im) ^ 2)
        = π * ((v i).re ^ 2 + (v i).im ^ 2) := by
    intro i
    have hcont1 : Continuous fun θ : ℝ => (v i).re ^ 2 * Real.sin θ ^ 2 := by fun_prop
    have hcont2 : Continuous fun θ : ℝ => (v i).im ^ 2 * Real.cos θ ^ 2 := by fun_prop
    have hcont3 : Continuous fun θ : ℝ =>
        2 * (v i).re * (v i).im * (Real.sin θ * Real.cos θ) := by fun_prop
    have hsplit : (fun θ : ℝ => (Real.sin θ * (v i).re + Real.cos θ * (v i).im) ^ 2)
        = fun θ : ℝ => (v i).re ^ 2 * Real.sin θ ^ 2
            + ((v i).im ^ 2 * Real.cos θ ^ 2
              + 2 * (v i).re * (v i).im * (Real.sin θ * Real.cos θ)) := by
      funext θ; ring
    rw [hsplit, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_sin_sq, integral_cos_sq,
      integral_sin_mul_cos₁]
    all_goals first
      | (rw [Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]; ring)
      | (apply Continuous.intervalIntegrable; fun_prop)
  have hcont : ∀ i : Fin d, Continuous fun θ : ℝ =>
      (Real.sin θ * (v i).re + Real.cos θ * (v i).im) ^ 2 := by
    intro i; fun_prop
  simp only [norm_imVec_circlePt_sq]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hcont i).intervalIntegrable _ _)]
  simp only [hterm]
  rw [← Finset.mul_sum]
  congr 1
  rw [enorm_sq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **The mean value estimate.**  For every `v ∈ ℂᵈ` the mean over `θ ∈ [0,2π]` of the
Euclidean norm of `Im(e^{iθ}v)` is at least half the Euclidean norm of `v`. -/
theorem circleMean_imVec_ge (v : ℂᵈ) :
    enorm v / 2 ≤ (∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖) / (2 * π) := by
  rcases eq_or_lt_of_le (enorm_nonneg v) with h0 | hpos
  · -- `v = 0`
    have hv : v = 0 := by
      have h1 : ∑ i : Fin d, ‖v i‖ ^ 2 = 0 := by
        have := enorm_sq v
        rw [← h0] at this
        simpa using this.symm
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖v j‖)).mp h1 i
        (Finset.mem_univ i)
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    subst hv
    have hnn : (0 : ℝ) ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ (0 : ℂᵈ))‖ :=
      intervalIntegral.integral_nonneg (by positivity) (fun θ _ => norm_nonneg _)
    have hzero : enorm (0 : ℂᵈ) = 0 := by simp [enorm]
    rw [hzero, zero_div]
    exact div_nonneg hnn (by positivity)
  · have hle : ∀ θ : ℝ, ‖imVec (circlePt θ v)‖ ^ 2 ≤ ‖imVec (circlePt θ v)‖ * enorm v := by
      intro θ
      have h1 : ‖imVec (circlePt θ v)‖ ≤ enorm v := by
        rw [← enorm_circlePt θ v]
        exact norm_imVec_le_enorm _
      calc ‖imVec (circlePt θ v)‖ ^ 2
          = ‖imVec (circlePt θ v)‖ * ‖imVec (circlePt θ v)‖ := sq _
        _ ≤ ‖imVec (circlePt θ v)‖ * enorm v :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have hInt : (∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖ ^ 2)
        ≤ (∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖) * enorm v := by
      rw [← intervalIntegral.integral_mul_const]
      have hcont : Continuous fun θ : ℝ => ‖imVec (circlePt θ v)‖ := by
        apply continuous_norm.comp
        have hcoord : Continuous fun θ : ℝ => (fun i : Fin d => (circlePt θ v i).im) := by
          apply continuous_pi
          intro i
          have hfun : (fun θ : ℝ => (circlePt θ v i).im)
              = fun θ : ℝ => Real.sin θ * (v i).re + Real.cos θ * (v i).im := by
            funext θ
            exact imVec_circlePt_apply θ v i
          rw [hfun]
          fun_prop
        exact ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous).comp hcoord
      exact intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * π)
        ((hcont.pow 2).intervalIntegrable _ _)
        ((hcont.mul continuous_const).intervalIntegrable _ _) hle
    rw [integral_norm_imVec_circlePt_sq] at hInt
    have h2 : (∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖) * enorm v
        = enorm v * (∫ θ in (0 : ℝ)..(2 * π), ‖imVec (circlePt θ v)‖) := by ring
    rw [h2] at hInt
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hInt, hpos.le]

lemma reVec_circlePt_apply (θ : ℝ) (v : ℂᵈ) (i : Fin d) :
    reVec (circlePt θ v) i = Real.cos θ * (v i).re - Real.sin θ * (v i).im := by
  have h : circlePt θ v i = (Real.cos θ + Real.sin θ * Complex.I) * v i := by
    rw [circlePt_apply, Complex.exp_ofReal_mul_I]
  rw [reVec_apply, h]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero,
    zero_add, add_zero]

lemma circlePt_add_pi (θ : ℝ) (v : ℂᵈ) : circlePt (θ + π) v = - circlePt θ v := by
  ext i
  simp only [circlePt_apply, Pi.neg_apply]
  rw [show ((θ + π : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (π : ℂ) * Complex.I by push_cast; ring, Complex.exp_add,
    Complex.exp_pi_mul_I]
  ring

lemma reVec_neg (z : ℂᵈ) : reVec (-z) = -reVec z := by
  rw [reVec, reVec]
  have h : (fun i : Fin d => ((-z) i).re) = -(fun i : Fin d => (z i).re) := by
    funext i
    simp
  rw [h, map_neg]

/-- For `z ∈ ℂᵈ` the Euclidean norm of the real part is at most the Euclidean norm of `z`. -/
lemma norm_reVec_le_enorm (z : ℂᵈ) : ‖reVec z‖ ≤ enorm z := by
  have h2 : ∀ i : Fin d, ‖z i‖ ^ 2 = (z i).re ^ 2 + (z i).im ^ 2 := by
    intro i
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h1 : ‖reVec z‖ ^ 2 ≤ enorm z ^ 2 := by
    rw [enorm_sq, EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [reVec_apply, h2 i]
    linarith [sq_nonneg (z i).im]
  calc ‖reVec z‖ = Real.sqrt (‖reVec z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (enorm z ^ 2) := Real.sqrt_le_sqrt h1
    _ = enorm z := Real.sqrt_sq (enorm_nonneg _)

/-- The mean of `Re(e^{iθ}v)` over a full turn vanishes. -/
lemma integral_reVec_circlePt (v : ℂᵈ) :
    ∫ θ in (0 : ℝ)..(2 * π), reVec (circlePt θ v) = 0 := by
  set f : ℝ → ℝᵈ := fun θ => reVec (circlePt θ v) with hf
  have hanti : ∀ θ, f (θ + π) = - f θ := by
    intro θ
    simp only [hf]
    rw [circlePt_add_pi, reVec_neg]
  have hper : Function.Periodic f (2 * π) := by
    intro θ
    have h2 : θ + 2 * π = (θ + π) + π := by ring
    rw [h2, hanti (θ + π), hanti θ, neg_neg]
  have hcont : Continuous f := by
    have hcoord : Continuous fun θ : ℝ => (fun i : Fin d => (circlePt θ v i).re) := by
      apply continuous_pi
      intro i
      have hfun : (fun θ : ℝ => (circlePt θ v i).re)
          = fun θ : ℝ => Real.cos θ * (v i).re - Real.sin θ * (v i).im := by
        funext θ
        exact reVec_circlePt_apply θ v i
      rw [hfun]
      fun_prop
    exact ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous).comp hcoord
  have hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable f volume t₁ t₂ := fun t₁ t₂ =>
    hcont.intervalIntegrable t₁ t₂
  -- the integral over `[π, 3π]` equals the integral over `[0, 2π]` (periodicity)
  have hper3 : (∫ θ in π..(3 * π), f θ) = ∫ θ in (0 : ℝ)..(2 * π), f θ := by
    have h := hper.intervalIntegral_add_eq (0 : ℝ) π
    simp only [zero_add, show π + 2 * π = 3 * π by ring] at h
    exact h.symm
  -- the same integral, rewritten by the substitution `θ ↦ θ + π`
  have hshift : (∫ θ in π..(3 * π), f θ) = - ∫ θ in (0 : ℝ)..(2 * π), f θ := by
    have h1 : (∫ θ in π..(3 * π), f θ) = ∫ θ in (0 : ℝ)..(2 * π), f (θ + π) := by
      have h := intervalIntegral.integral_comp_add_right f π (a := (0 : ℝ)) (b := 2 * π)
      rw [zero_add, show 2 * π + π = 3 * π by ring] at h
      exact h.symm
    rw [h1, show (fun θ : ℝ => f (θ + π)) = fun θ => - f θ from funext fun θ => hanti θ]
    simp [intervalIntegral.integral_neg]
  have hfinal : (∫ θ in (0 : ℝ)..(2 * π), f θ) = - ∫ θ in (0 : ℝ)..(2 * π), f θ :=
    calc (∫ θ in (0 : ℝ)..(2 * π), f θ) = ∫ θ in π..(3 * π), f θ := hper3.symm
      _ = - ∫ θ in (0 : ℝ)..(2 * π), f θ := hshift
  have hzero : (∫ θ in (0 : ℝ)..(2 * π), f θ) = 0 := by
    have h2 : (2 : ℝ) • (∫ θ in (0 : ℝ)..(2 * π), f θ) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hfinal]
      simp
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  rw [hzero]

/-- **The sub-mean-value estimate at points of `ℝᵈ`** (the last step of the proof of
`prop:Ew_is_psh`).  If `ω` is continuous and its second-order Taylor remainder satisfies
`ω(x + h) - ω(x) - ∇ω(x)·h ≥ -lam‖h‖²`, then the mean of `θ ↦ ω(x + Re(e^{iθ}v))` over a full turn
is at least `ω(x) - lam‖v‖²`.

The Taylor hypothesis is supplied in §3 by the `C²` regularity of `ω`; the point of the lemma is
that the linear term of the expansion integrates away, because `⨍ Re(e^{iθ}v) dθ = 0`
(`integral_reVec_circlePt`). -/
lemma circleMean_omega_ge {ω : ℝᵈ → ℝ} {lam : ℝ} (hω : Continuous ω) (hlam : 0 ≤ lam)
    (x : ℝᵈ) (v : ℂᵈ)
    (hTaylor : ∀ h : ℝᵈ, ω (x + h) - ω x - fderiv ℝ ω x h ≥ -(lam * ‖h‖ ^ 2)) :
    ω x - lam * enorm v ^ 2
      ≤ (∫ θ in (0 : ℝ)..(2 * π), ω (x + reVec (circlePt θ v))) / (2 * π) := by
  set L : ℝᵈ →L[ℝ] ℝ := fderiv ℝ ω x with hL
  have hcontR : Continuous fun θ : ℝ => reVec (circlePt θ v) := by
    have hcoord : Continuous fun θ : ℝ => (fun i : Fin d => (circlePt θ v i).re) := by
      apply continuous_pi
      intro i
      have hfun : (fun θ : ℝ => (circlePt θ v i).re)
          = fun θ : ℝ => Real.cos θ * (v i).re - Real.sin θ * (v i).im := by
        funext θ
        exact reVec_circlePt_apply θ v i
      rw [hfun]
      fun_prop
    exact ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous).comp hcoord
  have hA : Continuous fun _ : ℝ => ω x := continuous_const
  have hB : Continuous fun θ : ℝ => L (reVec (circlePt θ v)) := L.continuous.comp hcontR
  have hC : Continuous fun _ : ℝ => lam * enorm v ^ 2 := continuous_const
  have hcont1 : Continuous fun θ : ℝ => ω (x + reVec (circlePt θ v)) :=
    hω.comp (continuous_const.add hcontR)
  have hpt : ∀ θ : ℝ, ω x + L (reVec (circlePt θ v)) - lam * enorm v ^ 2
      ≤ ω (x + reVec (circlePt θ v)) := by
    intro θ
    have h1 := hTaylor (reVec (circlePt θ v))
    have h2 : ‖reVec (circlePt θ v)‖ ≤ enorm v := by
      rw [← enorm_circlePt θ v]
      exact norm_reVec_le_enorm _
    have h3 : lam * ‖reVec (circlePt θ v)‖ ^ 2 ≤ lam * enorm v ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2) hlam
    linarith
  have hmono : (∫ θ in (0 : ℝ)..(2 * π), (ω x + L (reVec (circlePt θ v)) - lam * enorm v ^ 2))
      ≤ ∫ θ in (0 : ℝ)..(2 * π), ω (x + reVec (circlePt θ v)) :=
    intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * π)
      (show IntervalIntegrable
        (fun θ : ℝ => ω x + L (reVec (circlePt θ v)) - lam * enorm v ^ 2) volume 0 (2 * π) from
          ((hA.add hB).sub hC).intervalIntegrable 0 (2 * π))
      (show IntervalIntegrable (fun θ : ℝ => ω (x + reVec (circlePt θ v))) volume 0 (2 * π) from
          hcont1.intervalIntegrable 0 (2 * π)) hpt
  have hLint : (∫ θ in (0 : ℝ)..(2 * π), L (reVec (circlePt θ v)))
      = L (∫ θ in (0 : ℝ)..(2 * π), reVec (circlePt θ v)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm L (hcontR.intervalIntegrable _ _)
  have hcompute : (∫ θ in (0 : ℝ)..(2 * π), (ω x + L (reVec (circlePt θ v)) - lam * enorm v ^ 2))
      = 2 * π * (ω x - lam * enorm v ^ 2) := by
    rw [intervalIntegral.integral_sub
        (show IntervalIntegrable (fun θ : ℝ => ω x + L (reVec (circlePt θ v))) volume 0 (2 * π)
          from (hA.add hB).intervalIntegrable 0 (2 * π))
        (show IntervalIntegrable (fun _ : ℝ => lam * enorm v ^ 2) volume 0 (2 * π)
          from hC.intervalIntegrable 0 (2 * π)),
      intervalIntegral.integral_add
        (show IntervalIntegrable (fun _ : ℝ => ω x) volume 0 (2 * π)
          from hA.intervalIntegrable 0 (2 * π))
        (show IntervalIntegrable (fun θ : ℝ => L (reVec (circlePt θ v))) volume 0 (2 * π)
          from hB.intervalIntegrable 0 (2 * π)),
      hLint, intervalIntegral.integral_const, intervalIntegral.integral_const,
      integral_reVec_circlePt, map_zero]
    simp [smul_eq_mul]
    ring
  rw [hcompute] at hmono
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)]
  linarith [hmono]

/-- **The sub-mean-value estimate at points of `ℝᵈ`.**  For a `C²` weight `ω` whose second
derivative is bounded by `lam`, the mean of `θ ↦ ω(x + Re(e^{iθ}v))` over a full turn is at least
`ω(x) - lam‖v‖²`.  This is the second half of the last step of the proof of `prop:Ew_is_psh`. -/
lemma circleMean_omega_ge_of_contDiff {ω : ℝᵈ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hω : ContDiff ℝ 2 ω) (h2 : ∀ x : ℝᵈ, ‖iteratedFDeriv ℝ 2 ω x‖ ≤ lam) (x : ℝᵈ) (v : ℂᵈ) :
    ω x - lam * enorm v ^ 2
      ≤ (∫ θ in (0 : ℝ)..(2 * π), ω (x + reVec (circlePt θ v))) / (2 * π) :=
  circleMean_omega_ge hω.continuous hlam x v fun h => by
    have h1 := Commons.Analysis.Calculus.norm_taylor_remainder_le hlam hω h2 x h
    have h2' : -(lam * ‖h‖ ^ 2) ≤ ω (x + h) - ω x - fderiv ℝ ω x h := by
      have := abs_le.mp (by rw [Real.norm_eq_abs] at h1; exact h1)
      linarith [this.1]
    exact h2'

end Submission.FUP
