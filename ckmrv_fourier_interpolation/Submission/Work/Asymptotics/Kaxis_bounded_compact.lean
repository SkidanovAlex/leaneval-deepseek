import Mathlib
import Submission.Work.Asymptotics.MiddleRange.Basic
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.MiddleRange.norm_le_of_norm_le_of_two_zeros
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.Kaxis_local_coincidence

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Metric Filter Complex

namespace Work.Asymptotics

open Work.Kernels

set_option maxHeartbeats 4000000

namespace KbcAux

/-! ## The contour point `t ↦ it` -/

/-- The point `it` of the imaginary axis, as a total function of `t` (junk for `t ≤ 0`). -/
def ct (t : ℝ) : ℍ := UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I)

lemma ct_eq_imagAxis {t : ℝ} (h : 0 < t) : ct t = imagAxis t h := by
  have h2 : 0 < (((t : ℂ) * Complex.I)).im := by simpa using h
  rw [ct, UpperHalfPlane.ofComplex_apply_of_im_pos h2, imagAxis]

lemma ct_coe {t : ℝ} (h : 0 < t) : ((ct t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
  rw [ct_eq_imagAxis h]; rfl

lemma ct_re {t : ℝ} (h : 0 < t) : ((ct t : ℍ) : ℂ).re = 0 := by
  rw [ct_coe h]; simp

lemma ct_im {t : ℝ} (h : 0 < t) : (ct t).im = t := by
  rw [ct_eq_imagAxis h]
  simp [imagAxis, Complex.mul_im]

lemma ct_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ‖((ct s : ℍ) : ℂ) - ((ct t : ℍ) : ℂ)‖ = ‖(s : ℂ) - (t : ℂ)‖ := by
  rw [ct_coe hs, ct_coe ht,
    show (s : ℂ) * Complex.I - (t : ℂ) * Complex.I = ((s - t : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    show ((s : ℂ) - (t : ℂ)) = ((s - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm]

/-! ## The one-zero maximum modulus bound -/

/-- **One-zero bound.**  A function holomorphic on the disc `ball c ρ` with a zero at a point of
the half-radius disc is bounded there by `(2M/ρ)·|z - z₁|`, where `M` bounds `‖f‖` on the disc. -/
theorem norm_le_mul_dist_of_one_zero {f : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : DiffContOnCl ℂ f (Metric.ball c ρ)) (hbd : ∀ z ∈ Metric.ball c ρ, ‖f z‖ ≤ M)
    {z₁ : ℂ} (h₁ : z₁ ∈ Metric.ball c (ρ / 2)) (hf₁ : f z₁ = 0) :
    ∀ z ∈ Metric.ball c (ρ / 2), ‖f z‖ ≤ (2 * M / ρ) * ‖z - z₁‖ := by
  intro z hz
  have hz₁ρ : z₁ ∈ Metric.ball c ρ := Metric.ball_subset_ball (by linarith) h₁
  have hgd : DifferentiableOn ℂ (dslope f z₁) (Metric.ball c ρ) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hz₁ρ)).mpr hf.differentiableOn
  have hfac : ∀ w : ℂ, (w - z₁) * dslope f z₁ w = f w := by
    intro w; simpa using sub_smul_dslope_of_zero hf₁ w
  have hbound : ‖dslope f z₁ z‖ ≤ 2 * M / ρ := by
    have key : ∀ᶠ r in 𝓝[<] ρ, ‖dslope f z₁ z‖ ≤ M / (r - ρ / 2) := by
      filter_upwards [Ioo_mem_nhdsLT (show ρ / 2 < ρ by linarith)] with r hr
      obtain ⟨hrl, hrr⟩ := hr
      have hzr : z ∈ Metric.ball c r := Metric.mem_ball.mpr (by
        have := Metric.mem_ball.mp hz; linarith)
      have hgd' : DiffContOnCl ℂ (dslope f z₁) (Metric.ball c r) :=
        hgd.diffContOnCl_ball (Metric.closedBall_subset_ball hrr)
      have hpos : 0 < r - ρ / 2 := by linarith
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hgd' ?_
        (subset_closure hzr)
      intro w hw
      have hws : w ∈ Metric.sphere c r := frontier_ball_subset_sphere hw
      have hwr : dist w c = r := Metric.mem_sphere.mp hws
      have hwρ : w ∈ Metric.ball c ρ := Metric.mem_ball.mpr (by rw [hwr]; exact hrr)
      have hfw := hbd w hwρ
      have hfwn : ‖f w‖ = ‖w - z₁‖ * ‖dslope f z₁ w‖ := by rw [← hfac w, norm_mul]
      have hd₁w : r - ρ / 2 ≤ ‖w - z₁‖ := by
        have ht : r ≤ ‖w - z₁‖ + dist z₁ c := by
          have := dist_triangle w z₁ c
          rw [hwr] at this
          simpa [dist_eq_norm] using this
        have hz₁c : dist z₁ c < ρ / 2 := Metric.mem_ball.mp h₁
        linarith
      rw [le_div_iff₀ hpos]
      calc ‖dslope f z₁ w‖ * (r - ρ / 2)
          ≤ ‖dslope f z₁ w‖ * ‖w - z₁‖ := mul_le_mul_of_nonneg_left hd₁w (norm_nonneg _)
        _ = ‖f w‖ := by rw [hfwn]; ring
        _ ≤ M := hfw
    have hne2 : ρ - ρ / 2 ≠ 0 := by linarith
    have hc : ContinuousAt (fun r : ℝ => M / (r - ρ / 2)) ρ :=
      ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) hne2
    have hval : M / (ρ - ρ / 2) = 2 * M / ρ := by
      rw [show ρ - ρ / 2 = ρ / 2 by ring]; field_simp
    have htend : Tendsto (fun r : ℝ => M / (r - ρ / 2)) (𝓝[<] ρ) (𝓝 (2 * M / ρ)) := by
      rw [← hval]; exact hc.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto htend key
  rw [← hfac z, norm_mul]
  calc ‖z - z₁‖ * ‖dslope f z₁ z‖ ≤ ‖z - z₁‖ * (2 * M / ρ) :=
        mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = (2 * M / ρ) * ‖z - z₁‖ := by ring

/-! ## The zeros of the cleared kernel and its holomorphy -/

lemma KfunClear_self (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d z z = 0 := by
  rw [KfunClear, Work.Residues.KPlusClear_diag d hd z, Work.Residues.KMinusClear_diag ℓ d hd z]
  ring

/-- The cleared kernel vanishes at the `S`-conjugate pair: `KfunClear (S z) z = 0`. -/
lemma KfunClear_S_self (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d (ModularGroup.S • z) z = 0 := by
  rw [KfunClear, (KClear_S_vanishing ℓ d hd z).1, (KClear_S_vanishing ℓ d hd z).2]
  ring

lemma mdifferentiable_KfunClear_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => KfunClear ℓ d τ z) :=
  (KernelClear_growth_tau ℓ d hd z).1.1

lemma mdifferentiable_KfunClear_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => KfunClear ℓ d τ z) :=
  (KernelClear_growth_z ℓ d hd τ).1.1

/-- The lift of `τ ↦ KfunClear τ z` to a ball (inside `ℍ`) is differentiable with continuous
extension to the closed ball. -/
lemma diffContOnCl_lift_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    {c : ℍ} {ρ : ℝ} (hsub : Metric.closedBall (c : ℂ) ρ ⊆ {w : ℂ | 0 < w.im}) :
    DiffContOnCl ℂ (fun w : ℂ => KfunClear ℓ d (UpperHalfPlane.ofComplex w) z)
      (Metric.ball (c : ℂ) ρ) := by
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => KfunClear ℓ d (UpperHalfPlane.ofComplex w) z)
      {w : ℂ | 0 < w.im} := by
    intro w hw
    exact (differentiableAt_comp_ofComplex_of_mdiff (mdifferentiable_KfunClear_fst ℓ d hd z)
      (⟨w, hw⟩ : ℍ)).differentiableWithinAt
  exact hdiff.diffContOnCl_ball hsub

lemma closedBall_subset_upper {c : ℍ} {ρ : ℝ} (h : ρ < c.im) :
    Metric.closedBall (c : ℂ) ρ ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have h1 : ‖w - (c : ℂ)‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have h2 : |(w - (c : ℂ)).im| ≤ ‖w - (c : ℂ)‖ := Complex.abs_im_le_norm _
  have h3 : (w - (c : ℂ)).im = w.im - c.im := by
    simp only [Complex.sub_im, UpperHalfPlane.coe_im]
  have h4 : -(ρ) ≤ w.im - c.im := by
    have := (abs_le.mp (le_trans h2 h1)).1
    linarith [h3]
  have h5 : (0 : ℝ) < c.im - ρ := by linarith
  show (0 : ℝ) < w.im
  linarith

/-- Bounds for `KfunClear` on a product of two closed Euclidean balls inside `ℍ`. -/
lemma exists_bound_KfunClear_of_balls (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (c₁ c₂ : ℍ) {R₁ R₂ : ℝ} (hR₁ : R₁ < c₁.im) (hR₂ : R₂ < c₂.im) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ z : ℍ, ‖(τ : ℂ) - (c₁ : ℂ)‖ ≤ R₁ → ‖(z : ℂ) - (c₂ : ℂ)‖ ≤ R₂ →
      ‖KfunClear ℓ d τ z‖ ≤ M := by
  obtain ⟨s₁, hs₁, hb₁⟩ := exists_scale_bound_euclidean (c := c₁) (r := R₁) hR₁
  obtain ⟨s₂, hs₂, hb₂⟩ := exists_scale_bound_euclidean (c := c₂) (r := R₂) hR₂
  obtain ⟨M, hM, h⟩ := exists_bound_KfunClear_of_scale_bounds ℓ d hd hs₁ hs₂
    (fun τ hτ => hb₁ τ hτ) (fun z hz => hb₂ z hz)
  exact ⟨M, hM, fun τ z h1 h2 => h τ h1 z h2⟩

/-! ## Metric helpers -/

/-- Euclidean triangle inequality for points of `ℍ`. -/
lemma norm_sub_le_three (a b c : ℍ) :
    ‖(a : ℂ) - (b : ℂ)‖ ≤ ‖(a : ℂ) - (c : ℂ)‖ + ‖(c : ℂ) - (b : ℂ)‖ := by
  rw [show (a : ℂ) - (b : ℂ) = ((a : ℂ) - (c : ℂ)) + ((c : ℂ) - (b : ℂ)) by ring]
  exact norm_add_le _ _

/-- The imaginary part dominates `im b - r` when `‖a - b‖ < r`. -/
lemma im_gt_sub_norm {a b : ℍ} {r : ℝ} (h : ‖(a : ℂ) - (b : ℂ)‖ < r) : b.im - r < a.im := by
  have h1 : |(a : ℂ).im - (b : ℂ).im| ≤ ‖(a : ℂ) - (b : ℂ)‖ := by
    rw [show (a : ℂ).im - (b : ℂ).im = ((a : ℂ) - (b : ℂ)).im by simp]
    exact Complex.abs_im_le_norm _
  have h2 := (abs_lt.mp (lt_of_le_of_lt h1 h)).1
  simp only [UpperHalfPlane.coe_im] at h2
  linarith

/-- Euclidean distance of two `S`-conjugates. -/
lemma norm_S_sub_S (z z₀ : ℍ) :
    ‖((ModularGroup.S • z : ℍ) : ℂ) - ((ModularGroup.S • z₀ : ℍ) : ℂ)‖
      = ‖(z : ℂ) - (z₀ : ℂ)‖ / (‖(z : ℂ)‖ * ‖(z₀ : ℂ)‖) := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hz₀ : (z₀ : ℂ) ≠ 0 := z₀.ne_zero
  have h1 : ((ModularGroup.S • z : ℍ) : ℂ) = (-(z : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  have h2 : ((ModularGroup.S • z₀ : ℍ) : ℂ) = (-(z₀ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  rw [h1, h2]
  have h3 : (-(z : ℂ))⁻¹ - (-(z₀ : ℂ))⁻¹ = -((z : ℂ)⁻¹ - (z₀ : ℂ)⁻¹) := by ring
  rw [h3, norm_neg, inv_sub_inv hz hz₀, norm_div, norm_mul, norm_sub_rev]

/-- The imaginary part of `S z₀`. -/
lemma im_S (z₀ : ℍ) : (ModularGroup.S • z₀ : ℍ).im = z₀.im / ‖(z₀ : ℂ)‖ ^ 2 := by
  have h1 : ((ModularGroup.S • z₀ : ℍ) : ℂ) = (-(z₀ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  have h2 : (ModularGroup.S • z₀ : ℍ).im = ((-(z₀ : ℂ))⁻¹).im := by
    rw [← UpperHalfPlane.coe_im (ModularGroup.S • z₀), h1]
  rw [h2, Complex.inv_im, Complex.neg_im, UpperHalfPlane.coe_im, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq]
  ring

/-! ## The one-zero bound for functions on `ℍ` -/

/-- **One-zero bound on `ℍ`** (Euclidean distances). -/
theorem one_zero_apply {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {c : ℍ} {r M : ℝ}
    (hr0 : 0 < r) (hr : r < c.im)
    (hbd : ∀ w : ℍ, ‖(w : ℂ) - (c : ℂ)‖ ≤ r → ‖f w‖ ≤ M)
    {w₀ : ℍ} (hw₀ : ‖(w₀ : ℂ) - (c : ℂ)‖ < r / 2) (hz : f w₀ = 0) :
    ∀ w : ℍ, ‖(w : ℂ) - (c : ℂ)‖ < r / 2 → ‖f w‖ ≤ (2 * M / r) * ‖(w : ℂ) - (w₀ : ℂ)‖ := by
  intro w hw
  set F : ℂ → ℂ := fun u => f (UpperHalfPlane.ofComplex u) with hFdef
  have hsub : Metric.closedBall (c : ℂ) r ⊆ {u : ℂ | 0 < u.im} := closedBall_subset_upper hr
  have hof : ∀ (u : ℂ) (hu : 0 < u.im), UpperHalfPlane.ofComplex u = ⟨u, hu⟩ :=
    fun u hu => UpperHalfPlane.ofComplex_apply_of_im_pos hu
  have hF : DiffContOnCl ℂ F (Metric.ball (c : ℂ) r) := by
    have hdiff : DifferentiableOn ℂ F {u : ℂ | 0 < u.im} := by
      intro u hu
      have := differentiableAt_comp_ofComplex_of_mdiff hf (⟨u, hu⟩ : ℍ)
      simpa only [hFdef] using this.differentiableWithinAt
    exact hdiff.diffContOnCl_ball hsub
  have hbdF : ∀ u ∈ Metric.ball (c : ℂ) r, ‖F u‖ ≤ M := by
    intro u hu
    have hu' : 0 < u.im := hsub (Metric.ball_subset_closedBall hu)
    have h1 : ‖u - (c : ℂ)‖ ≤ r := le_of_lt (by simpa [dist_eq_norm] using hu)
    have h2 := hbd ⟨u, hu'⟩ h1
    show ‖f (UpperHalfPlane.ofComplex u)‖ ≤ M
    rw [hof u hu']
    exact h2
  have h0F : F (w₀ : ℂ) = 0 := by
    simp only [hFdef, UpperHalfPlane.ofComplex_apply, hz]
  have hmain := norm_le_mul_dist_of_one_zero hr0 hF hbdF (z₁ := (w₀ : ℂ))
    (by simpa [dist_eq_norm] using hw₀) h0F
  have hw' : (w : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hw
  have h := hmain (w : ℂ) hw'
  simp only [hFdef, UpperHalfPlane.ofComplex_apply] at h
  exact h

/-! ## The local one-zero bounds for the cleared kernel -/

/-- **The cleared kernel vanishes at least linearly in `τ` at the diagonal `τ = z`.** -/
theorem one_zero_diag_at (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z₀ : ℍ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ τ z : ℍ, ‖(τ : ℂ) - (z₀ : ℂ)‖ < ρ →
      ‖(z : ℂ) - (z₀ : ℂ)‖ < ρ → ‖KfunClear ℓ d τ z‖ ≤ C * ‖(τ : ℂ) - (z : ℂ)‖ := by
  obtain ⟨M, hM, hMb⟩ := exists_bound_KfunClear_of_balls ℓ d hd z₀ z₀
    (R₁ := 3 * z₀.im / 4) (R₂ := 3 * z₀.im / 4) (by linarith [z₀.im_pos])
    (by linarith [z₀.im_pos])
  refine ⟨z₀.im / 32, 16 * M / z₀.im, by linarith [z₀.im_pos], by positivity,
    fun τ z hτ hz => ?_⟩
  set δ : ℝ := z₀.im / 8 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith [z₀.im_pos]
  have hr : δ < z.im := by
    have h1 := im_gt_sub_norm hz
    rw [hδdef]
    linarith [z₀.im_pos]
  have hbd : ∀ w : ℍ, ‖(w : ℂ) - (z : ℂ)‖ ≤ δ → ‖KfunClear ℓ d w z‖ ≤ M := by
    intro w hw
    have h1 : ‖(w : ℂ) - (z₀ : ℂ)‖ ≤ 3 * z₀.im / 4 := by
      have h2 := norm_sub_le_three w z₀ z
      rw [hδdef] at hw
      linarith [z₀.im_pos]
    have h3 : ‖(z : ℂ) - (z₀ : ℂ)‖ ≤ 3 * z₀.im / 4 := by linarith [z₀.im_pos]
    exact hMb _ _ h1 h3
  have hmain := one_zero_apply (mdifferentiable_KfunClear_fst ℓ d hd z) hδ hr hbd
    (w₀ := z) (by rw [sub_self, norm_zero]; linarith) (KfunClear_self ℓ d hd z)
  have hτ2 : ‖(τ : ℂ) - (z : ℂ)‖ < δ / 2 := by
    have h2 := norm_sub_le_three τ z z₀
    rw [norm_sub_rev (z₀ : ℂ) (z : ℂ)] at h2
    rw [hδdef]
    linarith [z₀.im_pos]
  have h := hmain τ hτ2
  rw [hδdef] at h
  have hrw : 2 * M / (z₀.im / 8) = 16 * M / z₀.im := by
    have hz : z₀.im ≠ 0 := ne_of_gt z₀.im_pos
    field_simp
    ring
  rw [hrw] at h
  exact h

/-- **The cleared kernel vanishes at least linearly in `τ` at the `S`-conjugate `τ = S z`.** -/
theorem one_zero_S_at (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z₀ : ℍ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ τ z : ℍ, ‖(z : ℂ) - (z₀ : ℂ)‖ < ρ →
      ‖(τ : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ < ρ →
      ‖KfunClear ℓ d τ z‖ ≤ C * ‖(τ : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ := by
  set w₀ : ℍ := ModularGroup.S • z₀ with hw₀
  have hw₀pos : 0 < w₀.im := w₀.im_pos
  have hw₀val : w₀.im = z₀.im / ‖(z₀ : ℂ)‖ ^ 2 := by
    rw [hw₀]; exact im_S z₀
  have hz₀pos : 0 < ‖(z₀ : ℂ)‖ := norm_pos_iff.mpr z₀.ne_zero
  obtain ⟨M, hM, hMb⟩ := exists_bound_KfunClear_of_balls ℓ d hd w₀ z₀
    (R₁ := 3 * w₀.im / 4) (R₂ := 3 * z₀.im / 4) (by linarith) (by linarith [z₀.im_pos])
  refine ⟨min (min (‖(z₀ : ℂ)‖ / 2) (z₀.im / 8)) (w₀.im / 16), 16 * M / w₀.im, ?_,
    by positivity, fun τ z hz hτ => ?_⟩
  · exact lt_min (lt_min (by positivity) (by linarith [z₀.im_pos])) (by linarith)
  · set uz : ℍ := ModularGroup.S • z with huz
    have hz1 : ‖(z : ℂ) - (z₀ : ℂ)‖ < z₀.im / 8 :=
      lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_right _ _))
    have hz2 : ‖(z : ℂ) - (z₀ : ℂ)‖ < ‖(z₀ : ℂ)‖ / 2 :=
      lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_left _ _))
    have huzw : ‖(uz : ℂ) - (w₀ : ℂ)‖ < w₀.im / 4 := by
      have h1 : ‖(uz : ℂ) - (w₀ : ℂ)‖
          = ‖(z : ℂ) - (z₀ : ℂ)‖ / (‖(z : ℂ)‖ * ‖(z₀ : ℂ)‖) := by
        rw [huz, hw₀]; exact norm_S_sub_S z z₀
      rw [h1, div_lt_iff₀ (mul_pos (norm_pos_iff.mpr z.ne_zero) hz₀pos)]
      have hz3 : ‖(z : ℂ)‖ * ‖(z₀ : ℂ)‖ ≥ ‖(z₀ : ℂ)‖ ^ 2 / 2 := by
        have h := abs_norm_sub_norm_le (z₀ : ℂ) (z : ℂ)
        rw [norm_sub_rev] at h
        have h4 := (abs_le.mp h).2
        nlinarith [hz2, hz₀pos, norm_nonneg (z : ℂ)]
      have hkey : z₀.im / 8 ≤ (w₀.im / 4) * (‖(z : ℂ)‖ * ‖(z₀ : ℂ)‖) := by
        have h5 : z₀.im / 8 = (w₀.im / 4) * (‖(z₀ : ℂ)‖ ^ 2 / 2) := by
          rw [hw₀val]
          field_simp
          ring
        rw [h5]
        exact mul_le_mul_of_nonneg_left hz3 (by positivity)
      linarith [hz1, hkey]
    set δ : ℝ := w₀.im / 8 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; linarith
    have hr : δ < uz.im := by
      have h1 := im_gt_sub_norm huzw
      rw [hδdef]
      linarith
    have hbd : ∀ w : ℍ, ‖(w : ℂ) - (uz : ℂ)‖ ≤ δ → ‖KfunClear ℓ d w z‖ ≤ M := by
      intro w hw
      have h1 : ‖(w : ℂ) - (w₀ : ℂ)‖ ≤ 3 * w₀.im / 4 := by
        have h2 := norm_sub_le_three w w₀ uz
        rw [hδdef] at hw
        linarith
      have h3 : ‖(z : ℂ) - (z₀ : ℂ)‖ ≤ 3 * z₀.im / 4 := by linarith [z₀.im_pos, hz1]
      exact hMb _ _ h1 h3
    have hzero : KfunClear ℓ d uz z = 0 := by
      rw [huz]; exact KfunClear_S_self ℓ d hd z
    have hmain := one_zero_apply (mdifferentiable_KfunClear_fst ℓ d hd z) hδ hr hbd
      (w₀ := uz) (by rw [sub_self, norm_zero]; linarith) hzero
    have hτ2 : ‖(τ : ℂ) - (uz : ℂ)‖ < δ / 2 := by
      rw [hδdef]
      have h := lt_of_lt_of_le hτ (min_le_right _ _)
      linarith
    have h := hmain τ hτ2
    rw [hδdef] at h
    have hrw : 2 * M / (w₀.im / 8) = 16 * M / w₀.im := by
      have hz : w₀.im ≠ 0 := ne_of_gt hw₀pos
      field_simp
      ring
    rw [hrw] at h
    simpa only [huz] using h

end KbcAux

open KbcAux

/-! ## Auxiliary facts about the contour point -/

lemma ofComplex_coeKbc (τ : ℍ) : UpperHalfPlane.ofComplex (τ : ℂ) = τ := by
  have h := UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos
  exact UpperHalfPlane.ext (by simpa using congrArg Subtype.val h)

/-! ## The parameter space and the contour segment -/

/-- The parameter space `K × [1,B]` of the far-range estimate. -/
def PspaceKbc (K : Set ℍ) (B : ℝ) : Set (ℍ × ℝ) := K ×ˢ Set.Icc 1 B

lemma isCompact_PspaceKbc {K : Set ℍ} (hK : IsCompact K) (B : ℝ) : IsCompact (PspaceKbc K B) :=
  hK.prod isCompact_Icc

lemma mem_PspaceKbc {K : Set ℍ} {B : ℝ} {q : ℍ × ℝ} :
    q ∈ PspaceKbc K B ↔ q.1 ∈ K ∧ 1 ≤ q.2 ∧ q.2 ≤ B :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The contour segment `{it : 1 ≤ t ≤ B}`. -/
def CsegKbc (B : ℝ) : Set ℍ := ct '' Set.Icc 1 B

lemma continuousOn_ct_Icc (B : ℝ) : ContinuousOn ct (Set.Icc 1 B) := by
  have h1 : ContinuousOn (fun t : ℝ => UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))
      (Set.Ioi 0) := UpperHalfPlane.continuousOn_ofComplex_I_mul
  refine (h1.mono ?_).congr ?_
  · intro t ht
    exact Set.mem_Ioi.mpr (by linarith [Set.mem_Icc.mp ht])
  · intro t _
    show ct t = UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))
    exact congrArg UpperHalfPlane.ofComplex (mul_comm (t : ℂ) Complex.I)

lemma isCompact_CsegKbc (B : ℝ) : IsCompact (CsegKbc B) :=
  IsCompact.image_of_continuousOn isCompact_Icc (continuousOn_ct_Icc B)

lemma ct_mem_Cseg {t B : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ B) : ct t ∈ CsegKbc B :=
  ⟨t, Set.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩

/-- The scale of a contour point is bounded by `B + 2`. -/
lemma scale_ct_le {t B : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ B) : scale (ct t) ≤ B + 2 := by
  have ht : 0 < t := by linarith
  have him : (ct t).im = t := ct_im ht
  have hnorm : ‖(ct t : ℂ)‖ = t := by
    rw [ct_coe ht, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have h3 : scale = fun z : ℍ => 1 + (z.im)⁻¹ + ‖(z : ℂ)‖ := rfl
  rw [h3]
  simp only [him, hnorm]
  have hinv : (t)⁻¹ ≤ 1 := (inv_le_one₀ ht).mpr h1
  linarith

/-- Bounds for `KfunClear` on the box `K × {it : t ∈ [1,B]}`. -/
lemma exists_bound_KfunClear_box (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {B : ℝ} (hB : 1 ≤ B) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ ∈ K, ∀ t : ℝ, 1 ≤ t → t ≤ B → ‖KfunClear ℓ d τ (ct t)‖ ≤ M := by
  obtain ⟨R₁, hR₁, hb₁⟩ := exists_scale_bound_of_isCompact hK
  have hR₂ : 0 < B + 2 := by linarith
  obtain ⟨M, hM, h⟩ := exists_bound_KfunClear_of_scale_bounds (S := K)
    (T := {z : ℍ | scale z ≤ B + 2}) ℓ d hd hR₁ hR₂ hb₁ (fun z hz => hz)
  exact ⟨M, hM, fun τ hτ t ht1 htB => h τ hτ (ct t) (scale_ct_le ht1 htB)⟩

/-- `Δ` is bounded below on the contour segment. -/
lemma exists_lower_Delta_ct {B : ℝ} (hB : 1 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 1 ≤ t → t ≤ B → δ ≤ ‖DeltaFun (ct t)‖ := by
  obtain ⟨δ, hδ, h⟩ := exists_lower_DeltaFun (isCompact_CsegKbc B)
  exact ⟨δ, hδ, fun t ht1 htB => h (ct t) (ct_mem_Cseg ht1 htB)⟩

/-! ## Continuity of `t ↦ j (it)` -/

lemma mdiff_jInvariantFunKbc : MDiff jInvariantFun := by
  have hE4 : MDiff (fun τ : ℍ => E4Fun τ) := ModularFormClass.holo ModularForm.E₄
  have hΔ : MDiff (fun τ : ℍ => DeltaFun τ) := CuspFormClass.holo CuspForm.discriminant
  change MDiff (fun τ : ℍ => E4Fun τ ^ 3 / DeltaFun τ)
  exact (hE4.pow 3).div hΔ (fun z => ClassicalFacts.DeltaFun_ne_zero z)

lemma continuousOn_jInvariantFun_ofComplex :
    ContinuousOn (fun w : ℂ => jInvariantFun (UpperHalfPlane.ofComplex w)) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp mdiff_jInvariantFunKbc).continuousOn

lemma continuousAt_jInvariantFun_ct {t₀ : ℝ} (h₀ : 0 < t₀) :
    ContinuousAt (fun t : ℝ => jInvariantFun (ct t)) t₀ := by
  have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) * Complex.I) t₀ :=
    (Complex.continuous_ofReal.mul continuous_const).continuousAt
  have h2 : ContinuousAt (fun w : ℂ => jInvariantFun (UpperHalfPlane.ofComplex w))
      ((t₀ : ℂ) * Complex.I) :=
    continuousOn_jInvariantFun_ofComplex.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by
        show 0 < ((t₀ : ℂ) * Complex.I).im
        rw [Complex.mul_im]
        simpa using h₀))
  exact h2.comp (x := t₀) h1

/-- A neighbourhood on which `j` does not move much, in the `τ`-variable. -/
lemma exists_norm_lt_jInvariantFunKbc (τ₀ : ℍ) {e : ℝ} (he : 0 < e) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ : ℍ, ‖(τ : ℂ) - (τ₀ : ℂ)‖ < r →
      ‖jInvariantFun τ - jInvariantFun τ₀‖ < e := by
  have hcont : ContinuousAt (fun w : ℂ => jInvariantFun (UpperHalfPlane.ofComplex w))
      (τ₀ : ℂ) :=
    continuousOn_jInvariantFun_ofComplex.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ₀.im_pos)
  obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.mp hcont e he
  refine ⟨r, hr, fun τ hτ => ?_⟩
  have h1 := h (by rw [dist_eq_norm]; exact hτ)
  rw [dist_eq_norm, ofComplex_coeKbc, ofComplex_coeKbc] at h1
  exact h1

/-- A neighbourhood on which `j (it)` does not move much. -/
lemma exists_norm_lt_jInvariantFun_ct {t₀ : ℝ} (h₀ : 0 < t₀) {e : ℝ} (he : 0 < e) :
    ∃ s : ℝ, 0 < s ∧ ∀ t : ℝ, |t - t₀| < s →
      ‖jInvariantFun (ct t) - jInvariantFun (ct t₀)‖ < e := by
  obtain ⟨s, hs, h⟩ := Metric.continuousAt_iff.mp (continuousAt_jInvariantFun_ct h₀) e he
  refine ⟨s, hs, fun t ht => ?_⟩
  have h1 := h (by rw [Real.dist_eq]; exact ht)
  rwa [dist_eq_norm] at h1

/-! ## The local bound away from the coincidences -/

lemma norm_growthPrefactorKbc (d : ℕ) (τ z : ℍ) :
    ‖growthPrefactor d τ z‖
      = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2)
        * ‖jInvariantFun τ - jInvariantFun z‖ := by
  simp only [growthPrefactor, norm_mul, norm_pow]

lemma div_two_eq_of_mul (g P M p m : ℂ) (h1 : p = g * P) (h2 : m = g * M) (hg : g ≠ 0) :
    (P + M) / 2 = (p + m) / 2 / g := by
  rw [h1, h2, ← mul_add, mul_div_assoc, mul_div_cancel_left₀ _ hg]

lemma Kfun_eq_KfunClear_div (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ)
    (h : jInvariantFun τ ≠ jInvariantFun z) :
    Kfun ℓ d τ z = KfunClear ℓ d τ z / growthPrefactor d τ z := by
  have h1 := ClearLink.KPlusClear_eq_smul d hd τ z h
  have h2 := ClearLink.KMinusClear_eq_smul ℓ d hd τ z h
  have hg : growthPrefactor d τ z ≠ 0 := by
    simp only [growthPrefactor]
    exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _))) (sub_ne_zero.mpr h)
  rw [show Kfun ℓ d τ z = (KPlus d τ z + KMinus ℓ d τ z) / 2 from rfl,
    show KfunClear ℓ d τ z = (KPlusClear d τ z + KMinusClear ℓ d τ z) / 2 from rfl]
  exact div_two_eq_of_mul (growthPrefactor d τ z) (KPlus d τ z) (KMinus ℓ d τ z)
    (KPlusClear d τ z) (KMinusClear ℓ d τ z) h1 h2 hg

/-- **The local bound at a parameter point which is not a coincidence** (with the growth
exponent of `growthPrefactor` exposed as a parameter, so that the arithmetic is carried out
with a variable exponent). -/
theorem exists_local_bound_clean_aux (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {B : ℝ} (hB : 1 ≤ B) (e : ℕ)
    (hgp : ∀ τ z : ℍ, ‖growthPrefactor d τ z‖
      = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e * ‖jInvariantFun τ - jInvariantFun z‖)
    (p : ℍ × ℝ) (hp : p ∈ PspaceKbc K B)
    (hne : jInvariantFun p.1 ≠ jInvariantFun (ct p.2)) :
    ∃ U : Set (ℍ × ℝ), IsOpen U ∧ p ∈ U ∧
      ∃ C : ℝ, ∀ q ∈ U, q ∈ PspaceKbc K B → ‖Kaxis (Kfun ℓ d) q.1 q.2‖ ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := exists_bound_KfunClear_box ℓ d hd hK hB
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_lower_DeltaFun hK
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_lower_Delta_ct hB
  obtain ⟨hpK, hp1, hpB⟩ := mem_PspaceKbc.mp hp
  have hp2 : 0 < p.2 := by linarith
  set Jp : ℝ := ‖jInvariantFun p.1 - jInvariantFun (ct p.2)‖ with hJp
  have hJppos : 0 < Jp := by rw [hJp]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h3pos : (0 : ℝ) < Jp / 3 := by linarith
  obtain ⟨r₁, hr₁pos, hr₁⟩ := exists_norm_lt_jInvariantFunKbc p.1 h3pos
  obtain ⟨r₂, hr₂pos, hr₂⟩ := exists_norm_lt_jInvariantFun_ct hp2 h3pos
  have hc1 : Continuous fun q : ℍ × ℝ => ‖(q.1 : ℂ) - (p.1 : ℂ)‖ := by
    have hval : Continuous fun q : ℍ × ℝ => ((q.1 : ℍ) : ℂ) :=
      UpperHalfPlane.continuous_coe.comp continuous_fst
    have h : Continuous fun q : ℍ × ℝ => ((q.1 : ℂ) - (p.1 : ℂ)) :=
      hval.sub continuous_const
    exact continuous_norm.comp h
  have hc2 : Continuous fun q : ℍ × ℝ => |q.2 - p.2| := by
    have h : Continuous fun q : ℍ × ℝ => (q.2 - p.2) :=
      continuous_snd.sub continuous_const
    exact continuous_abs.comp h
  refine ⟨{q : ℍ × ℝ | ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < r₁ ∧ |q.2 - p.2| < r₂}, ?_, ?_, ?_⟩
  · exact (isOpen_lt hc1 continuous_const).inter (isOpen_lt hc2 continuous_const)
  · constructor
    · show ‖(p.1 : ℂ) - (p.1 : ℂ)‖ < r₁
      rw [sub_self, norm_zero]; exact hr₁pos
    · show |p.2 - p.2| < r₂
      rw [sub_self, abs_zero]; exact hr₂pos
  · refine ⟨M / (δ₁ * δ₂ ^ e * (Jp / 3)), fun q hq hqP => ?_⟩
    obtain ⟨hqK, hq1, hqB⟩ := mem_PspaceKbc.mp hqP
    obtain ⟨hqr₁, hqr₂⟩ := hq
    have hq2 : 0 < q.2 := by linarith
    have hJ1 : ‖jInvariantFun q.1 - jInvariantFun p.1‖ < Jp / 3 := hr₁ q.1 hqr₁
    have hJ2 : ‖jInvariantFun (ct q.2) - jInvariantFun (ct p.2)‖ < Jp / 3 := hr₂ q.2 hqr₂
    have hrew : jInvariantFun p.1 - jInvariantFun (ct p.2)
        = ((jInvariantFun q.1 - jInvariantFun (ct q.2))
            - (jInvariantFun q.1 - jInvariantFun p.1))
          + (jInvariantFun (ct q.2) - jInvariantFun (ct p.2)) := by ring
    have hJq : Jp / 3 ≤ ‖jInvariantFun q.1 - jInvariantFun (ct q.2)‖ := by
      have htri : ‖jInvariantFun p.1 - jInvariantFun (ct p.2)‖ ≤
          ‖jInvariantFun q.1 - jInvariantFun (ct q.2)‖ + Jp / 3 + Jp / 3 := by
        rw [hrew]
        have h1 := norm_add_le ((jInvariantFun q.1 - jInvariantFun (ct q.2))
          - (jInvariantFun q.1 - jInvariantFun p.1))
          (jInvariantFun (ct q.2) - jInvariantFun (ct p.2))
        have h2 := norm_sub_le (jInvariantFun q.1 - jInvariantFun (ct q.2))
          (jInvariantFun q.1 - jInvariantFun p.1)
        linarith
      have h3 : Jp ≤ ‖jInvariantFun q.1 - jInvariantFun (ct q.2)‖ + Jp / 3 + Jp / 3 := by
        rwa [hJp]
      linarith
    have hJpos : 0 < ‖jInvariantFun q.1 - jInvariantFun (ct q.2)‖ := by linarith
    have hjne : jInvariantFun q.1 ≠ jInvariantFun (ct q.2) := by
      intro h0
      rw [h0, sub_self, norm_zero] at hJpos
      exact lt_irrefl 0 hJpos
    have hKfun := Kfun_eq_KfunClear_div ℓ d hd q.1 (ct q.2) hjne
    have hMq := hM q.1 hqK q.2 hq1 hqB
    have hΔ1 := hδ₁ q.1 hqK
    have hΔ2 := hδ₂ q.2 hq1 hqB
    have hδpos : (0 : ℝ) < δ₁ * δ₂ ^ e * (Jp / 3) :=
      mul_pos (mul_pos hδ₁pos (pow_pos hδ₂pos e)) h3pos
    have hpre : δ₁ * δ₂ ^ e * (Jp / 3) ≤ ‖growthPrefactor d q.1 (ct q.2)‖ := by
      rw [hgp q.1 (ct q.2)]
      have h2 : δ₂ ^ e ≤ ‖DeltaFun (ct q.2)‖ ^ e := pow_le_pow_left₀ hδ₂pos.le hΔ2 e
      have h3 : (0:ℝ) ≤ δ₂ ^ e := pow_nonneg hδ₂pos.le e
      have h5 : δ₁ * δ₂ ^ e ≤ ‖DeltaFun q.1‖ * ‖DeltaFun (ct q.2)‖ ^ e :=
        mul_le_mul hΔ1 h2 h3 (norm_nonneg _)
      exact mul_le_mul h5 hJq h3pos.le (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) e))
    have hprepos : 0 < ‖growthPrefactor d q.1 (ct q.2)‖ := lt_of_lt_of_le hδpos hpre
    have hfinal : ‖KfunClear ℓ d q.1 (ct q.2)‖ / ‖growthPrefactor d q.1 (ct q.2)‖
        ≤ M / (δ₁ * δ₂ ^ e * (Jp / 3)) := by
      rw [div_le_div_iff₀ hprepos hδpos]
      exact le_trans (mul_le_mul_of_nonneg_right hMq hδpos.le)
        (mul_le_mul_of_nonneg_left hpre hMpos.le)
    simp only [Kaxis, dif_pos hq2, ← ct_eq_imagAxis hq2, hKfun, norm_div]
    exact hfinal

/-- **The local bound at a parameter point which is not a coincidence.** -/
theorem exists_local_bound_cleanKbc (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {B : ℝ} (hB : 1 ≤ B)
    (p : ℍ × ℝ) (hp : p ∈ PspaceKbc K B)
    (hne : jInvariantFun p.1 ≠ jInvariantFun (ct p.2)) :
    ∃ U : Set (ℍ × ℝ), IsOpen U ∧ p ∈ U ∧
      ∃ C : ℝ, ∀ q ∈ U, q ∈ PspaceKbc K B → ‖Kaxis (Kfun ℓ d) q.1 q.2‖ ≤ C :=
  exists_local_bound_clean_aux ℓ d hd hK hB (if d = 8 then 1 else 2)
    (fun τ z => norm_growthPrefactorKbc d τ z) p hp hne

/-! ## The local bound at a coincidence -/

/-- **The local bound at a parameter point which is a coincidence** `j τ = j (it)`.

The proof is the CKMRV residue computation: for `τ ∈ 𝒟` the only coincidences of the contour
with the `SL(2,ℤ)`-orbit of `τ` are `z = τ` and `z = S τ`, and the cleared kernel
`KfunClear` vanishes on both curves (`Work.Residues.KPlusClear_diag`,
`Work.Asymptotics.KClear_S_vanishing`); a one-zero mean-value estimate for the holomorphic
`z ↦ KfunClear(τ,z)` combined with the lower bound for `‖j τ - j z‖` (a strict derivative away
from the elliptic point `i`, a two-fold zero at `i`) bounds the quotient. -/
theorem exists_local_bound_coinc (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) (hsub : K ⊆ DomainD) {B : ℝ} (hB : 1 ≤ B)
    (p : ℍ × ℝ) (hp : p ∈ PspaceKbc K B)
    (hcoin : jInvariantFun p.1 = jInvariantFun (ct p.2)) :
    ∃ U : Set (ℍ × ℝ), IsOpen U ∧ p ∈ U ∧
      ∃ C : ℝ, ∀ q ∈ U, q ∈ PspaceKbc K B → ‖Kaxis (Kfun ℓ d) q.1 q.2‖ ≤ C := by
  obtain ⟨hpK, hp1, hpB⟩ := mem_PspaceKbc.mp hp
  have hp2 : 0 < p.2 := by linarith
  obtain ⟨r, hr, C, hC, hloc⟩ := Kaxis_local_coincidence ℓ d hd (hsub hpK) hp2
    (by rw [← ct_eq_imagAxis hp2]; exact hcoin)
  refine ⟨{q : ℍ × ℝ | dist q.1 p.1 < r ∧ |q.2 - p.2| < r},
    (Metric.isOpen_ball.preimage continuous_fst).inter
      (isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const),
    ⟨by rw [dist_self]; exact hr, by rw [sub_self, abs_zero]; exact hr⟩, C, ?_⟩
  intro q hq hqP
  obtain ⟨hqK, hq1, hqB⟩ := mem_PspaceKbc.mp hqP
  obtain ⟨hq1', hq2'⟩ := hq
  exact hloc q.1 q.2 (hsub hqK) (by linarith) hq1' hq2'

/-! ## Boundedness of a locally bounded function on a compact set -/

theorem isCompact_bounded_of_local {X : Type*} [PseudoMetricSpace X] {s : Set X}
    (hs : IsCompact s) {f : X → ℂ}
    (hloc : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ C, ∀ y ∈ s, y ∈ U → ‖f y‖ ≤ C) :
    ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨0, by simp⟩
  have h : ∀ x : s, ∃ U : Set X, IsOpen U ∧ (x : X) ∈ U ∧
      ∃ C : ℝ, ∀ y ∈ s, y ∈ U → ‖f y‖ ≤ C := fun x => hloc x.1 x.2
  choose U hUop hxU C hC using h
  obtain ⟨b', -, hb'fin, hcover⟩ := hs.elim_finite_subcover_image (b := Set.univ) (c := U)
    (fun i _ => hUop i) (fun y hy => by
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨⟨y, hy⟩, Set.mem_univ _, hxU ⟨y, hy⟩⟩)
  have hb'ne : hb'fin.toFinset.Nonempty := by
    obtain ⟨y₀, hy₀⟩ := hsne
    obtain ⟨i, hi, -⟩ : ∃ i, i ∈ b' ∧ y₀ ∈ U i := by
      have := hcover hy₀
      simpa only [Set.mem_iUnion, exists_prop] using this
    exact ⟨i, (Set.Finite.mem_toFinset hb'fin).mpr hi⟩
  refine ⟨hb'fin.toFinset.sup' hb'ne C, fun x hx => ?_⟩
  obtain ⟨i, hi, hxi⟩ : ∃ i, i ∈ b' ∧ x ∈ U i := by
    have := hcover hx
    simpa only [Set.mem_iUnion, exists_prop] using this
  exact le_trans (hC i x hx hxi)
    (Finset.le_sup' C ((Set.Finite.mem_toFinset hb'fin).mpr hi))

/-- The CKMRV kernel on the contour is bounded on `K × [1,T]` for `K ⊆ 𝒟` compact. -/
theorem Kaxis_bounded_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → 1 ≤ t → t ≤ T →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ B := by
  classical
  rcases lt_or_ge T 1 with hT | hT
  · refine ⟨0, le_rfl, fun τ t hτ h1 h2 => ?_⟩
    exfalso
    linarith
  · have hloc : ∀ p ∈ PspaceKbc K T, ∃ U : Set (ℍ × ℝ), IsOpen U ∧ p ∈ U ∧
        ∃ C : ℝ, ∀ q ∈ U, q ∈ PspaceKbc K T → ‖Kaxis (Kfun ℓ d) q.1 q.2‖ ≤ C := by
      intro p hp
      rcases eq_or_ne (jInvariantFun p.1) (jInvariantFun (ct p.2)) with hcoin | hne
      · exact exists_local_bound_coinc ℓ d hd hK hsub hT p hp hcoin
      · exact exists_local_bound_cleanKbc ℓ d hd hK hT p hp hne
    obtain ⟨C, hC⟩ := isCompact_bounded_of_local (isCompact_PspaceKbc hK T)
      (fun p hp => by
        obtain ⟨U, hUop, hpU, C', hC'⟩ := hloc p hp
        exact ⟨U, hUop, hpU, C', fun q hq hqU => hC' q hqU hq⟩)
    refine ⟨max C 0, le_max_right _ _, fun τ t hτ h1 h2 => ?_⟩
    have hq : (τ, t) ∈ PspaceKbc K T := mem_PspaceKbc.mpr ⟨hτ, h1, h2⟩
    have h0t : 0 < t := by linarith
    have h := hC (τ, t) hq
    have h2' : ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
      simpa only [Kaxis, dif_pos h0t, ← ct_eq_imagAxis h0t] using h
    exact le_trans h2' (le_max_left _ _)

end Work.Asymptotics
