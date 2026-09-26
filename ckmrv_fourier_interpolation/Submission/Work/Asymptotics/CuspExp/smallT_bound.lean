import Mathlib
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Asymptotics.CuspExp.Basic
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.MiddleRange.Basic
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.MiddleRange.Coincidence
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Asymptotics.CuspExp

open UpperHalfPlane
open scoped Topology

noncomputable section

namespace SmallT

open Work.Kernels

/-! ## Self-contained copies of the local analytic inputs

The following two namespaces contain verbatim copies of the lemmas we use from
`Submission/Work/Asymptotics/Kaxis_bounded_compact.lean` and from
`Submission/Work/Asymptotics/MiddleRange/exists_local_bound_at_I.lean` together with
`.../exists_diffQuotient_lower_general.lean`, so that this file does not depend on those
(each of which is being reworked in parallel).  Only the statements are new here; the proofs are
those of the respective files. -/

namespace KbcAux
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Metric Filter Complex
open Work.Kernels
set_option maxHeartbeats 1600000

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

namespace MiddleRange
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Metric Filter Complex
open Work.Kernels
open Work.Asymptotics.MiddleRange


/-! ## Elementary facts about the elliptic point `i` -/

/-- `S` fixes `i`. -/
lemma S_smul_I : ModularGroup.S • (UpperHalfPlane.I : ℍ) = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul, UpperHalfPlane.coe_I]
  have h : (-1 : ℂ) / Complex.I = Complex.I := by
    rw [div_eq_mul_inv, Complex.inv_I]; ring
  exact h

/-- The only fixed point of `S` in `ℍ` is `i`. -/
lemma eq_I_of_S_smul_eq {z : ℍ} (h : ModularGroup.S • z = z) : z = UpperHalfPlane.I := by
  have h1 : (z : ℂ) = (-1 : ℂ) / (z : ℂ) := by
    have hh := congrArg (fun w : ℍ => (w : ℂ)) h
    rw [coe_S_smul] at hh
    exact hh.symm
  have hz : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have h2 : (z : ℂ) ^ 2 = -1 := by
    have hmul := congrArg (fun w : ℂ => w * (z : ℂ)) h1
    simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hz, mul_one] at hmul
    simpa [pow_two] using hmul
  have hsq : (z : ℂ) ^ 2 = Complex.I ^ 2 := by rw [h2, Complex.I_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h3 | h3
  · exact UpperHalfPlane.ext h3
  · exfalso
    have him : (z : ℂ).im = -1 := by rw [h3]; simp
    rw [UpperHalfPlane.coe_im] at him
    linarith [z.im_pos]

/-- The norm bound `1/2 ≤ ‖w‖` on the disc of radius `1/2` around `i`. -/
lemma half_le_norm_of_norm_sub_I_lt {w : ℍ} (hw : ‖(w : ℂ) - Complex.I‖ < 1 / 2) :
    (1 : ℝ) / 2 ≤ ‖(w : ℂ)‖ := by
  have h1 : ‖(w : ℂ)‖ ≥ (1 : ℝ) - ‖(w : ℂ) - Complex.I‖ := by
    have hsub := norm_sub_le (w : ℂ) ((w : ℂ) - Complex.I)
    rw [show (w : ℂ) - ((w : ℂ) - Complex.I) = Complex.I by ring, Complex.norm_I] at hsub
    linarith
  linarith

/-! ## A two-zero maximum modulus bound for functions on `ℍ` -/

/-- **Two-zero bound on `ℍ`** (Euclidean distances).  A holomorphic function on `ℍ`, bounded by
`M` on the Euclidean ball of radius `r` around `c` and vanishing at two distinct points `w₁ ≠ w₂`
of the half ball, obeys `‖f w‖ ≤ (4 M / r²) ‖w - w₁‖ ‖w - w₂‖` there. -/
theorem two_zero_apply {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {c : ℍ} {r M : ℝ}
    (hr0 : 0 < r) (hr : r < c.im) (hM : 0 ≤ M)
    (hbd : ∀ w : ℍ, ‖(w : ℂ) - (c : ℂ)‖ ≤ r → ‖f w‖ ≤ M)
    {w₁ w₂ : ℍ} (h₁ : ‖(w₁ : ℂ) - (c : ℂ)‖ < r / 2) (h₂ : ‖(w₂ : ℂ) - (c : ℂ)‖ < r / 2)
    (hne : w₁ ≠ w₂) (hz₁ : f w₁ = 0) (hz₂ : f w₂ = 0) :
    ∀ w : ℍ, ‖(w : ℂ) - (c : ℂ)‖ < r / 2 →
      ‖f w‖ ≤ (4 * M / r ^ 2) * ‖(w : ℂ) - (w₁ : ℂ)‖ * ‖(w : ℂ) - (w₂ : ℂ)‖ := by
  intro w hw
  set F : ℂ → ℂ := fun u => f (UpperHalfPlane.ofComplex u) with hFdef
  have hsub : Metric.closedBall (c : ℂ) r ⊆ {u : ℂ | 0 < u.im} :=
    KbcAux.closedBall_subset_upper hr
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
    rw [hof u hu']; exact h2
  have hz₁F : F (w₁ : ℂ) = 0 := by
    simp only [hFdef, UpperHalfPlane.ofComplex_apply, hz₁]
  have hz₂F : F (w₂ : ℂ) = 0 := by
    simp only [hFdef, UpperHalfPlane.ofComplex_apply, hz₂]
  have hneF : (w₁ : ℂ) ≠ (w₂ : ℂ) := fun h => hne (UpperHalfPlane.ext h)
  have hb₁ : (w₁ : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact h₁
  have hb₂ : (w₂ : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact h₂
  have hw' : (w : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hw
  have hmain := norm_le_of_norm_le_of_two_zeros hr0 hM hF hbdF hb₁ hb₂ hneF hz₁F hz₂F
    (w : ℂ) hw'
  simpa only [hFdef, UpperHalfPlane.ofComplex_apply] using hmain

/-! ## Euclidean balls inside hyperbolic balls -/

/-- A Euclidean ball of radius `ρ ≤ im c / 2` around `c ∈ ℍ` is contained in the hyperbolic
closed ball of radius `1`. -/
lemma dist_le_one_of_norm_lt {c : ℍ} {ρ : ℝ} (hρ : ρ ≤ c.im / 2) {z : ℍ}
    (h : ‖(z : ℂ) - (c : ℂ)‖ < ρ) : dist z c ≤ 1 := by
  have h1 : dist z c ≤ ‖(z : ℂ) - (c : ℂ)‖ / Real.sqrt (z.im * c.im) := by
    simpa only [dist_eq_norm] using UpperHalfPlane.dist_le_dist_coe_div_sqrt z c
  have hzi : c.im / 2 ≤ z.im := by
    have h2 := KbcAux.im_gt_sub_norm (a := z) (b := c) h
    linarith
  have hsqrt : c.im / 2 ≤ Real.sqrt (z.im * c.im) := by
    have hsq : (c.im / 2) ^ 2 ≤ z.im * c.im := by nlinarith [c.im_pos, hzi]
    calc c.im / 2 = Real.sqrt ((c.im / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (z.im * c.im) := Real.sqrt_le_sqrt hsq
  have hsqrtpos : 0 < Real.sqrt (z.im * c.im) := Real.sqrt_pos.mpr (by positivity)
  have hnum : ‖(z : ℂ) - (c : ℂ)‖ < Real.sqrt (z.im * c.im) :=
    lt_of_lt_of_le (lt_of_lt_of_le h hρ) hsqrt
  have h3 : ‖(z : ℂ) - (c : ℂ)‖ / Real.sqrt (z.im * c.im) < 1 :=
    (div_lt_one hsqrtpos).mpr hnum
  linarith

/-! ## Quadratic vanishing of the cleared kernel near `(i,i)` -/

/-- **Quadratic vanishing of `KfunClear` near `i`.**  On a Euclidean neighbourhood of `(i,i)` the
cleared kernel is bounded by a constant times the product of the two distances to the two
branches: `‖KfunClear τ z‖ ≤ C ‖z - τ‖ ‖z - S τ‖`. -/
theorem two_zero_KfunClear_I (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ τ z : ℍ,
      ‖(τ : ℂ) - Complex.I‖ < ρ → ‖(z : ℂ) - Complex.I‖ < ρ →
      ‖KfunClear ℓ d τ z‖ ≤ C * ‖(z : ℂ) - (τ : ℂ)‖ *
        ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖ := by
  obtain ⟨M, hM, hMb⟩ := KbcAux.exists_bound_KfunClear_of_balls ℓ d hd UpperHalfPlane.I
    UpperHalfPlane.I (R₁ := 3 / 4) (R₂ := 3 / 4)
    (by rw [UpperHalfPlane.I_im]; norm_num) (by rw [UpperHalfPlane.I_im]; norm_num)
  refine ⟨1 / 32, 256 * M, by norm_num, by positivity, fun τ z hτ hz => ?_⟩
  have hτ4 : ‖(τ : ℂ) - Complex.I‖ < 1 / 4 := by linarith
  have hz4 : ‖(z : ℂ) - Complex.I‖ < 1 / 4 := by linarith
  have hτ8 : ‖(τ : ℂ) - Complex.I‖ < 1 / 8 := by linarith
  have hz8 : ‖(z : ℂ) - Complex.I‖ < 1 / 8 := by linarith
  have hτ34 : ‖(τ : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ ≤ 3 / 4 := by
    rw [UpperHalfPlane.coe_I]; linarith
  have hz34 : ‖(z : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ ≤ 3 / 4 := by
    rw [UpperHalfPlane.coe_I]; linarith
  have hτ8I : ‖(τ : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < 1 / 4 / 2 := by
    rw [UpperHalfPlane.coe_I]; linarith
  have hz8I : ‖(z : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < 1 / 4 / 2 := by
    rw [UpperHalfPlane.coe_I]; linarith
  have hSτ8 : ‖((ModularGroup.S • τ : ℍ) : ℂ) - Complex.I‖ < 1 / 8 := by
    linarith [norm_S_sub_I_le τ (half_le_norm_of_norm_sub_I_lt (by linarith : ‖(τ : ℂ) - Complex.I‖ < 1 / 2))]
  have hSz8 : ‖((ModularGroup.S • z : ℍ) : ℂ) - Complex.I‖ < 1 / 8 := by
    linarith [norm_S_sub_I_le z (half_le_norm_of_norm_sub_I_lt (by linarith : ‖(z : ℂ) - Complex.I‖ < 1 / 2))]
  have hSτ8I : ‖((ModularGroup.S • τ : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < 1 / 4 / 2 := by
    rw [UpperHalfPlane.coe_I]; linarith
  have hSz8I : ‖((ModularGroup.S • z : ℍ) : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ < 1 / 4 / 2 := by
    rw [UpperHalfPlane.coe_I]; linarith
  by_cases hτI : τ = UpperHalfPlane.I
  · -- `τ = i`: two-zero bound in the first variable
    subst hτI
    by_cases hzI : z = UpperHalfPlane.I
    · subst hzI
      rw [KfunClear, Work.Residues.KPlusClear_diag d hd UpperHalfPlane.I,
        Work.Residues.KMinusClear_diag ℓ d hd UpperHalfPlane.I]
      simp
    have hne1 : z ≠ ModularGroup.S • z := fun h => hzI (eq_I_of_S_smul_eq h.symm)
    have hmain := two_zero_apply (f := fun w : ℍ => KfunClear ℓ d w z)
      (KbcAux.mdifferentiable_KfunClear_fst ℓ d hd z) (c := UpperHalfPlane.I) (r := 1 / 4)
      (M := M) (by norm_num) (by rw [UpperHalfPlane.I_im]; norm_num) hM.le
      (fun w hw => hMb w z (by linarith) hz34)
      hz8I hSz8I hne1 (KfunClear_self_eq_zero ℓ d hd z) (KfunClear_S_eq_zero ℓ d hd z)
      UpperHalfPlane.I (by rw [sub_self, norm_zero]; norm_num)
    have hbound : ‖((ModularGroup.S • z : ℍ) : ℂ) - Complex.I‖ ≤ 4 * ‖(z : ℂ) - Complex.I‖ :=
      norm_S_sub_I_le z (half_le_norm_of_norm_sub_I_lt (by linarith : ‖(z : ℂ) - Complex.I‖ < 1 / 2))
    have hIz : ‖((UpperHalfPlane.I : ℍ) : ℂ) - (z : ℂ)‖ = ‖(z : ℂ) - Complex.I‖ := by
      rw [norm_sub_rev, UpperHalfPlane.coe_I]
    have hISz : ‖((UpperHalfPlane.I : ℍ) : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖
        ≤ 4 * ‖(z : ℂ) - Complex.I‖ := by
      rw [UpperHalfPlane.coe_I, norm_sub_rev]
      exact hbound
    calc ‖KfunClear ℓ d UpperHalfPlane.I z‖
        ≤ (4 * M / (1 / 4) ^ 2) * ‖(z : ℂ) - Complex.I‖ *
            (4 * ‖(z : ℂ) - Complex.I‖) := by
          refine le_trans hmain ?_
          rw [hIz]
          exact mul_le_mul_of_nonneg_left hISz (by positivity)
      _ = 256 * M * ‖(z : ℂ) - Complex.I‖ * ‖(z : ℂ) - Complex.I‖ := by ring
      _ ≤ 256 * M * ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ *
            ‖(z : ℂ) - ((ModularGroup.S • UpperHalfPlane.I : ℍ) : ℂ)‖ := by
          rw [S_smul_I, UpperHalfPlane.coe_I]
  · -- `τ ≠ i`: two-zero bound in the second variable
    have hne1 : τ ≠ ModularGroup.S • τ := fun h => hτI (eq_I_of_S_smul_eq h.symm)
    have hmain := two_zero_apply (f := fun w : ℍ => KfunClear ℓ d τ w)
      (KbcAux.mdifferentiable_KfunClear_snd ℓ d hd τ) (c := UpperHalfPlane.I) (r := 1 / 4)
      (M := M) (by norm_num) (by rw [UpperHalfPlane.I_im]; norm_num) hM.le
      (fun w hw => hMb τ w hτ34 (by linarith))
      hτ8I hSτ8I hne1 (KfunClear_self_eq_zero ℓ d hd τ) (KfunClear_smul_S_eq_zero ℓ d hd τ)
      z hz8I
    calc ‖KfunClear ℓ d τ z‖
        ≤ (4 * M / (1 / 4) ^ 2) * ‖(z : ℂ) - (τ : ℂ)‖ *
            ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖ := hmain
      _ ≤ 256 * M * ‖(z : ℂ) - (τ : ℂ)‖ *
            ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖ := by
          have h64 : (4 : ℝ) * M / (1 / 4) ^ 2 = 64 * M := by ring
          rw [h64]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          linarith

/-! ## `Δ` is bounded below near a point of `ℍ` -/

/-- `Δ` has no zeros on `ℍ`, hence is bounded below on a Euclidean neighbourhood of any point. -/
theorem exists_DeltaFun_lower (z₀ : ℍ) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ ∀ z : ℍ, ‖(z : ℂ) - (z₀ : ℂ)‖ < ρ → δ ≤ ‖DeltaFun z‖ := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_lower_DeltaFun (isCompact_closedBall z₀ 1)
  refine ⟨min (z₀.im / 2) 1, min δ 1, lt_min (by positivity) one_pos, lt_min hδpos one_pos,
    fun z hz => ?_⟩
  have hz' : ‖(z : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 := lt_of_lt_of_le hz (min_le_left _ _)
  have h1 : dist z z₀ ≤ 1 := dist_le_one_of_norm_lt (c := z₀) (le_refl _) hz'
  exact le_trans (min_le_left _ _) (hδ z h1)

/-! ## `j` dominates the product of the two distances near `i` -/

/-- Near `τ = z = i` the `j`-difference dominates the product `‖z - τ‖ ‖z - S τ‖`: this is the
combination of `Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I` with
`Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz`. -/
theorem j_lower_I : ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ τ z : ℍ,
    ‖(τ : ℂ) - Complex.I‖ < ρ → ‖(z : ℂ) - Complex.I‖ < ρ →
    c * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖
      ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
  obtain ⟨ρ₃, hρ₃, c₃, hc₃, hb₃⟩ := exists_lambdaFun_lipschitz UpperHalfPlane.I
  obtain ⟨ρ₄, hρ₄, c₄, hc₄, hb₄⟩ := exists_j_sub_lower_lambda_near_I
  set ρ : ℝ := min ρ₄ (min ρ₃ (min (ρ₃ / 4) (1 / 2))) with hρdef
  have hρpos : 0 < ρ :=
    lt_min hρ₄ (lt_min hρ₃ (lt_min (by linarith) (by norm_num)))
  refine ⟨ρ, c₄ * c₃ ^ 2, hρpos, by positivity, fun τ z hτ hz => ?_⟩
  have hτρ₄ : ‖(τ : ℂ) - Complex.I‖ < ρ₄ := lt_of_lt_of_le hτ (min_le_left _ _)
  have hzρ₄ : ‖(z : ℂ) - Complex.I‖ < ρ₄ := lt_of_lt_of_le hz (min_le_left _ _)
  have hτρ₃ : ‖(τ : ℂ) - Complex.I‖ < ρ₃ :=
    lt_of_lt_of_le hτ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzρ₃ : ‖(z : ℂ) - Complex.I‖ < ρ₃ :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hτ04 : ‖(τ : ℂ) - Complex.I‖ < ρ₃ / 4 :=
    lt_of_lt_of_le hτ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hτ12 : ‖(τ : ℂ) - Complex.I‖ < 1 / 2 :=
    lt_of_lt_of_le hτ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hSτ : ‖((ModularGroup.S • τ : ℍ) : ℂ) - Complex.I‖ < ρ₃ := by
    have h := norm_S_sub_I_le τ (half_le_norm_of_norm_sub_I_lt hτ12)
    linarith
  have hlam1 : c₃ * ‖(z : ℂ) - (τ : ℂ)‖ ≤ ‖lambdaFun τ - lambdaFun z‖ := by
    rw [norm_sub_rev (z : ℂ) (τ : ℂ)]
    exact hb₃ τ z hτρ₃ hzρ₃
  have hlS : c₃ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖
      ≤ ‖lambdaFun z - lambdaFun (ModularGroup.S • τ)‖ :=
    hb₃ z (ModularGroup.S • τ) hzρ₃ hSτ
  have hlSz : lambdaFun τ + lambdaFun z - 1 = lambdaFun z - lambdaFun (ModularGroup.S • τ) := by
    rw [LogLambda.lambdaFun_S]
    have h := Rigidity.lambdaFun_add_lambdaSFun τ
    linear_combination h
  have hJ' : c₄ * ‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖
      ≤ ‖jInvariantFun τ - jInvariantFun z‖ := hb₄ τ z hτρ₄ hzρ₄
  calc c₄ * c₃ ^ 2 * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖
      = c₄ * (c₃ * ‖(z : ℂ) - (τ : ℂ)‖) *
          (c₃ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖) := by ring
    _ ≤ c₄ * ‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlam1 hc₄.le) (by rw [hlSz]; exact hlS)
          (by positivity) (by positivity)
    _ ≤ ‖jInvariantFun τ - jInvariantFun z‖ := hJ'

/-! ## The local Euclidean bound for `Kfun` near `i` -/

/-- **The kernel `Kfun` is bounded on a Euclidean neighbourhood of `(i,i)`.**  Off the coincidence
set the cleared kernel vanishes quadratically (`two_zero_KfunClear_I`) while the growth prefactor
`Δ(τ)Δ(z)^e (j τ - j z)` dominates the same product (`j_lower_I` and `exists_DeltaFun_lower`); on
the coincidence set the value is controlled by
`Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence`. -/
theorem key_bound_I (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ τ z : ℍ,
      ‖(τ : ℂ) - Complex.I‖ < ρ → ‖(z : ℂ) - Complex.I‖ < ρ →
      ‖Kfun ℓ d τ z‖ ≤ C := by
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hb₁⟩ := two_zero_KfunClear_I ℓ d hd
  obtain ⟨ρ₂, c₂, hρ₂, hc₂, hb₂⟩ := j_lower_I
  obtain ⟨ρ₃, δ, hρ₃, hδ, hb₃⟩ := exists_DeltaFun_lower UpperHalfPlane.I
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_bound_Kfun_of_coincidence ℓ d hd
    (isCompact_closedBall UpperHalfPlane.I 1) (isCompact_closedBall UpperHalfPlane.I 1)
  set e : ℕ := (if d = 8 then 1 else 2) with he
  set ρ : ℝ := min (min ρ₁ ρ₂) (min ρ₃ (1 / 2)) with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ (by norm_num))
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρ₂ : ρ ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρρ₃ : ρ ≤ ρ₃ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ12 : ρ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, max C₀ (C₁ / (δ ^ (1 + e) * c₂)), hρpos, le_trans hC₀pos.le (le_max_left _ _),
    fun τ z hτ hz => ?_⟩
  by_cases hJ : jInvariantFun τ = jInvariantFun z
  · have hτ1 : dist τ UpperHalfPlane.I ≤ 1 :=
      dist_le_one_of_norm_lt (c := UpperHalfPlane.I) (ρ := 1 / 2)
        (by rw [UpperHalfPlane.I_im]) (lt_of_lt_of_le hτ hρ12)
    have hz1 : dist z UpperHalfPlane.I ≤ 1 :=
      dist_le_one_of_norm_lt (c := UpperHalfPlane.I) (ρ := 1 / 2)
        (by rw [UpperHalfPlane.I_im]) (lt_of_lt_of_le hz hρ12)
    exact le_trans (hC₀ τ z hτ1 hz1 hJ) (le_max_left _ _)
  · have hτ₁ : ‖(τ : ℂ) - Complex.I‖ < ρ₁ := lt_of_lt_of_le hτ hρρ₁
    have hz₁ : ‖(z : ℂ) - Complex.I‖ < ρ₁ := lt_of_lt_of_le hz hρρ₁
    have hτ₂ : ‖(τ : ℂ) - Complex.I‖ < ρ₂ := lt_of_lt_of_le hτ hρρ₂
    have hz₂ : ‖(z : ℂ) - Complex.I‖ < ρ₂ := lt_of_lt_of_le hz hρρ₂
    have hτ₃ : ‖(τ : ℂ) - Complex.I‖ < ρ₃ := lt_of_lt_of_le hτ hρρ₃
    have hz₃ : ‖(z : ℂ) - Complex.I‖ < ρ₃ := lt_of_lt_of_le hz hρρ₃
    have hΔτ : δ ≤ ‖DeltaFun τ‖ := hb₃ τ hτ₃
    have hΔz : δ ≤ ‖DeltaFun z‖ := hb₃ z hz₃
    have h2z := hb₁ τ z hτ₁ hz₁
    have hJlow := hb₂ τ z hτ₂ hz₂
    have hτz : (0 : ℝ) < ‖(z : ℂ) - (τ : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h
      exact hJ (by rw [show z = τ from UpperHalfPlane.ext (sub_eq_zero.mp h)])
    have hzSτ : (0 : ℝ) < ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h
      refine hJ ?_
      rw [show z = ModularGroup.S • τ from UpperHalfPlane.ext (sub_eq_zero.mp h),
        KernelFacts.jInvariantFun_S_smul]
    have hKc : ‖KfunClear ℓ d τ z‖ ≤
        C₁ * (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖) := by
      simpa only [mul_assoc] using h2z
    have hJlow' : c₂ * (‖(z : ℂ) - (τ : ℂ)‖ *
        ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖) ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
      simpa only [mul_assoc] using hJlow
    have hlow : δ ^ (1 + e) * ‖jInvariantFun τ - jInvariantFun z‖ ≤ ‖growthPrefactor d τ z‖ := by
      rw [norm_growthPrefactor, ← he]
      have hBe : δ ^ e ≤ ‖DeltaFun z‖ ^ e := pow_le_pow_left₀ hδ.le hΔz e
      have h3 : δ * δ ^ e ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e :=
        mul_le_mul hΔτ hBe (pow_nonneg hδ.le e) (norm_nonneg _)
      have h4 : δ * δ ^ e * ‖jInvariantFun τ - jInvariantFun z‖
          ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e * ‖jInvariantFun τ - jInvariantFun z‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      calc δ ^ (1 + e) * ‖jInvariantFun τ - jInvariantFun z‖
          = δ * δ ^ e * ‖jInvariantFun τ - jInvariantFun z‖ := by rw [pow_add, pow_one]
        _ ≤ _ := h4
    have hden : δ ^ (1 + e) * (c₂ * (‖(z : ℂ) - (τ : ℂ)‖ *
          ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖)) ≤ ‖growthPrefactor d τ z‖ := by
      calc δ ^ (1 + e) * (c₂ * (‖(z : ℂ) - (τ : ℂ)‖ *
            ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖))
          ≤ δ ^ (1 + e) * ‖jInvariantFun τ - jInvariantFun z‖ :=
            mul_le_mul_of_nonneg_left hJlow' (by positivity)
        _ ≤ ‖growthPrefactor d τ z‖ := hlow
    have hgp_pos : 0 < ‖growthPrefactor d τ z‖ :=
      lt_of_lt_of_le (mul_pos (show (0 : ℝ) < δ ^ (1 + e) by positivity)
        (mul_pos hc₂ (mul_pos hτz hzSτ))) hden
    have hone : C₁ / (δ ^ (1 + e) * c₂) * (δ ^ (1 + e) * (c₂ *
          (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖)))
        = C₁ * (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖) := by
      field_simp
    have hCmem : C₁ * (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖) ≤
        (C₁ / (δ ^ (1 + e) * c₂)) * ‖growthPrefactor d τ z‖ := by
      calc C₁ * (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖)
          = C₁ / (δ ^ (1 + e) * c₂) * (δ ^ (1 + e) * (c₂ *
              (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖))) :=
            hone.symm
        _ ≤ (C₁ / (δ ^ (1 + e) * c₂)) * ‖growthPrefactor d τ z‖ :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    have hKfun_eq : ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖ := by
      have h1 := ClearLink.KPlusClear_eq_smul d hd τ z hJ
      have h2 := ClearLink.KMinusClear_eq_smul ℓ d hd τ z hJ
      have hgp : growthPrefactor d τ z ≠ 0 := by
        simp only [growthPrefactor]
        exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
          (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _))) (sub_ne_zero.mpr hJ)
      have heq : Kfun ℓ d τ z = KfunClear ℓ d τ z / growthPrefactor d τ z := by
        rw [Kfun, KfunClear, h1, h2]
        field_simp
      rw [heq, norm_div]
    calc ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖ := hKfun_eq
      _ ≤ C₁ / (δ ^ (1 + e) * c₂) := by
          rw [div_le_iff₀ hgp_pos]
          linarith [hKc, hCmem]
      _ ≤ max C₀ (C₁ / (δ ^ (1 + e) * c₂)) := le_max_right _ _

/-! ## The lower bound on the difference quotient of `j` at any non-elliptic contour point

`exists_diffQuotient_lower` proves the local lower bound for `j` near the contour point `i t₀`
under the extra hypotheses `ε ≤ t₀ ≤ 1`.  Neither bound is used by its proof: the only point of
the positive imaginary axis at which `j'` vanishes is `i` itself (equivalently the only point at
which `E₆` vanishes), because the `SL(2,ℤ)`-orbits of the elliptic points `i` and `ρ` meet the
positive imaginary axis in at most finitely many points.  This file records the general form,
which requires only `0 < t₀` and `t₀ ≠ 1`. -/

/-- The dictionary between the honest complex derivative of the lift `f ∘ ofComplex` and the
normalized derivative `D f = (2πi)⁻¹ d/dτ`; this holds for every `f`. -/
private lemma deriv_comp_ofComplex_eq (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * Derivative.normalizedDerivOfComplex f z := by
  rw [Derivative.normalizedDerivOfComplex, mul_inv_cancel_left₀]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-! ### Positivity of `θ₀₀⁴`, `θ₁₀⁴`, `θ₀₁⁴` on the imaginary axis -/

private lemma UFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ u : ℝ, 0 < u ∧ UFun (imagAxis t ht) = ↑u := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta_imag_pos t ht
  refine ⟨r ^ 4, pow_pos hr 4, ?_⟩
  simp only [UFun, theta00Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  push_cast
  ring

private lemma WFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ w : ℝ, 0 < w ∧ WFun (imagAxis t ht) = ↑w := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta₂_one_half_imag_pos t ht
  refine ⟨r ^ 4, pow_pos hr 4, ?_⟩
  simp only [WFun, theta01Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  push_cast
  ring

private lemma VFun_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ v : ℝ, 0 < v ∧ VFun (imagAxis t ht) = ↑v := by
  obtain ⟨r, hr, hr'⟩ := Work.Analysis.ThetaReal.jacobiTheta₂_half_arg_imag_pos t ht
  refine ⟨Real.exp (-(Real.pi * t / 4)) ^ 4 * r ^ 4, by positivity, ?_⟩
  simp only [VFun, theta10Fun]
  rw [show ((imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hr']
  have hexp : Real.pi * Complex.I * ((t : ℂ) * Complex.I) / 4 = ↑(-(Real.pi * t / 4)) := by
    push_cast
    rw [show (Real.pi : ℂ) * Complex.I * (↑t * Complex.I) / 4
        = (Real.pi : ℂ) * ↑t * (Complex.I * Complex.I) / 4 by ring]
    rw [Complex.I_mul_I]
    ring
  rw [hexp, ← Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
    mul_pow]

/-- `E₄` does not vanish on the positive imaginary axis: on it `E₄ = (U² + V² + W²)/2` with
`U, V, W` positive real numbers. -/
private lemma E4Fun_imagAxis_ne_zero (t : ℝ) (ht : 0 < t) :
    E4Fun (imagAxis t ht) ≠ 0 := by
  obtain ⟨u, hu, hU⟩ := UFun_imagAxis_pos t ht
  obtain ⟨v, hv, hV⟩ := VFun_imagAxis_pos t ht
  obtain ⟨w, hw, hW⟩ := WFun_imagAxis_pos t ht
  rw [Work.Residues.KMinusClearTS.E4Fun_eq_theta, hU, hV, hW]
  have hval : ((↑u : ℂ) ^ 2 + (↑v : ℂ) ^ 2 + (↑w : ℂ) ^ 2) / 2
      = ((u ^ 2 + v ^ 2 + w ^ 2) / 2 : ℝ) := by push_cast; ring
  rw [hval]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))

/-! ### `E₆(i) = 0` and `E₆ = 0 ⟹ j = 1728` -/

/-- `S` fixes the point `i` of `ℍ`. -/
private lemma S_smul_I_aux : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
  rw [inv_neg, Complex.inv_I]
  ring

/-- `E₆(i) = 0`: the weight-`6` form `E₆` transforms by `z^6` under `S`, and `S` fixes `i`,
so `E₆(i) = i^6 E₆(i) = -E₆(i)`. -/
private lemma E6Fun_I_eq_zero : E6Fun UpperHalfPlane.I = 0 := by
  have h := Work.Residues.E6Fun_S_smul UpperHalfPlane.I
  rw [S_smul_I_aux] at h
  have hI6 : (UpperHalfPlane.I : ℂ) ^ 6 = -1 := by
    rw [UpperHalfPlane.coe_I, show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  rw [hI6, neg_one_mul] at h
  have h2 : (2 : ℂ) * E6Fun UpperHalfPlane.I = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- If `E₆` vanishes at `z` then `j(z) = 1728`: from `Δ·j = E₄³` and `1728Δ = E₄³ - E₆²`. -/
private lemma jInvariantFun_eq_1728_of_E6Fun_eq_zero {z : UpperHalfPlane} (h : E6Fun z = 0) :
    jInvariantFun z = 1728 := by
  have h1 : DeltaFun z * jInvariantFun z = E4Fun z ^ 3 :=
    ClassicalFacts.DeltaFun_mul_jInvariantFun z
  have h2 : (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2 :=
    Work.Residues.KMinusClearTS.disc_eq z
  have h3 : E4Fun z ^ 3 = 1728 * DeltaFun z := by rw [h2, h]; ring
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [h3] at h1
  exact mul_left_cancel₀ hD (by rw [h1]; ring)

/-- **The difference quotient of `j` is bounded below near the diagonal at every non-elliptic
point of the positive imaginary axis.**  For `z₀ = i t₀` with `t₀ > 0`, `t₀ ≠ 1`, the point `z₀`
is not an elliptic point of `SL(2,ℤ)`, so `j'` does not vanish there and `‖j τ - j z‖` dominates
`‖τ - z‖` in a neighbourhood of the diagonal. -/
theorem exists_diffQuotient_lower_general {t₀ : ℝ} (ht₀ : 0 < t₀) (hne : t₀ ≠ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧ ∀ τ z : UpperHalfPlane,
      ‖(τ : ℂ) - ((Work.Kernels.imagAxis t₀ ht₀) : ℂ)‖ < ρ →
      ‖(z : ℂ) - ((Work.Kernels.imagAxis t₀ ht₀) : ℂ)‖ < ρ →
      c * ‖(τ : ℂ) - (z : ℂ)‖ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
  have ht0 : 0 < t₀ := ht₀
  set z₀ : UpperHalfPlane := Work.Kernels.imagAxis t₀ ht0 with hz₀
  -- non-vanishing of `E₄` and `E₆` at `z₀ = i t₀`
  have hE4 : E4Fun z₀ ≠ 0 := E4Fun_imagAxis_ne_zero t₀ ht0
  have hE6 : E6Fun z₀ ≠ 0 := by
    intro hE6zero
    have hjz : jInvariantFun z₀ = 1728 := jInvariantFun_eq_1728_of_E6Fun_eq_zero hE6zero
    have hjI : jInvariantFun UpperHalfPlane.I = 1728 :=
      jInvariantFun_eq_1728_of_E6Fun_eq_zero E6Fun_I_eq_zero
    have heq : jInvariantFun z₀ = jInvariantFun UpperHalfPlane.I := by rw [hjz, hjI]
    obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq heq
    have hI : UpperHalfPlane.I = Work.Kernels.imagAxis 1 (by norm_num : (0 : ℝ) < 1) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_I, imagAxis, UpperHalfPlane.coe_mk]
      norm_num
    have hγ' : γ • Work.Kernels.imagAxis 1 (by norm_num : (0 : ℝ) < 1)
        = Work.Kernels.imagAxis t₀ ht0 := by
      rw [← hI, ← hz₀]
      exact hγ
    have key : Work.Kernels.imagAxis 1 (by norm_num : (0 : ℝ) < 1)
        = Work.Kernels.imagAxis t₀ ht0 := by
      rcases eq_one_or_neg_one_or_S_of_smul_imagAxis (by norm_num : (0 : ℝ) < 1) ht0 hγ' with
        h1 | h1 | h1 | h1
      · rw [h1, one_smul] at hγ'; exact hγ'
      · rw [h1, ModularGroup.SL_neg_smul, one_smul] at hγ'; exact hγ'
      · rw [h1, ← hI, S_smul_I_aux, hI] at hγ'; exact hγ'
      · rw [h1, ModularGroup.SL_neg_smul, ← hI, S_smul_I_aux, hI] at hγ'; exact hγ'
    have h2 := congrArg UpperHalfPlane.im key
    have h3 : (1 : ℝ) = t₀ := by simpa [imagAxis] using h2
    exact hne h3.symm
  -- the strict derivative of the lift of `j`
  have hMD : MDiff Work.Kernels.jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant)
      (fun z => ClassicalFacts.DeltaFun_ne_zero z)
  have hAnaOn : AnalyticOnNhd ℂ
      (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hMD).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hAna : AnalyticAt ℂ (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (z₀ : ℂ) :=
    hAnaOn (z₀ : ℂ) (by simpa using z₀.im_pos)
  have hderiv_ne :
      deriv (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) (z₀ : ℂ) ≠ 0 := by
    rw [deriv_comp_ofComplex_eq, Work.Residues.normalizedDeriv_jInvariantFun]
    refine mul_ne_zero ?_ ?_
    · exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    · simp only
      exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hE4) hE6))
        (ClassicalFacts.DeltaFun_ne_zero z₀)
  obtain ⟨ρ, hρ, c, hc, h⟩ :=
    exists_lipschitz_lower_bound_of_hasStrictDerivAt hAna.hasStrictDerivAt hderiv_ne
  refine ⟨ρ, hρ, c, hc, fun τ z hτ hz => ?_⟩
  have h1 := h (τ : ℂ) (z : ℂ) hτ hz
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h1
end MiddleRange


/-! ## The contour point `i t`

Everything is phrased with the total function `zc t = ofComplex (I * t)`, which for `t > 0` is the
point `i t = imagAxis t _` of the upper half plane. -/

/-- The contour point `i t`, as a total function of `t`. -/
def zc (t : ℝ) : ℍ := UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))

lemma continuousOn_zc : ContinuousOn zc (Set.Ioi (0 : ℝ)) := by
  unfold zc
  exact UpperHalfPlane.continuousOn_ofComplex_I_mul

lemma zc_coe {t : ℝ} (h : 0 < t) : ((zc t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
  have hz : 0 < (Complex.I * (t : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add]
    exact h
  have h1 : ((zc t : ℍ) : ℂ) = Complex.I * (t : ℂ) := by
    rw [zc, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rw [h1, mul_comm]

lemma zc_re {t : ℝ} (h : 0 < t) : ((zc t : ℍ) : ℂ).re = 0 := by
  rw [zc_coe h]
  simp [Complex.mul_re]

lemma zc_im {t : ℝ} (h : 0 < t) : (zc t).im = t := by
  rw [← UpperHalfPlane.coe_im, zc_coe h]
  simp [Complex.mul_im]

lemma zc_eq_imagAxis {t : ℝ} (h : 0 < t) : zc t = imagAxis t h := by
  apply UpperHalfPlane.ext
  show ((zc t : ℍ) : ℂ) = ((imagAxis t h : ℍ) : ℂ)
  rw [zc_coe h]
  rfl

lemma zc_one : zc 1 = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [zc_coe one_pos, UpperHalfPlane.coe_I]
  norm_num

lemma norm_zc_sub {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    ‖((zc t : ℍ) : ℂ) - ((zc s : ℍ) : ℂ)‖ = |t - s| := by
  rw [zc_coe ht, zc_coe hs]
  have h : (t : ℂ) * Complex.I - (s : ℂ) * Complex.I = ((t - s : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma norm_zc_sub_I {t : ℝ} (h : 0 < t) :
    ‖((zc t : ℍ) : ℂ) - Complex.I‖ = |t - 1| := by
  have h1 : ((zc 1 : ℍ) : ℂ) = Complex.I := by rw [zc_one, UpperHalfPlane.coe_I]
  rw [← h1, norm_zc_sub h one_pos]

lemma norm_zc {t : ℝ} (h : 0 < t) : ‖((zc t : ℍ) : ℂ)‖ = t := by
  rw [zc_coe h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h]

lemma S_smul_I : ModularGroup.S • (UpperHalfPlane.I : ℍ) = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I, inv_neg,
    Complex.inv_I]
  ring

lemma S_smul_S_smul (z : ℍ) : ModularGroup.S • (ModularGroup.S • z) = z := by
  have hSS : ModularGroup.S * ModularGroup.S = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    decide
  rw [← mul_smul, hSS, ModularGroup.SL_neg_smul, one_smul]

lemma S_smul_zc {t : ℝ} (h : 0 < t) : ModularGroup.S • zc t = zc (1 / t) := by
  have hz0 : 0 < 1 / t := by positivity
  apply UpperHalfPlane.ext
  show ((ModularGroup.S • zc t : ℍ) : ℂ) = ((zc (1 / t) : ℍ) : ℂ)
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, zc_coe h, zc_coe hz0]
  rw [show (1 / t : ℝ) = t⁻¹ by rw [one_div]]
  push_cast
  rw [inv_neg, mul_inv, Complex.inv_I]
  ring

lemma Kaxis_eq_zc (K : ℍ → ℍ → ℂ) (τ : ℍ) {t : ℝ} (h : 0 < t) :
    Kaxis K τ t = K τ (zc t) := by
  rw [Kaxis, dif_pos h, zc_eq_imagAxis h]

lemma norm_S_zc_sub_le {t t₀ : ℝ} (ht : 0 < t) (ht₀ : 0 < t₀) (h : |t - t₀| ≤ t₀ / 2) :
    ‖((ModularGroup.S • zc t : ℍ) : ℂ) - ((ModularGroup.S • zc t₀ : ℍ) : ℂ)‖
      ≤ 2 * |t - t₀| / t₀ ^ 2 := by
  have hz1 : (0 : ℝ) < 1 / t := by positivity
  have hz2 : (0 : ℝ) < 1 / t₀ := by positivity
  rw [S_smul_zc ht, S_smul_zc ht₀, norm_zc_sub hz1 hz2]
  have hdiv : (1 / t - 1 / t₀) = (t₀ - t) / (t * t₀) := by field_simp
  rw [hdiv]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t * t₀), abs_sub_comm]
  have ht2 : t₀ / 2 ≤ t := by
    have := neg_abs_le (t - t₀)
    linarith
  have hden : t₀ ^ 2 / 2 ≤ t * t₀ := by nlinarith
  calc |t - t₀| / (t * t₀) ≤ |t - t₀| / (t₀ ^ 2 / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden
    _ = 2 * |t - t₀| / t₀ ^ 2 := by field_simp

/-! ## The contour segment `{i t | 1 ≤ t ≤ T}` and the parameter space `K × [1,T]` -/

/-- The contour segment `{i t : 1 ≤ t ≤ T}`. -/
def Cseg (T : ℝ) : Set ℍ := zc '' Set.Icc (1 : ℝ) T

lemma mem_Cseg {T : ℝ} {z : ℍ} : z ∈ Cseg T ↔ ∃ t ∈ Set.Icc (1 : ℝ) T, zc t = z := Iff.rfl

lemma isCompact_Cseg (T : ℝ) : IsCompact (Cseg T) :=
  isCompact_Icc.image_of_continuousOn
    (continuousOn_zc.mono (fun t ht => lt_of_lt_of_le zero_lt_one ht.1))

/-- The parameter space: `K × [1,T]`. -/
def PKT (K : Set ℍ) (T : ℝ) : Set (ℍ × ℝ) := {q | q.1 ∈ K ∧ 1 ≤ q.2 ∧ q.2 ≤ T}

lemma mem_PKT {K : Set ℍ} {T : ℝ} {q : ℍ × ℝ} :
    q ∈ PKT K T ↔ q.1 ∈ K ∧ 1 ≤ q.2 ∧ q.2 ≤ T := Iff.rfl

lemma pos_of_mem_PKT {K : Set ℍ} {T : ℝ} {q : ℍ × ℝ} (hq : q ∈ PKT K T) : 0 < q.2 :=
  lt_of_lt_of_le zero_lt_one hq.2.1

lemma isCompact_PKT {K : Set ℍ} (hK : IsCompact K) (T : ℝ) : IsCompact (PKT K T) := by
  have h : PKT K T = K ×ˢ Set.Icc (1 : ℝ) T := by
    ext q
    simp only [PKT, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
  rw [h]
  exact hK.prod isCompact_Icc

/-! ## `Kfun` as the cleared kernel divided by the growth prefactor -/

lemma Kfun_div_prefactor (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ)
    (h : jInvariantFun τ ≠ jInvariantFun z) :
    Kfun ℓ d τ z = KfunClear ℓ d τ z / growthPrefactor d τ z := by
  have h1 := ClearLink.KPlusClear_eq_smul d hd τ z h
  have h2 := ClearLink.KMinusClear_eq_smul ℓ d hd τ z h
  have hgp : growthPrefactor d τ z ≠ 0 := by
    simp only [growthPrefactor]
    exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _))) (sub_ne_zero.mpr h)
  rw [Kfun, KfunClear, h1, h2, eq_div_iff hgp]
  ring

lemma norm_growthPrefactor (d : ℕ) (τ z : ℍ) :
    ‖growthPrefactor d τ z‖ = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2) *
      ‖jInvariantFun τ - jInvariantFun z‖ := by
  by_cases hd8 : d = 8 <;> simp [growthPrefactor, hd8, norm_mul, norm_pow]

/-! ## The bound away from the coincidences (no neighbourhood needed) -/

/-- On a compact set of parameters without coincidences `j τ = j (i t)` the kernel is bounded:
the cleared kernel is bounded there (Theorem 4.9(4)), `Δ` is bounded away from `0` on the compact
pieces of `τ` and `z`, and `j τ - j (i t)` is bounded away from `0`. -/
theorem exists_bound_of_no_coincidence (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {T : ℝ} {S : Set (ℍ × ℝ)} (hS : IsCompact S)
    (hSK : S ⊆ PKT K T)
    (hne : ∀ q ∈ S, jInvariantFun q.1 ≠ jInvariantFun (zc q.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, ‖Kfun ℓ d q.1 (zc q.2)‖ ≤ C := by
  rcases S.eq_empty_or_nonempty with rfl | hneS
  · exact ⟨0, le_refl 0, by simp⟩
  obtain ⟨R₁, hR₁, hb₁⟩ := exists_scale_bound_of_isCompact hK
  obtain ⟨R₂, hR₂, hb₂⟩ := exists_scale_bound_of_isCompact (isCompact_Cseg T)
  obtain ⟨M, hM, hMb⟩ := exists_bound_KfunClear_of_scale_bounds ℓ d hd hR₁ hR₂ hb₁ hb₂
  obtain ⟨δ₁, hδ₁, hbδ₁⟩ := exists_lower_DeltaFun hK
  obtain ⟨δ₂, hδ₂, hbδ₂⟩ := exists_lower_DeltaFun (isCompact_Cseg T)
  have hcont : ContinuousOn
      (fun q : ℍ × ℝ => jInvariantFun q.1 - jInvariantFun (zc q.2)) S :=
    (MiddleRange.continuous_jInvariantFun.continuousOn (s := Set.univ)).comp
        continuous_fst.continuousOn (fun q _ => Set.mem_univ _) |>.sub
      ((MiddleRange.continuous_jInvariantFun.continuousOn (s := Set.univ)).comp
        (continuousOn_zc.comp continuous_snd.continuousOn
          (fun q hq => pos_of_mem_PKT (hSK hq)))
        (fun q _ => Set.mem_univ _))
  obtain ⟨q₀, hq₀S, hmin⟩ := hS.exists_isMinOn hneS hcont.norm
  set δJ : ℝ := ‖jInvariantFun q₀.1 - jInvariantFun (zc q₀.2)‖ with hδJ
  have hδJpos : 0 < δJ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne q₀ hq₀S))
  set e : ℕ := (if d = 8 then 1 else 2) with he
  refine ⟨M / (δ₁ * δ₂ ^ e * δJ), by positivity, fun q hq => ?_⟩
  have hJ : δJ ≤ ‖jInvariantFun q.1 - jInvariantFun (zc q.2)‖ := (isMinOn_iff.mp hmin) q hq
  have hne' := hne q hq
  have hCseg : zc q.2 ∈ Cseg T :=
    mem_Cseg.mpr ⟨q.2, ⟨(hSK hq).2.1, (hSK hq).2.2⟩, rfl⟩
  have hnum : ‖KfunClear ℓ d q.1 (zc q.2)‖ ≤ M := hMb q.1 (hSK hq).1 (zc q.2) hCseg
  have hden : δ₁ * δ₂ ^ e * δJ ≤ ‖growthPrefactor d q.1 (zc q.2)‖ := by
    rw [norm_growthPrefactor]
    have h2 : δ₂ ^ e ≤ ‖DeltaFun (zc q.2)‖ ^ e :=
      pow_le_pow_left₀ hδ₂.le (hbδ₂ (zc q.2) hCseg) e
    have h3 : δ₁ * δ₂ ^ e ≤ ‖DeltaFun q.1‖ * ‖DeltaFun (zc q.2)‖ ^ e :=
      mul_le_mul (hbδ₁ q.1 (hSK hq).1) h2 (by positivity) (norm_nonneg _)
    exact mul_le_mul h3 hJ (by positivity) (by positivity)
  rw [Kfun_div_prefactor ℓ d hd q.1 (zc q.2) hne', norm_div]
  have hpos : 0 < δ₁ * δ₂ ^ e * δJ := by positivity
  exact le_trans (div_le_div_of_nonneg_right hnum (norm_nonneg _))
    (div_le_div_of_nonneg_left hM.le hpos hden)

/-! ## Local bounds at a coincidence -/

/-- **The coincidence `τ₀ = i`.**  Here the two branches `z = τ` and `z = S τ` merge; the
middle-range development (`MiddleRange.key_bound_I`) bounds `Kfun` on a Euclidean neighbourhood
of `(i,i)`. -/
theorem local_bound_at_I (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ),
      ‖(τ : ℂ) - Complex.I‖ < ρ → |t - 1| < ρ →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨ρ, C, hρ, hC, hkey⟩ := MiddleRange.key_bound_I ℓ d hd
  refine ⟨ρ, C, hρ, hC, fun τ t hτ ht => ?_⟩
  by_cases ht0 : 0 < t
  · rw [Kaxis_eq_zc _ τ ht0]
    exact hkey τ (zc t) hτ (by rw [norm_zc_sub_I ht0]; exact ht)
  · rw [Kaxis, dif_neg ht0, norm_zero]
    exact hC

/-- **A coincidence on the diagonal branch** `τ₀ = i t₀` (`t₀ ≠ 1`).  The cleared kernel vanishes
at least linearly in `τ - z` (`KbcAux.one_zero_diag_at`) and `j τ - j z` dominates `‖τ - z‖`
(`exists_diffQuotient_lower_general`), so the quotient `KfunClear / growthPrefactor` is bounded. -/
theorem local_bound_diag (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {T : ℝ} {τ₀ : ℍ} {t₀ : ℝ} (ht₀1 : 1 ≤ t₀)
    (hτ₀ : τ₀ = zc t₀) (hnz : t₀ ≠ 1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ),
      τ ∈ K → 1 ≤ t → t ≤ T → ‖(τ : ℂ) - (τ₀ : ℂ)‖ < ρ → |t - t₀| < ρ →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  have ht₀0 : 0 < t₀ := lt_of_lt_of_le zero_lt_one ht₀1
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hb₁⟩ := KbcAux.one_zero_diag_at ℓ d hd τ₀
  obtain ⟨ρ₂, hρ₂, c, hc, hb₂⟩ := MiddleRange.exists_diffQuotient_lower_general ht₀0 hnz
  have hbase : imagAxis t₀ ht₀0 = τ₀ := by rw [← zc_eq_imagAxis ht₀0, hτ₀]
  obtain ⟨δ₁, hδ₁, hbδ₁⟩ := exists_lower_DeltaFun hK
  obtain ⟨δ₂, hδ₂, hbδ₂⟩ := exists_lower_DeltaFun (isCompact_Cseg T)
  obtain ⟨C₀, hC₀, hb₀⟩ := MiddleRange.exists_bound_Kfun_of_coincidence ℓ d hd hK
    (isCompact_Cseg T)
  set e : ℕ := (if d = 8 then 1 else 2) with he
  set ρ : ℝ := min (min ρ₁ ρ₂) 1 / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    have h : 0 < min (min ρ₁ ρ₂) 1 := lt_min (lt_min hρ₁ hρ₂) one_pos
    linarith
  have hρ₁' : ρ ≤ ρ₁ := by
    rw [hρdef]
    have h1 := min_le_left (min ρ₁ ρ₂) 1
    have h2 := min_le_left ρ₁ ρ₂
    linarith
  have hρ₂' : ρ ≤ ρ₂ := by
    rw [hρdef]
    have h1 := min_le_left (min ρ₁ ρ₂) 1
    have h2 := min_le_right ρ₁ ρ₂
    linarith
  refine ⟨ρ, max C₀ (C₁ / (δ₁ * δ₂ ^ e * c)) + 1, hρpos, by positivity, ?_⟩
  intro τ t hτK ht1 htT hτ hdt
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rw [Kaxis_eq_zc _ τ ht0]
  have hzt : ‖((zc t : ℍ) : ℂ) - (τ₀ : ℂ)‖ = |t - t₀| := by
    rw [hτ₀, norm_zc_sub ht0 ht₀0]
  have hz₁ : ‖((zc t : ℍ) : ℂ) - (τ₀ : ℂ)‖ < ρ₁ := by
    rw [hzt]; exact lt_of_lt_of_le hdt hρ₁'
  have hz₂ : ‖((zc t : ℍ) : ℂ) - (τ₀ : ℂ)‖ < ρ₂ := by
    rw [hzt]; exact lt_of_lt_of_le hdt hρ₂'
  have hzf : zc t ∈ Cseg T := mem_Cseg.mpr ⟨t, ⟨ht1, htT⟩, rfl⟩
  by_cases hcoin : jInvariantFun τ = jInvariantFun (zc t)
  · refine le_trans (hb₀ τ (zc t) hτK hzf hcoin) ?_
    linarith [le_max_left C₀ (C₁ / (δ₁ * δ₂ ^ e * c))]
  · have hne : τ ≠ zc t := fun hh => hcoin (by rw [hh])
    have hnorm : (0 : ℝ) < ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro hh
      exact hne (UpperHalfPlane.ext (sub_eq_zero.mp hh))
    have hj : c * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖ ≤
        ‖jInvariantFun τ - jInvariantFun (zc t)‖ :=
      hb₂ τ (zc t) (by rw [hbase]; exact lt_of_lt_of_le hτ hρ₂') (by rw [hbase]; exact hz₂)
    have hnum : ‖KfunClear ℓ d τ (zc t)‖ ≤ C₁ * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖ :=
      hb₁ τ (zc t) (lt_of_lt_of_le hτ hρ₁') hz₁
    have hden : δ₁ * δ₂ ^ e * c * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖ ≤
        ‖growthPrefactor d τ (zc t)‖ := by
      rw [norm_growthPrefactor]
      have h2 : δ₂ ^ e ≤ ‖DeltaFun (zc t)‖ ^ e :=
        pow_le_pow_left₀ hδ₂.le (hbδ₂ (zc t) hzf) e
      have h3 : δ₁ * δ₂ ^ e * c ≤ ‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e * c := by
        refine mul_le_mul_of_nonneg_right ?_ hc.le
        exact mul_le_mul (hbδ₁ τ hτK) h2 (by positivity) (norm_nonneg _)
      calc δ₁ * δ₂ ^ e * c * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖
          = (δ₁ * δ₂ ^ e * c) * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖ := by ring
        _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e * c)
              * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖ :=
            mul_le_mul_of_nonneg_right h3 hnorm.le
        _ = (‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e) * (c * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖) := by
              ring
        _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e)
              * ‖jInvariantFun τ - jInvariantFun (zc t)‖ :=
            mul_le_mul_of_nonneg_left hj (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) e))
    rw [Kfun_div_prefactor ℓ d hd τ (zc t) hcoin, norm_div]
    have hpos : 0 < δ₁ * δ₂ ^ e * c * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖ := by positivity
    calc ‖KfunClear ℓ d τ (zc t)‖ / ‖growthPrefactor d τ (zc t)‖
        ≤ (C₁ * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖) / ‖growthPrefactor d τ (zc t)‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (C₁ * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖)
            / (δ₁ * δ₂ ^ e * c * ‖(τ : ℂ) - ((zc t : ℍ) : ℂ)‖) :=
          div_le_div_of_nonneg_left (by positivity) hpos hden
      _ = C₁ / (δ₁ * δ₂ ^ e * c) := mul_div_mul_right _ _ (ne_of_gt hnorm)
      _ ≤ max C₀ (C₁ / (δ₁ * δ₂ ^ e * c)) + 1 := by
          linarith [le_max_right C₀ (C₁ / (δ₁ * δ₂ ^ e * c))]

/-- **A coincidence on the `S`-branch** `i t₀ = S τ₀` (i.e. `τ₀ = i/t₀`), `t₀ ≠ 1`.  The cleared
kernel vanishes linearly in `τ - S z` (`KbcAux.one_zero_S_at`) while `j`-differences dominate
Euclidean distances near the (non-elliptic) point `τ₀` (`exists_diffQuotient_lower_general`). -/
theorem local_bound_S (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {T : ℝ} {τ₀ : ℍ} {t₀ : ℝ} (ht₀1 : 1 ≤ t₀)
    (hτ₀ : ModularGroup.S • zc t₀ = τ₀) (hnz : t₀ ≠ 1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ),
      τ ∈ K → 1 ≤ t → t ≤ T → ‖(τ : ℂ) - (τ₀ : ℂ)‖ < ρ → |t - t₀| < ρ →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  have ht₀0 : 0 < t₀ := lt_of_lt_of_le zero_lt_one ht₀1
  have ht₀1' : (0 : ℝ) < 1 / t₀ := by positivity
  have hne' : (1 : ℝ) / t₀ ≠ 1 := by
    intro h
    have h2 : t₀ = 1 := by
      have h3 : 1 / t₀ * t₀ = 1 * t₀ := by rw [h]
      rw [div_mul_cancel₀ _ (ne_of_gt ht₀0), one_mul] at h3
      exact h3.symm
    exact hnz h2
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hb₁⟩ := KbcAux.one_zero_S_at ℓ d hd (zc t₀)
  obtain ⟨ρ₂, hρ₂, c, hc, hb₂⟩ := MiddleRange.exists_diffQuotient_lower_general ht₀1' hne'
  have hbase₂ : imagAxis (1 / t₀) ht₀1' = τ₀ := by
    rw [← zc_eq_imagAxis ht₀1', ← S_smul_zc ht₀0, hτ₀]
  obtain ⟨δ₁, hδ₁, hbδ₁⟩ := exists_lower_DeltaFun hK
  obtain ⟨δ₂, hδ₂, hbδ₂⟩ := exists_lower_DeltaFun (isCompact_Cseg T)
  obtain ⟨C₀, hC₀, hb₀⟩ := MiddleRange.exists_bound_Kfun_of_coincidence ℓ d hd hK
    (isCompact_Cseg T)
  set e : ℕ := (if d = 8 then 1 else 2) with he
  set ρ : ℝ := min (min ρ₁ (ρ₁ / 2)) (min (min ρ₂ (ρ₂ * t₀ ^ 2 / 2))
    (min (ρ₁ * t₀ ^ 2 / 4) (t₀ / 2))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    refine lt_min (lt_min hρ₁ (by linarith)) (lt_min (lt_min hρ₂ (by positivity))
      (lt_min (by positivity) (by linarith)))
  have hρρ₁ : ρ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρ₁₂ : ρ ≤ ρ₁ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρρ₂ : ρ ≤ ρ₂ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρρ₂t : ρ ≤ ρ₂ * t₀ ^ 2 / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρρ₁t : ρ ≤ ρ₁ * t₀ ^ 2 / 4 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρt : ρ ≤ t₀ / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨ρ, max C₀ (C₁ / (δ₁ * δ₂ ^ e * c)) + 1, hρpos, by positivity, ?_⟩
  intro τ t hτK ht1 htT hτ hdt
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rw [Kaxis_eq_zc _ τ ht0]
  have hzf : zc t ∈ Cseg T := mem_Cseg.mpr ⟨t, ⟨ht1, htT⟩, rfl⟩
  by_cases hcoin : jInvariantFun τ = jInvariantFun (zc t)
  · refine le_trans (hb₀ τ (zc t) hτK hzf hcoin) ?_
    linarith [le_max_left C₀ (C₁ / (δ₁ * δ₂ ^ e * c))]
  · have hne : τ ≠ zc t := fun hh => hcoin (by rw [hh])
    -- the two points `S z` and `S z₀ = τ₀` stay close
    have hSz : ‖((ModularGroup.S • zc t : ℍ) : ℂ) - (τ₀ : ℂ)‖ < ρ₂ := by
      rw [← hτ₀]
      have := norm_S_zc_sub_le ht0 ht₀0 (le_of_lt (lt_of_lt_of_le hdt hρt))
      refine lt_of_le_of_lt this ?_
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < t₀ ^ 2)]
      have h2 : 2 * |t - t₀| < 2 * ρ := by linarith
      have h3 : 2 * ρ ≤ 2 * (ρ₂ * t₀ ^ 2 / 2) := by linarith [hρρ₂t]
      linarith
    have hSz₁ : ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ < ρ₁ := by
      have h1 : ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖
          ≤ ‖(τ : ℂ) - (τ₀ : ℂ)‖ + ‖(τ₀ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ := by
        rw [show (τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)
            = ((τ : ℂ) - (τ₀ : ℂ)) + ((τ₀ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)) by ring]
        exact norm_add_le _ _
      have h2 : ‖(τ₀ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ ≤ ρ₁ / 2 := by
        rw [norm_sub_rev]
        have hthis : ‖((ModularGroup.S • zc t : ℍ) : ℂ) - (τ₀ : ℂ)‖
            ≤ 2 * |t - t₀| / t₀ ^ 2 := by
          rw [← hτ₀]
          exact norm_S_zc_sub_le ht0 ht₀0 (le_of_lt (lt_of_lt_of_le hdt hρt))
        refine le_trans hthis ?_
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < t₀ ^ 2)]
        have h3 : 2 * |t - t₀| ≤ 2 * ρ := by linarith
        have h4 : 2 * ρ ≤ ρ₁ * t₀ ^ 2 / 2 := by nlinarith [hρρ₁t]
        have h5 : ρ₁ / 2 * t₀ ^ 2 = ρ₁ * t₀ ^ 2 / 2 := by ring
        linarith
      linarith
    have hz₁ : ‖((zc t : ℍ) : ℂ) - ((zc t₀ : ℍ) : ℂ)‖ < ρ₁ := by
      rw [norm_zc_sub ht0 ht₀0]
      exact lt_of_lt_of_le hdt hρρ₁
    have hnum : ‖KfunClear ℓ d τ (zc t)‖ ≤
        C₁ * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ :=
      hb₁ τ (zc t) hz₁ hSz₁
    have hj : c * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ ≤
        ‖jInvariantFun τ - jInvariantFun (zc t)‖ := by
      have h := hb₂ τ (ModularGroup.S • zc t) (by rw [hbase₂]; exact lt_of_lt_of_le hτ hρρ₂)
        (by rw [hbase₂]; exact hSz)
      rwa [KernelFacts.jInvariantFun_S_smul] at h
    have hnorm : (0 : ℝ) < ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro hh
      refine hcoin ?_
      have h2 : τ = ModularGroup.S • zc t := UpperHalfPlane.ext (sub_eq_zero.mp hh)
      rw [h2, KernelFacts.jInvariantFun_S_smul]
    have hden : δ₁ * δ₂ ^ e * c * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ ≤
        ‖growthPrefactor d τ (zc t)‖ := by
      rw [norm_growthPrefactor]
      have h2 : δ₂ ^ e ≤ ‖DeltaFun (zc t)‖ ^ e :=
        pow_le_pow_left₀ hδ₂.le (hbδ₂ (zc t) hzf) e
      have h3 : δ₁ * δ₂ ^ e * c ≤ ‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e * c := by
        refine mul_le_mul_of_nonneg_right ?_ hc.le
        exact mul_le_mul (hbδ₁ τ hτK) h2 (by positivity) (norm_nonneg _)
      calc δ₁ * δ₂ ^ e * c * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖
          = (δ₁ * δ₂ ^ e * c) * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ := by ring
        _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e * c)
              * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ :=
            mul_le_mul_of_nonneg_right h3 hnorm.le
        _ = (‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e)
              * (c * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖) := by ring
        _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun (zc t)‖ ^ e)
              * ‖jInvariantFun τ - jInvariantFun (zc t)‖ :=
            mul_le_mul_of_nonneg_left hj (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) e))
    rw [Kfun_div_prefactor ℓ d hd τ (zc t) hcoin, norm_div]
    have hpos : (0 : ℝ) < δ₁ * δ₂ ^ e * c
        * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖ := by positivity
    calc ‖KfunClear ℓ d τ (zc t)‖ / ‖growthPrefactor d τ (zc t)‖
        ≤ (C₁ * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖)
            / ‖growthPrefactor d τ (zc t)‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (C₁ * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖)
            / (δ₁ * δ₂ ^ e * c * ‖(τ : ℂ) - ((ModularGroup.S • zc t : ℍ) : ℂ)‖) :=
          div_le_div_of_nonneg_left (by positivity) hpos hden
      _ = C₁ / (δ₁ * δ₂ ^ e * c) := mul_div_mul_right _ _ (ne_of_gt hnorm)
      _ ≤ max C₀ (C₁ / (δ₁ * δ₂ ^ e * c)) + 1 := by
          linarith [le_max_right C₀ (C₁ / (δ₁ * δ₂ ^ e * c))]

/-! ## The kernel is bounded on `K × [1,T]` -/

theorem exists_bound_Kaxis_low (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) (hsub : K ⊆ DomainD) {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ), τ ∈ K → 1 ≤ t → t ≤ T →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  have hPKT : IsCompact (PKT K T) := isCompact_PKT hK T
  have hloc : ∀ q : PKT K T, ∃ V : Set (ℍ × ℝ), IsOpen V ∧ (q : ℍ × ℝ) ∈ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q' ∈ PKT K T, q' ∈ V → ‖Kaxis (Kfun ℓ d) q'.1 q'.2‖ ≤ C := by
    intro q
    set τ₀ : ℍ := (q : ℍ × ℝ).1 with hτ₀def
    set t₀ : ℝ := (q : ℍ × ℝ).2 with ht₀def
    have hτ₀K : τ₀ ∈ K := q.2.1
    have ht₀1 : 1 ≤ t₀ := q.2.2.1
    have ht₀T : t₀ ≤ T := q.2.2.2
    have ht₀0 : 0 < t₀ := pos_of_mem_PKT q.2
    by_cases hcoin : jInvariantFun τ₀ = jInvariantFun (zc t₀)
    · have hcases := eq_or_eq_S_of_re_eq_zero (hsub hτ₀K) (zc_re ht₀0) hcoin
      by_cases hI : τ₀ = UpperHalfPlane.I
      · -- the elliptic point `i`
        have ht₀eq : t₀ = 1 := by
          have h : zc t₀ = UpperHalfPlane.I := by
            rcases hcases with h | h
            · rw [h, hI]
            · rw [h, hI, S_smul_I]
          have h2 := zc_im ht₀0
          rw [h] at h2
          exact h2.symm
        obtain ⟨ρ, C, hρ, hC, hb⟩ := local_bound_at_I ℓ d hd
        refine ⟨{q' : ℍ × ℝ | ‖(q'.1 : ℂ) - Complex.I‖ < ρ ∧ |q'.2 - 1| < ρ},
          ?_, ⟨?_, ?_⟩, C, hC, ?_⟩
        · refine IsOpen.inter ?_ ?_
          · exact isOpen_lt (((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
              continuous_const).norm) continuous_const
          · exact isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const
        · rw [← hτ₀def, hI, UpperHalfPlane.coe_I, sub_self, norm_zero]; exact hρ
        · rw [← ht₀def, ht₀eq, sub_self, abs_zero]; exact hρ
        · intro q' hq' hq'V
          exact hb q'.1 q'.2 hq'V.1 hq'V.2
      · rcases hcases with hD | hS
        · -- the diagonal branch `z = τ`
          have hnz : t₀ ≠ 1 := by
            intro hh
            exact hI (by rw [← hD, hh]; exact zc_one)
          obtain ⟨ρ, C, hρ, hC, hb⟩ := local_bound_diag ℓ d hd hK ht₀1 hD.symm hnz
          refine ⟨{q' : ℍ × ℝ | ‖(q'.1 : ℂ) - (τ₀ : ℂ)‖ < ρ ∧ |q'.2 - t₀| < ρ},
            ?_, ⟨?_, ?_⟩, C, hC, ?_⟩
          · refine IsOpen.inter ?_ ?_
            · exact isOpen_lt (((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
                continuous_const).norm) continuous_const
            · exact isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const
          · rw [sub_self, norm_zero]; exact hρ
          · rw [sub_self, abs_zero]; exact hρ
          · intro q' hq' hq'V
            exact hb q'.1 q'.2 hq'.1 hq'.2.1 hq'.2.2 hq'V.1 hq'V.2
        · -- the `S`-branch
          have hSτ : ModularGroup.S • zc t₀ = τ₀ := by rw [hS]; exact S_smul_S_smul τ₀
          have hnz : t₀ ≠ 1 := by
            intro hh
            apply hI
            have h2 : ModularGroup.S • τ₀ = UpperHalfPlane.I := by rw [← hS, hh, zc_one]
            have h3 : τ₀ = ModularGroup.S • (ModularGroup.S • τ₀) := (S_smul_S_smul τ₀).symm
            rw [h3, h2, S_smul_I]
          obtain ⟨ρ, C, hρ, hC, hb⟩ := local_bound_S ℓ d hd hK ht₀1 hSτ hnz
          refine ⟨{q' : ℍ × ℝ | ‖(q'.1 : ℂ) - (τ₀ : ℂ)‖ < ρ ∧ |q'.2 - t₀| < ρ},
            ?_, ⟨?_, ?_⟩, C, hC, ?_⟩
          · refine IsOpen.inter ?_ ?_
            · exact isOpen_lt (((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
                continuous_const).norm) continuous_const
            · exact isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const
          · rw [sub_self, norm_zero]; exact hρ
          · rw [sub_self, abs_zero]; exact hρ
          · intro q' hq' hq'V
            exact hb q'.1 q'.2 hq'.1 hq'.2.1 hq'.2.2 hq'V.1 hq'V.2
    · -- no coincidence at `q`: a small metric ball stays in the no-coincidence set
      have hzc2 : ContinuousAt (fun q' : ℍ × ℝ => zc q'.2) (q : ℍ × ℝ) := by
        have h1 : ContinuousAt zc ((q : ℍ × ℝ).2) :=
          continuousOn_zc.continuousAt (isOpen_Ioi.mem_nhds ht₀0)
        exact h1.comp continuous_snd.continuousAt
      have hcont : ContinuousAt (fun q' : ℍ × ℝ => jInvariantFun q'.1 - jInvariantFun (zc q'.2))
          (q : ℍ × ℝ) :=
        ContinuousAt.sub
          (ContinuousAt.comp MiddleRange.continuous_jInvariantFun.continuousAt
            continuous_fst.continuousAt)
          (ContinuousAt.comp MiddleRange.continuous_jInvariantFun.continuousAt hzc2)
      have hfq : (fun q' : ℍ × ℝ => jInvariantFun q'.1 - jInvariantFun (zc q'.2))
          (q : ℍ × ℝ) ≠ 0 := sub_ne_zero.mpr hcoin
      have hpre : (fun q' : ℍ × ℝ => jInvariantFun q'.1 - jInvariantFun (zc q'.2)) ⁻¹'
          ({0}ᶜ) ∈ 𝓝 (q : ℍ × ℝ) :=
        hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by simpa using hfq))
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
      have hS : IsCompact (PKT K T ∩ Metric.closedBall (q : ℍ × ℝ) (ε / 2)) :=
        hPKT.inter_right Metric.isClosed_closedBall
      have hneS : ∀ q' ∈ PKT K T ∩ Metric.closedBall (q : ℍ × ℝ) (ε / 2),
          jInvariantFun q'.1 ≠ jInvariantFun (zc q'.2) := by
        intro q' hq'
        have hd : dist q' (q : ℍ × ℝ) < ε := lt_of_le_of_lt hq'.2 (by linarith)
        have hmem : (fun q'' : ℍ × ℝ => jInvariantFun q''.1 - jInvariantFun (zc q''.2)) q'
            ∈ ({0}ᶜ : Set ℂ) := hball hd
        exact sub_ne_zero.mp (by simpa using hmem)
      obtain ⟨C, hC, hbC⟩ := exists_bound_of_no_coincidence ℓ d hd hK hS Set.inter_subset_left hneS
      refine ⟨Metric.ball (q : ℍ × ℝ) (ε / 2), Metric.isOpen_ball,
        Metric.mem_ball_self (by linarith), C, hC, ?_⟩
      intro q' hq' hq'V
      rw [Kaxis_eq_zc _ q'.1 (pos_of_mem_PKT hq')]
      exact hbC q' ⟨hq', Metric.ball_subset_closedBall hq'V⟩
  classical
  choose V hVopen hVmem C hC hVb using hloc
  have hcover : PKT K T ⊆ ⋃ q : PKT K T, V q := fun q hq =>
    Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hVmem ⟨q, hq⟩⟩
  obtain ⟨t, ht⟩ := hPKT.elim_finite_subcover V hVopen hcover
  have hsumpos : (0 : ℝ) < ∑ q ∈ t, C q + 1 := by
    have h1 : 0 ≤ ∑ q ∈ t, C q := Finset.sum_nonneg (fun q _ => hC q)
    linarith
  refine ⟨∑ q ∈ t, C q + 1, hsumpos.le, fun τ tt hτ ht1 htT => ?_⟩
  have hq' : (τ, tt) ∈ PKT K T := ⟨hτ, ht1, htT⟩
  obtain ⟨q₀, hq₀t, hq₀mem⟩ := Set.mem_iUnion₂.mp (ht hq')
  have hb1 := hVb q₀ (τ, tt) hq' hq₀mem
  have hsum : C q₀ ≤ ∑ q ∈ t, C q :=
    Finset.single_le_sum (fun q _ => hC q) hq₀t
  linarith

/-! ## The non-decaying part `Aexp` is bounded on `K × [1,T]` -/

theorem exists_bound_Aexp (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) (hsub : K ⊆ DomainD) {T : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ), τ ∈ K → 1 ≤ t → t ≤ T →
      ‖Aexp (Gcusp ℓ d) τ t‖ ≤ C := by
  obtain ⟨R, hR, hscale⟩ := exists_scale_bound_of_isCompact hK
  have hb : ∀ i j : Fin 2, ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ K, ‖Gcusp ℓ d i j τ‖ ≤ B := by
    intro i j
    obtain ⟨α, N, hα, hN, hmod⟩ :=
      (Work.Kernels.moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d i j)).mp (GcuspInP ℓ d i j)
    refine ⟨α * R ^ N, by positivity, fun τ hτ => ?_⟩
    refine le_trans (hmod τ (hsub hτ)) ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (scale_pos τ).le (hscale τ hτ) hN) hα
  obtain ⟨B00, hB00, hb00⟩ := hb 0 0
  obtain ⟨B01, hB01, hb01⟩ := hb 0 1
  obtain ⟨B10, hB10, hb10⟩ := hb 1 0
  obtain ⟨B11, hB11, hb11⟩ := hb 1 1
  have hCnn : 0 ≤ B00 + (|T| + 1) * B01 + Real.exp (2 * Real.pi * (|T| + 1))
      * (B10 + (|T| + 1) * B11) + 1 := by
    have h1 : 0 ≤ (|T| + 1) * B01 := mul_nonneg (by positivity) hB01
    have h2 : 0 ≤ (|T| + 1) * B11 := mul_nonneg (by positivity) hB11
    have h3 : 0 ≤ Real.exp (2 * Real.pi * (|T| + 1)) := (Real.exp_pos _).le
    have h4 : 0 ≤ B10 + (|T| + 1) * B11 := by linarith
    have h5 : 0 ≤ Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) :=
      mul_nonneg h3 h4
    linarith
  refine ⟨B00 + (|T| + 1) * B01 + Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) + 1,
    hCnn, fun τ t hτ ht1 htT => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have htabs : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hI' : ‖((t : ℂ) * Complex.I)‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, htabs]
  have hexp : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
    rw [Complex.norm_exp]
    simp
  have htT' : t ≤ |T| + 1 := by
    have := le_abs_self T
    linarith
  have hexp_le : Real.exp (2 * Real.pi * t) ≤ Real.exp (2 * Real.pi * (|T| + 1)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  rw [Aexp]
  calc ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ
        + Complex.exp (2 * Real.pi * t) * (Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I)
            * Gcusp ℓ d 1 1 τ)‖
      ≤ ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖
        + ‖Complex.exp (2 * Real.pi * t) * (Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I)
            * Gcusp ℓ d 1 1 τ)‖ := norm_add_le _ _
    _ ≤ (B00 + t * B01) + Real.exp (2 * Real.pi * t) * (B10 + t * B11) := by
        refine add_le_add ?_ ?_
        · calc ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖
              ≤ ‖Gcusp ℓ d 0 0 τ‖ + ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖ :=
                norm_add_le _ _
            _ ≤ B00 + t * B01 := by
                refine add_le_add (hb00 τ hτ) ?_
                rw [norm_mul, hI']
                exact mul_le_mul_of_nonneg_left (hb01 τ hτ) ht0.le
        · rw [norm_mul, hexp]
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          calc ‖Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ‖
              ≤ ‖Gcusp ℓ d 1 0 τ‖ + ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ‖ :=
                norm_add_le _ _
            _ ≤ B10 + t * B11 := by
                refine add_le_add (hb10 τ hτ) ?_
                rw [norm_mul, hI']
                exact mul_le_mul_of_nonneg_left (hb11 τ hτ) ht0.le
    _ ≤ B00 + (|T| + 1) * B01
          + Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) := by
        have h2 : t * B01 ≤ (|T| + 1) * B01 := mul_le_mul_of_nonneg_right htT' hB01
        have h3 : t * B11 ≤ (|T| + 1) * B11 := mul_le_mul_of_nonneg_right htT' hB11
        have h5 : B10 + t * B11 ≤ B10 + (|T| + 1) * B11 := by linarith
        have h6 : Real.exp (2 * Real.pi * t) * (B10 + t * B11)
            ≤ Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) :=
          mul_le_mul hexp_le h5 (by positivity) (Real.exp_pos _).le
        linarith
    _ ≤ B00 + (|T| + 1) * B01
          + Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) + 1 :=
        le_add_of_nonneg_right zero_le_one

end SmallT

open SmallT

/-- The CKMRV kernel on the compact piece `1 ≤ t ≤ T` of the contour, minus the non-decaying
part `Aexp (Gcusp ℓ d)`, is uniformly bounded for `τ ∈ K ⊆ 𝒟`.  This is the "middle range"
estimate of the cusp expansion: for `t` below the threshold at which the expansion in
`E = e^{πiz}` converges, Kaxis is merely bounded (it is continuous on the compact set
`K × {imagAxis t | 1 ≤ t ≤ T}`, the only singularities being the removable coincidences
`j(τ) = j(it)` at `τ = it` and `τ = S·(it)`, where the *cleared* kernel vanishes by
`KClear_S_vanishing` and `KPlusClear_diag`/`KMinusClear_diag`). -/
theorem smallT_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ t : ℝ, 1 ≤ t → t ≤ T →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ C := by
  by_cases hT1 : (1 : ℝ) ≤ T
  · obtain ⟨C₁, hC₁, hb₁⟩ := SmallT.exists_bound_Kaxis_low ℓ d hd hK hsub hT1
    obtain ⟨C₂, hC₂, hb₂⟩ := SmallT.exists_bound_Aexp ℓ d hd hK hsub (T := T)
    refine ⟨C₁ + C₂ + 1, by positivity, fun τ hτ t ht1 htT => ?_⟩
    have h1 := hb₁ τ t hτ ht1 htT
    have h2 := hb₂ τ t hτ ht1 htT
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ := norm_sub_le _ _
      _ ≤ C₁ + C₂ := add_le_add h1 h2
      _ ≤ C₁ + C₂ + 1 := by linarith
  · refine ⟨1, one_pos, fun τ hτ t ht1 htT => ?_⟩
    exact absurd (show (1 : ℝ) ≤ t ∧ t ≤ T from ⟨ht1, htT⟩)
      (by intro h; have hTlt : T < 1 := not_le.mp hT1; linarith [h.1, h.2, hTlt])

end

end Work.Asymptotics.CuspExp
