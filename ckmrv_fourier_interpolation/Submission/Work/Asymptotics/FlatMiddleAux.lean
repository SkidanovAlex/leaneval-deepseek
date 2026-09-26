import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.MiddleRange.Basic
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Rigidity.LambdaAnharmonic
import Submission.Work.Kernels.KernelFacts.KPlus_S_add

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Metric Filter Complex

namespace Work.Asymptotics

open Work.Kernels

set_option maxHeartbeats 1600000

/-! ## The contour point `t ↦ i t` -/

/-- The contour point `i t`.  For `t > 0` this is the point `i t ∈ ℍ`; for `t ≤ 0` the value is
junk (but the function is total, which keeps the compactness arguments simple). -/
def cpt (t : ℝ) : ℍ := UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))

lemma cpt_coe {t : ℝ} (h : 0 < t) : ((cpt t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
  have hz : 0 < ((Complex.I * (t : ℂ))).im := by simpa using h
  show (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) : ℂ) = (t : ℂ) * Complex.I
  simp only [UpperHalfPlane.ofComplex_apply_of_im_pos hz, mul_comm]

lemma cpt_eq_of_pos {t : ℝ} (h : 0 < t) : cpt t = imagAxis t h := by
  refine UpperHalfPlane.ext ?_
  rw [cpt_coe h, imagAxis]

lemma cpt_im {t : ℝ} (h : 0 < t) : (cpt t).im = t := by
  rw [cpt_eq_of_pos h]
  simp [imagAxis]

lemma cpt_re {t : ℝ} (h : 0 < t) : ((cpt t : ℍ) : ℂ).re = 0 := by
  rw [cpt_coe h]
  simp

lemma continuousOn_cpt : ContinuousOn cpt (Set.Ioi 0) :=
  UpperHalfPlane.continuousOn_ofComplex_I_mul

lemma continuousAt_cpt {t : ℝ} (h : 0 < t) : ContinuousAt cpt t :=
  continuousOn_cpt.continuousAt (isOpen_Ioi.mem_nhds h)

/-! ## The one-zero maximum-modulus bound -/

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

lemma continuous_KfunClear_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    Continuous (fun z : ℍ => KfunClear ℓ d τ z) :=
  (mdifferentiable_KfunClear_snd ℓ d hd τ).continuous

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
  have h2 : ((w - (c : ℂ)).im) = w.im - (c : ℂ).im := by simp
  have h3 : |w.im - (c : ℂ).im| ≤ ‖w - (c : ℂ)‖ := by
    have h4 : |(w - (c : ℂ)).im| ≤ ‖w - (c : ℂ)‖ := Complex.abs_im_le_norm _
    rwa [h2] at h4
  have h5 : -(ρ) ≤ w.im - (c : ℂ).im := (abs_le.mp (le_trans h3 h1)).1
  have h6 : (c : ℂ).im - ρ ≤ w.im := by linarith
  have h7 : 0 < (c : ℂ).im - ρ := by rw [UpperHalfPlane.coe_im]; linarith
  show 0 < w.im
  linarith

/-- Bounds for `KfunClear` on a product of two closed balls inside `ℍ`. -/
lemma exists_bound_KfunClear_of_balls (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (c₁ c₂ : ℍ) {R₁ R₂ : ℝ} (hR₁ : R₁ < c₁.im) (hR₂ : R₂ < c₂.im) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ z : ℍ, ‖(τ : ℂ) - (c₁ : ℂ)‖ ≤ R₁ → ‖(z : ℂ) - (c₂ : ℂ)‖ ≤ R₂ →
      ‖KfunClear ℓ d τ z‖ ≤ M := by
  obtain ⟨s₁, hs₁, hb₁⟩ := exists_scale_bound_euclidean (c := c₁) (r := R₁) hR₁
  obtain ⟨s₂, hs₂, hb₂⟩ := exists_scale_bound_euclidean (c := c₂) (r := R₂) hR₂
  obtain ⟨M, hM, h⟩ := exists_bound_KfunClear_of_scale_bounds ℓ d hd hs₁ hs₂
    (fun τ hτ => hb₁ τ hτ) (fun z hz => hb₂ z hz)
  exact ⟨M, hM, fun τ z hτ hz => h τ hτ z hz⟩

/-! ## Continuity of the `S`-action and metric helpers -/

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

/-! ## The one-zero bound for functions on `ℍ` -/

/-- **One-zero bound on `ℍ`** (Euclidean distances).  A holomorphic function on `ℍ` vanishing at
`w₀` and bounded by `M` on the Euclidean ball of radius `r` around `c` satisfies
`‖f w‖ ≤ (2M/r)·‖w - w₀‖` on the half-ball. -/
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
    have h3 : ‖(z : ℂ) - (z₀ : ℂ)‖ < 3 * z₀.im / 4 := by linarith [z₀.im_pos]
    exact hMb _ _ h1 h3.le
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
    -- `uz` is close to `w₀`
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
      have h3 : ‖(z : ℂ) - (z₀ : ℂ)‖ < 3 * z₀.im / 4 := by linarith [z₀.im_pos, hz1]
      exact hMb _ _ h1 h3.le
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
    rw [huz] at h
    exact h

end Work.Asymptotics
