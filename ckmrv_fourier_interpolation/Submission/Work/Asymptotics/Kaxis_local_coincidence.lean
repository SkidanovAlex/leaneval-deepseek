
/-
# Local boundedness of the CKMRV kernel at an imaginary-axis coincidence

The CKMRV kernel `K^{(d)}` (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022),
Theorem 4.9) is a meromorphic function of `(τ,z)` with simple poles along the coincidence set
`j τ = j z`.  Along the imaginary axis `z = it` nothing is lost: the *value* of `K` at a
coincidence is finite, and the pole is in fact removable there.

Concretely, `Work.Kernels.growthPrefactor d τ z = Δ(τ)Δ(z)^e (j τ - j z)` clears the pole,
`Work.Kernels.KfunClear = growthPrefactor · Kfun`, and on the coincidence set near the imaginary
axis (`{τ = z} ∪ {τ = S z}`) the *cleared* kernel `KfunClear` vanishes
(`Work.Residues.KPlusClear_diag`, `Work.Asymptotics.KClear_S_vanishing`).  Hence
`Kfun = KfunClear / growthPrefactor` is bounded there, and this file makes that quantitative.

The situation splits:

* `τ₀ ≠ i`: the two coincidence branches `z = τ` and `z = S τ` are separated.  The cleared kernel
  vanishes at least linearly on the relevant branch (`Work.Asymptotics.one_zero_diag_at`
  and `one_zero_S_at`), while `j τ - j z` is bounded below by a multiple of the corresponding
  distance (`exists_j_diag_lower` below, built from
  `Work.Asymptotics.MiddleRange.exists_diffQuotient_lower`).
* `τ₀ = i`: the two branches merge and `j'(i) = 0`; here the cleared kernel vanishes at least
  *quadratically* (`two_zero_KfunClear_I`) and `j τ - j z` is bounded below by the product of the
  two `λ`-distances (`Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I` together with
  `exists_lambdaFun_lipschitz`).

At the coincidence points themselves (which are genuine zeroes of `growthPrefactor`) the value of
`K` is controlled directly by `Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.MiddleRange.norm_le_of_norm_le_of_two_zeros
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.MiddleRange.Basic
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Kernels.KernelFacts.KPlus_S_add

set_option maxHeartbeats 400000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Metric Filter Complex

namespace Work.Asymptotics

open Work.Kernels

namespace KL

/-! ## 0. Vendored one-zero machinery (from `Work.Asymptotics.KbcAux`) -/

lemma im_S (z₀ : ℍ) : (ModularGroup.S • z₀ : ℍ).im = z₀.im / ‖(z₀ : ℂ)‖ ^ 2 := by
  have h1 : ((ModularGroup.S • z₀ : ℍ) : ℂ) = (-(z₀ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  have h2 : (ModularGroup.S • z₀ : ℍ).im = ((-(z₀ : ℂ))⁻¹).im := by
    rw [← UpperHalfPlane.coe_im (ModularGroup.S • z₀), h1]
  rw [h2, Complex.inv_im, Complex.neg_im, UpperHalfPlane.coe_im, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq]
  ring


/-! ## 2. One-zero machinery (vendored from `Work.Asymptotics.KbcAux`) -/

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

lemma KfunClear_self (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d z z = 0 := by
  rw [KfunClear, Work.Residues.KPlusClear_diag d hd z, Work.Residues.KMinusClear_diag ℓ d hd z]
  ring

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

lemma exists_bound_KfunClear_of_balls (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (c₁ c₂ : ℍ) {R₁ R₂ : ℝ} (hR₁ : R₁ < c₁.im) (hR₂ : R₂ < c₂.im) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ z : ℍ, ‖(τ : ℂ) - (c₁ : ℂ)‖ ≤ R₁ → ‖(z : ℂ) - (c₂ : ℂ)‖ ≤ R₂ →
      ‖KfunClear ℓ d τ z‖ ≤ M := by
  obtain ⟨s₁, hs₁, hb₁⟩ := exists_scale_bound_euclidean (c := c₁) (r := R₁) hR₁
  obtain ⟨s₂, hs₂, hb₂⟩ := exists_scale_bound_euclidean (c := c₂) (r := R₂) hR₂
  obtain ⟨M, hM, h⟩ := exists_bound_KfunClear_of_scale_bounds ℓ d hd hs₁ hs₂
    (fun τ hτ => hb₁ τ hτ) (fun z hz => hb₂ z hz)
  exact ⟨M, hM, fun τ z h1 h2 => h τ h1 z h2⟩

lemma norm_sub_le_three (a b c : ℍ) :
    ‖(a : ℂ) - (b : ℂ)‖ ≤ ‖(a : ℂ) - (c : ℂ)‖ + ‖(c : ℂ) - (b : ℂ)‖ := by
  rw [show (a : ℂ) - (b : ℂ) = ((a : ℂ) - (c : ℂ)) + ((c : ℂ) - (b : ℂ)) by ring]
  exact norm_add_le _ _

lemma im_gt_sub_norm {a b : ℍ} {r : ℝ} (h : ‖(a : ℂ) - (b : ℂ)‖ < r) : b.im - r < a.im := by
  have h1 : |(a : ℂ).im - (b : ℂ).im| ≤ ‖(a : ℂ) - (b : ℂ)‖ := by
    rw [show (a : ℂ).im - (b : ℂ).im = ((a : ℂ) - (b : ℂ)).im by simp]
    exact Complex.abs_im_le_norm _
  have h2 := (abs_lt.mp (lt_of_le_of_lt h1 h)).1
  simp only [UpperHalfPlane.coe_im] at h2
  linarith

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
      have hd := (UpperHalfPlane.mdifferentiable_iff.mp hf).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu)
      exact hd.differentiableWithinAt
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
  simpa only [hFdef, UpperHalfPlane.ofComplex_apply] using h

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


/-! ## 1. Elementary facts about the imaginary axis and the involution `S` -/

lemma imagAxis_coe' (t : ℝ) (ht : 0 < t) : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl

lemma imagAxis_im' (t : ℝ) (ht : 0 < t) : (imagAxis t ht).im = t := by
  simp [imagAxis, Complex.mul_im]

lemma imagAxis_re' (t : ℝ) (ht : 0 < t) : ((imagAxis t ht : ℍ) : ℂ).re = 0 := by
  simp [imagAxis, Complex.mul_re]

lemma norm_imagAxis_sub (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    ‖((imagAxis t ht : ℍ) : ℂ) - ((imagAxis s hs : ℍ) : ℂ)‖ = |t - s| := by
  rw [imagAxis_coe', imagAxis_coe']
  have h : (t : ℂ) * Complex.I - (s : ℂ) * Complex.I = ((t - s : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma norm_imagAxis (t : ℝ) (ht : 0 < t) : ‖((imagAxis t ht : ℍ) : ℂ)‖ = t := by
  rw [imagAxis_coe', norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht]

lemma imagAxis_eq_I {t : ℝ} (ht : 0 < t) (h : t = 1) : imagAxis t ht = UpperHalfPlane.I := by
  subst h
  apply UpperHalfPlane.ext
  rw [imagAxis_coe', UpperHalfPlane.coe_I]
  norm_num

lemma coe_S_smul' (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

lemma S_smul_S_smul' (z : ℍ) : ModularGroup.S • (ModularGroup.S • z) = z := by
  have hSS : ModularGroup.S * ModularGroup.S = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    decide
  rw [← mul_smul, hSS, ModularGroup.SL_neg_smul, one_smul]

lemma S_smul_I' : ModularGroup.S • (UpperHalfPlane.I) = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul', UpperHalfPlane.coe_I, Complex.inv_I]
  ring

lemma S_fixpoint' {z : ℍ} (h : ModularGroup.S • z = z) : z = UpperHalfPlane.I := by
  have h1 := congrArg (fun w : ℍ => (w : ℂ)) h
  rw [coe_S_smul'] at h1
  have hz : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have h2 : (z : ℂ) ^ 2 = -1 := by
    field_simp at h1
    linear_combination (-1 : ℂ) * h1
  have h3 : (z : ℂ) - Complex.I = 0 ∨ (z : ℂ) + Complex.I = 0 := by
    have hh : ((z : ℂ) - Complex.I) * ((z : ℂ) + Complex.I) = 0 := by
      have e : ((z : ℂ) - Complex.I) * ((z : ℂ) + Complex.I)
          = (z : ℂ) ^ 2 - Complex.I ^ 2 := by ring
      rw [e, h2, Complex.I_sq]; ring
    exact mul_eq_zero.mp hh
  rcases h3 with h3 | h3
  · have hh : (z : ℂ) = Complex.I := sub_eq_zero.mp h3
    exact UpperHalfPlane.ext (by rw [hh, UpperHalfPlane.coe_I])
  · have hh : (z : ℂ) = -Complex.I := by linear_combination h3
    exfalso
    have him := congrArg Complex.im hh
    simp at him
    linarith [z.im_pos]

/-- `‖S z - i‖ ≤ 2 ‖z - i‖` for `‖z - i‖ < 1/2`, in the `ℍ`-point form. -/
lemma norm_S_sub_I_le' (z : ℍ) (h : ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 1 / 2) :
    ‖((ModularGroup.S • z : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)‖ ≤
      2 * ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ := by
  rw [show ((ModularGroup.S • z : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)
      = ((ModularGroup.S • z : ℍ) : ℂ) - ((ModularGroup.S • UpperHalfPlane.I : ℍ) : ℂ) by
    rw [S_smul_I']]
  rw [norm_S_sub_S]
  have hI : ‖((UpperHalfPlane.I : ℍ) : ℂ)‖ = 1 := by rw [UpperHalfPlane.coe_I, Complex.norm_I]
  rw [hI, mul_one]
  have hzn : (1:ℝ) / 2 ≤ ‖(z : ℂ)‖ := by
    have h1 : ‖(z : ℂ)‖ ≥ ‖((UpperHalfPlane.I : ℍ) : ℂ)‖ -
        ‖(z : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ)‖ := by
      have h2 := (abs_le.mp (abs_norm_sub_norm_le (z : ℂ) ((UpperHalfPlane.I : ℍ) : ℂ))).1
      linarith
    rw [hI] at h1
    linarith
  rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖(z : ℂ)‖)]
  nlinarith [norm_nonneg ((z : ℂ) - ((UpperHalfPlane.I : ℍ) : ℂ))]


/-! ## 3. A two-zero maximum-modulus bound for functions on `ℍ` -/

/-- **Two-zero bound on `ℍ`** (Euclidean distances), the two-zero companion of
`Work.Asymptotics.one_zero_apply`. -/
theorem two_zero_apply {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {c : ℍ} {r M : ℝ}
    (hr0 : 0 < r) (hr : r < c.im) (hM : 0 ≤ M)
    (hbd : ∀ w : ℍ, ‖(w : ℂ) - (c : ℂ)‖ ≤ r → ‖f w‖ ≤ M)
    {w₁ w₂ : ℍ} (h₁ : ‖(w₁ : ℂ) - (c : ℂ)‖ < r / 2) (h₂ : ‖(w₂ : ℂ) - (c : ℂ)‖ < r / 2)
    (hne : w₁ ≠ w₂) (hz₁ : f w₁ = 0) (hz₂ : f w₂ = 0) :
    ∀ w : ℍ, ‖(w : ℂ) - (c : ℂ)‖ < r / 2 →
      ‖f w‖ ≤ (4 * M / r ^ 2) * ‖(w : ℂ) - (w₁ : ℂ)‖ * ‖(w : ℂ) - (w₂ : ℂ)‖ := by
  intro w hw
  set F : ℂ → ℂ := fun u => f (UpperHalfPlane.ofComplex u) with hFdef
  have hsub : Metric.closedBall (c : ℂ) r ⊆ {u : ℂ | 0 < u.im} := closedBall_subset_upper hr
  have hof : ∀ (u : ℂ) (hu : 0 < u.im), UpperHalfPlane.ofComplex u = ⟨u, hu⟩ :=
    fun u hu => UpperHalfPlane.ofComplex_apply_of_im_pos hu
  have hF : DiffContOnCl ℂ F (Metric.ball (c : ℂ) r) := by
    have hdiff : DifferentiableOn ℂ F {u : ℂ | 0 < u.im} := by
      intro u hu
      have hd := (UpperHalfPlane.mdifferentiable_iff.mp hf).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu)
      exact hd.differentiableWithinAt
    exact hdiff.diffContOnCl_ball hsub
  have hbdF : ∀ u ∈ Metric.ball (c : ℂ) r, ‖F u‖ ≤ M := by
    intro u hu
    have hu' : 0 < u.im := hsub (Metric.ball_subset_closedBall hu)
    have h1 : ‖u - (c : ℂ)‖ ≤ r := le_of_lt (by simpa [dist_eq_norm] using hu)
    have h2 := hbd ⟨u, hu'⟩ h1
    show ‖f (UpperHalfPlane.ofComplex u)‖ ≤ M
    rw [hof u hu']
    exact h2
  have hz₁F : F (w₁ : ℂ) = 0 := by simp only [hFdef, UpperHalfPlane.ofComplex_apply, hz₁]
  have hz₂F : F (w₂ : ℂ) = 0 := by simp only [hFdef, UpperHalfPlane.ofComplex_apply, hz₂]
  have hneF : (w₁ : ℂ) ≠ (w₂ : ℂ) := fun h => hne (UpperHalfPlane.ext h)
  have hb₁ : (w₁ : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact h₁
  have hb₂ : (w₂ : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact h₂
  have hw' : (w : ℂ) ∈ Metric.ball (c : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hw
  have hmain := MiddleRange.norm_le_of_norm_le_of_two_zeros hr0 hM hF hbdF hb₁ hb₂ hneF hz₁F hz₂F
    (w : ℂ) hw'
  simpa only [hFdef, UpperHalfPlane.ofComplex_apply] using hmain

/-! ## 3. The cleared kernel vanishes (at least) quadratically at `τ = z = i` -/

/-- `KfunClear` vanishes on the `S`-branch: `KfunClear z (S z) = 0`. -/
lemma KfunClear_S_smul' (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d z (ModularGroup.S • z) = 0 := by
  obtain ⟨h1, h2⟩ := KClear_S_vanishing ℓ d hd (ModularGroup.S • z)
  rw [S_smul_S_smul'] at h1 h2
  simp only [KfunClear]
  rw [h1, h2]
  ring

/-- Near `i` the cleared kernel vanishes at least quadratically in the two distances
`‖z - τ‖` and `‖z - S τ‖`. -/
theorem two_zero_KfunClear_I (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ τ z : ℍ,
      ‖(τ : ℂ) - Complex.I‖ < ρ → ‖(z : ℂ) - Complex.I‖ < ρ →
      ‖KfunClear ℓ d τ z‖ ≤ C * ‖(z : ℂ) - (τ : ℂ)‖ *
        ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖ := by
  obtain ⟨M, hM, hMb⟩ := exists_bound_KfunClear_of_balls ℓ d hd UpperHalfPlane.I
    UpperHalfPlane.I (R₁ := 3 / 4) (R₂ := 3 / 4) (by norm_num) (by norm_num)
  have hI1 : ((UpperHalfPlane.I : ℍ) : ℂ) = Complex.I := UpperHalfPlane.coe_I
  have hIim : (UpperHalfPlane.I : ℍ).im = 1 := by simp [UpperHalfPlane.I]
  refine ⟨1 / 16, 8 * M / (1 / 4) ^ 2, by norm_num, by positivity, fun τ z hτ hz => ?_⟩
  have hτp : ‖(τ : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 1 / 16 := by rw [hI1]; exact hτ
  have hzp : ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 1 / 16 := by rw [hI1]; exact hz
  have hτ4 : ‖(τ : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 3 / 4 := by linarith
  have hz4 : ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 3 / 4 := by linarith
  have hτ8 : ‖(τ : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 1 / 4 / 2 := by linarith
  have hz8 : ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 1 / 4 / 2 := by linarith
  have hSτ8 : ‖((ModularGroup.S • τ : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 1 / 4 / 2 := by
    have h := norm_S_sub_I_le' τ (by linarith)
    linarith
  have hSz8 : ‖((ModularGroup.S • z : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)‖ < 1 / 4 / 2 := by
    have h := norm_S_sub_I_le' z (by linarith)
    linarith
  have hSz2 : ‖(UpperHalfPlane.I : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖
      ≤ 2 * ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ := by
    rw [norm_sub_rev]
    exact norm_S_sub_I_le' z (by linarith)
  by_cases hτI : τ = UpperHalfPlane.I
  · subst hτI
    by_cases hzI : z = UpperHalfPlane.I
    · subst hzI
      have h0 : KfunClear ℓ d UpperHalfPlane.I UpperHalfPlane.I = 0 := KfunClear_self ℓ d hd _
      rw [h0, norm_zero]
      positivity
    · have hne1 : z ≠ ModularGroup.S • z := fun h => hzI (S_fixpoint' h.symm)
      have hmain := two_zero_apply (f := fun w : ℍ => KfunClear ℓ d w z)
        (mdifferentiable_KfunClear_fst ℓ d hd z) (c := UpperHalfPlane.I) (r := 1 / 4)
        (M := M) (by norm_num) (by norm_num) hM.le
        (fun w hw => hMb w z (by linarith) (le_of_lt hz4))
        hz8 hSz8 hne1 (KfunClear_self ℓ d hd z) (KfunClear_S_self ℓ d hd z)
        UpperHalfPlane.I (by rw [sub_self, norm_zero]; norm_num)
      have h := hmain
      calc ‖KfunClear ℓ d UpperHalfPlane.I z‖
          ≤ (4 * M / (1 / 4) ^ 2) * ‖(UpperHalfPlane.I : ℂ) - (z : ℂ)‖ *
              ‖(UpperHalfPlane.I : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ := h
        _ ≤ (4 * M / (1 / 4) ^ 2) * ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ *
              (2 * ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖) := by
            have h1 : ‖(UpperHalfPlane.I : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖
                ≤ 2 * ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ := hSz2
            have h2 : ‖(UpperHalfPlane.I : ℂ) - (z : ℂ)‖
                ≤ ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ := le_of_eq (norm_sub_rev _ _)
            exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
              (norm_nonneg _) (by positivity)
        _ = 8 * M / (1 / 4) ^ 2 * ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ *
              ‖(z : ℂ) - ((ModularGroup.S • UpperHalfPlane.I : ℍ) : ℂ)‖ := by
            rw [S_smul_I']
            ring
  · have hne1 : τ ≠ ModularGroup.S • τ := fun h => hτI (S_fixpoint' h.symm)
    have hmain := two_zero_apply (f := fun w : ℍ => KfunClear ℓ d τ w)
      (mdifferentiable_KfunClear_snd ℓ d hd τ) (c := UpperHalfPlane.I) (r := 1 / 4)
      (M := M) (by norm_num) (by norm_num) hM.le
      (fun w hw => hMb τ w (le_of_lt hτ4) (by linarith))
      hτ8 hSτ8 hne1 (KfunClear_self ℓ d hd τ) (KfunClear_S_smul' ℓ d hd τ)
      z hz8
    have h := hmain
    calc ‖KfunClear ℓ d τ z‖
        ≤ (4 * M / (1 / 4) ^ 2) * ‖(z : ℂ) - (τ : ℂ)‖ *
            ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖ := h
      _ ≤ 8 * M / (1 / 4) ^ 2 * ‖(z : ℂ) - (τ : ℂ)‖ *
            ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖ := by
          have h3 : 4 * M / (1 / 4) ^ 2 ≤ 8 * M / (1 / 4) ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
            (norm_nonneg _)

/-! ## 4. The `j`-difference is bounded below by the distance, away from `i` -/

/-- **`j` dominates the distance near an imaginary-axis point `it₀ ≠ i`.** -/
theorem exists_j_diag_lower {t₀ : ℝ} (ht₀ : 0 < t₀) (hne : t₀ ≠ 1) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ u v : ℍ,
      ‖(u : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ →
      ‖(v : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ →
      c * ‖(u : ℂ) - (v : ℂ)‖ ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
  rcases le_or_gt t₀ 1 with ht1 | ht1
  · -- `t₀ ≤ 1`: use the difference-quotient estimate directly
    obtain ⟨ρ, hρ, c, hc, hb⟩ := MiddleRange.exists_diffQuotient_lower (ε := t₀ / 2)
      (by linarith) (by linarith) ht1 hne
    refine ⟨ρ, c, hρ, hc, fun u v hu hv => ?_⟩
    exact hb u v (by simpa [imagAxis] using hu) (by simpa [imagAxis] using hv)
  · -- `t₀ > 1`: transport along `S`
    have ht1pos : (0:ℝ) < 1 / t₀ := by positivity
    have hne' : (1 : ℝ) / t₀ ≠ 1 := by
      intro h
      apply hne
      field_simp at h
      linarith
    obtain ⟨ρ₂, hρ₂, c₂, hc₂, hb₂⟩ := MiddleRange.exists_diffQuotient_lower (ε := (1 / t₀) / 2)
      (by positivity) (by linarith) (by rw [div_le_one ht₀]; linarith) hne'
    -- `S (i t₀) = i / t₀`
    have hSz : ModularGroup.S • imagAxis t₀ ht₀ = imagAxis (1 / t₀) ht1pos := by
      apply UpperHalfPlane.ext
      rw [coe_S_smul', imagAxis_coe', imagAxis_coe']
      calc -(((t₀ : ℂ) * Complex.I))⁻¹ = -((Complex.I)⁻¹ * ((t₀ : ℝ) : ℂ)⁻¹) := by
            rw [_root_.mul_inv_rev]
        _ = -((-Complex.I) * ((t₀ : ℝ) : ℂ)⁻¹) := by rw [Complex.inv_I]
        _ = Complex.I * ((t₀ : ℝ) : ℂ)⁻¹ := by ring
        _ = ((1 / t₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hz₀norm : ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ = t₀ := norm_imagAxis t₀ ht₀
    refine ⟨min (ρ₂ * (t₀ / 2) ^ 2) (t₀ / 2), c₂ / (3 * t₀ / 2) ^ 2,
      lt_min (by positivity) (by linarith), by positivity, fun u v hu hv => ?_⟩
    have hu' : ‖(u : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < t₀ / 2 :=
      lt_of_lt_of_le hu (min_le_right _ _)
    have hv' : ‖(v : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < t₀ / 2 :=
      lt_of_lt_of_le hv (min_le_right _ _)
    have hun : t₀ / 2 ≤ ‖(u : ℂ)‖ := by
      have h1 : ‖(u : ℂ)‖ ≥ ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ -
          ‖(u : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
        have h2 := (abs_le.mp (abs_norm_sub_norm_le (u : ℂ) ((imagAxis t₀ ht₀ : ℍ) : ℂ))).1
        linarith
      rw [hz₀norm] at h1
      linarith
    have hvn : t₀ / 2 ≤ ‖(v : ℂ)‖ := by
      have h1 : ‖(v : ℂ)‖ ≥ ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ -
          ‖(v : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
        have h2 := (abs_le.mp (abs_norm_sub_norm_le (v : ℂ) ((imagAxis t₀ ht₀ : ℍ) : ℂ))).1
        linarith
      rw [hz₀norm] at h1
      linarith
    have hun' : ‖(u : ℂ)‖ ≤ 3 * t₀ / 2 := by
      have h1 : ‖(u : ℂ)‖ ≤ ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ +
          ‖(u : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
        have h := norm_add_le ((u : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ))
          ((imagAxis t₀ ht₀ : ℍ) : ℂ)
        rw [sub_add_cancel] at h
        linarith [h]
      rw [hz₀norm] at h1
      linarith
    have hvn' : ‖(v : ℂ)‖ ≤ 3 * t₀ / 2 := by
      have h1 : ‖(v : ℂ)‖ ≤ ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ +
          ‖(v : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
        have h := norm_add_le ((v : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ))
          ((imagAxis t₀ ht₀ : ℍ) : ℂ)
        rw [sub_add_cancel] at h
        linarith [h]
      rw [hz₀norm] at h1
      linarith
    have hSu : ‖((ModularGroup.S • u : ℍ) : ℂ) - ((imagAxis (1 / t₀) ht1pos : ℍ) : ℂ)‖
        < ρ₂ := by
      rw [← hSz, norm_S_sub_S]
      have hnum : ‖(u : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ₂ * (t₀ / 2) ^ 2 :=
        lt_of_lt_of_le hu (min_le_left _ _)
      have hden : t₀ ^ 2 / 2 ≤ ‖(u : ℂ)‖ * ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
        rw [hz₀norm]
        nlinarith [hun]
      rw [div_lt_iff₀ (lt_of_lt_of_le (by positivity : (0:ℝ) < t₀ ^ 2 / 2) hden)]
      nlinarith [hnum, hden, hρ₂]
    have hSv : ‖((ModularGroup.S • v : ℍ) : ℂ) - ((imagAxis (1 / t₀) ht1pos : ℍ) : ℂ)‖
        < ρ₂ := by
      rw [← hSz, norm_S_sub_S]
      have hnum : ‖(v : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ₂ * (t₀ / 2) ^ 2 :=
        lt_of_lt_of_le hv (min_le_left _ _)
      have hden : t₀ ^ 2 / 2 ≤ ‖(v : ℂ)‖ * ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
        rw [hz₀norm]
        nlinarith [hvn]
      rw [div_lt_iff₀ (lt_of_lt_of_le (by positivity : (0:ℝ) < t₀ ^ 2 / 2) hden)]
      nlinarith [hnum, hden, hρ₂]
    have hjj : c₂ * ‖((ModularGroup.S • u : ℍ) : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖
        ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
      have h := hb₂ (ModularGroup.S • u) (ModularGroup.S • v) hSu hSv
      simpa only [KernelFacts.jInvariantFun_S_smul] using h
    have hdist : ‖(u : ℂ) - (v : ℂ)‖ / (3 * t₀ / 2) ^ 2 ≤
        ‖((ModularGroup.S • u : ℍ) : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖ := by
      rw [norm_S_sub_S]
      refine div_le_div_of_nonneg_left (norm_nonneg _)
        (mul_pos (lt_of_lt_of_le (by linarith : (0:ℝ) < t₀ / 2) hun)
          (lt_of_lt_of_le (by linarith : (0:ℝ) < t₀ / 2) hvn)) ?_
      nlinarith [hun', hvn']
    have hfin : c₂ / (3 * t₀ / 2) ^ 2 * ‖(u : ℂ) - (v : ℂ)‖ ≤
        c₂ * ‖((ModularGroup.S • u : ℍ) : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖ := by
      calc c₂ / (3 * t₀ / 2) ^ 2 * ‖(u : ℂ) - (v : ℂ)‖
          = c₂ * (‖(u : ℂ) - (v : ℂ)‖ / (3 * t₀ / 2) ^ 2) := by ring
        _ ≤ c₂ * ‖((ModularGroup.S • u : ℍ) : ℂ) - ((ModularGroup.S • v : ℍ) : ℂ)‖ :=
            mul_le_mul_of_nonneg_left hdist hc₂.le
    exact le_trans hfin hjj

/-! ## 5. `Δ` is bounded below near a point of `ℍ` -/

/-- A Euclidean ball of radius `ρ ≤ im c / 2` around `c ∈ ℍ` is contained in the hyperbolic
closed ball of radius `1`. -/
lemma dist_le_one_of_norm_lt {c : ℍ} {ρ : ℝ} (hρ : ρ ≤ c.im / 2) {z : ℍ}
    (h : ‖(z : ℂ) - (c : ℂ)‖ < ρ) : dist z c ≤ 1 := by
  have h1 : dist z c ≤ ‖(z : ℂ) - (c : ℂ)‖ / Real.sqrt (z.im * c.im) := by
    have h := UpperHalfPlane.dist_le_dist_coe_div_sqrt z c
    rwa [dist_eq_norm] at h
  have hzi : c.im / 2 ≤ z.im := by
    have h2 := im_gt_sub_norm (a := z) (b := c) h
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

/-- `Δ` is bounded away from zero on a Euclidean neighbourhood of any point of `ℍ`. -/
theorem exists_DeltaFun_lower (z₀ : ℍ) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ ∀ z : ℍ, ‖(z : ℂ) - (z₀ : ℂ)‖ < ρ → δ ≤ ‖DeltaFun z‖ := by
  obtain ⟨δ, hδ, hb⟩ := exists_lower_DeltaFun (isCompact_closedBall z₀ 1)
  refine ⟨min (z₀.im / 4) (1 / 2), δ, lt_min (by linarith [z₀.im_pos]) (by norm_num), hδ,
    fun z hz => hb z (dist_le_one_of_norm_lt (ρ := min (z₀.im / 4) (1 / 2))
      (le_trans (min_le_left _ _) (by linarith [z₀.im_pos])) hz)⟩

/-! ## 6. Coincidences are controlled by Theorem 4.9 -/

theorem exists_coin_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ₀ z₀ : ℍ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ z : ℍ, dist τ τ₀ ≤ 1 → dist z z₀ ≤ 1 →
      jInvariantFun τ = jInvariantFun z → ‖Kfun ℓ d τ z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := MiddleRange.exists_bound_Kfun_of_coincidence ℓ d hd
    (isCompact_closedBall τ₀ 1) (isCompact_closedBall z₀ 1)
  exact ⟨C, hC, fun τ z h1 h2 h3 =>
    hb τ z (by rwa [Metric.mem_closedBall]) (by rwa [Metric.mem_closedBall]) h3⟩

/-! ## 7. The relation between `Kfun` and the cleared kernel -/

lemma Kfun_eq_KfunClear_div (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ)
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
  by_cases hd8 : d = 8 <;> simp [growthPrefactor, hd8, norm_pow]

/-! ## 8. The local Euclidean bound at a coincidence -/

/-- **The Euclidean local bound.**  Near a coincidence `(τ₀, i t₀)` with `τ₀ ∈ 𝒟` the kernel
`Kfun` is bounded. -/
theorem key_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : ℍ} (hτ₀ : τ₀ ∈ DomainD) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hcoin : jInvariantFun τ₀ = jInvariantFun (imagAxis t₀ ht₀)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ τ z : ℍ,
      ‖(τ : ℂ) - (τ₀ : ℂ)‖ < ρ → ‖(z : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ →
      ‖Kfun ℓ d τ z‖ ≤ C := by
  have hcases := eq_or_eq_S_of_re_eq_zero hτ₀ (imagAxis_re' t₀ ht₀) hcoin
  by_cases hI : τ₀ = UpperHalfPlane.I
  · -- the elliptic point `i`
    have hz₀I : (imagAxis t₀ ht₀ : ℍ) = UpperHalfPlane.I := by
      rcases hcases with h | h
      · rw [h]; exact hI
      · rw [h, hI, S_smul_I']
    obtain ⟨ρ₂, C₂, hρ₂, hC₂, hb₂⟩ := two_zero_KfunClear_I ℓ d hd
    obtain ⟨ρ₃, hρ₃, c₃, hc₃, hb₃⟩ := MiddleRange.exists_lambdaFun_lipschitz UpperHalfPlane.I
    obtain ⟨ρ₄, hρ₄, c₄, hc₄, hb₄⟩ := MiddleRange.exists_j_sub_lower_lambda_near_I
    obtain ⟨ρ₅, δ, hρ₅, hδ, hb₅⟩ := exists_DeltaFun_lower UpperHalfPlane.I
    obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_coin_bound ℓ d hd τ₀ (imagAxis t₀ ht₀)
    have hI1 : ((UpperHalfPlane.I : ℍ) : ℂ) = Complex.I := UpperHalfPlane.coe_I
    have hIim : (UpperHalfPlane.I : ℍ).im = 1 := by simp [UpperHalfPlane.I]
    set e : ℕ := (if d = 8 then 1 else 2) with he
    set D : ℝ := δ ^ (1 + e) * (c₄ * c₃ ^ 2) with hDdef
    set ρ : ℝ := min (min (min ρ₂ ρ₃) (min ρ₄ ρ₅)) (min (1 / 8) (ρ₃ / 2)) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact lt_min (lt_min (lt_min hρ₂ hρ₃) (lt_min hρ₄ hρ₅)) (lt_min (by norm_num) (by linarith))
    have hρρ₂ : ρ ≤ ρ₂ := le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
    have hρρ₃ : ρ ≤ ρ₃ := le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
    have hρρ₄ : ρ ≤ ρ₄ := le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_left _ _)
    have hρρ₅ : ρ ≤ ρ₅ := le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_right _ _)
    have hρ18 : ρ ≤ 1 / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hρ32 : ρ ≤ ρ₃ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have hρ12 : ρ ≤ (1:ℝ) / 2 := by linarith
    have hIim2 : (1:ℝ) / 2 ≤ (UpperHalfPlane.I : ℍ).im / 2 := by rw [hIim]
    have hDpos : 0 < D := by rw [hDdef]; positivity
    refine ⟨ρ, max C₀ (C₂ / D), hρpos, le_max_of_le_left hC₀pos.le, fun τ z hτ hz => ?_⟩
    have hτp : ‖(τ : ℂ) - (UpperHalfPlane.I : ℂ)‖ < ρ := by rw [← hI]; exact hτ
    have hzp : ‖(z : ℂ) - (UpperHalfPlane.I : ℂ)‖ < ρ := by rw [← hz₀I]; exact hz
    have hτ' : ‖(τ : ℂ) - Complex.I‖ < ρ := by simpa only [hI1] using hτp
    have hz' : ‖(z : ℂ) - Complex.I‖ < ρ := by simpa only [hI1] using hzp
    by_cases hJ : jInvariantFun τ = jInvariantFun z
    · have hc := hC₀ τ z (by rw [hI]; exact dist_le_one_of_norm_lt (le_trans hρ12 hIim2) hτp)
        (by rw [hz₀I]; exact dist_le_one_of_norm_lt (le_trans hρ12 hIim2) hzp) hJ
      exact le_trans hc (le_max_left _ _)
    · set P : ℝ := ‖(τ : ℂ) - (z : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖
        with hPdef
      set Jv : ℝ := ‖jInvariantFun τ - jInvariantFun z‖ with hJvdef
      set GP : ℝ := ‖growthPrefactor d τ z‖ with hGPdef
      have hPpos : 0 < P := by
        rw [hPdef]
        refine mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hJ (by
          rw [UpperHalfPlane.ext h])))) ?_
        refine norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hJ ?_))
        have hzz : z = ModularGroup.S • τ := UpperHalfPlane.ext h
        rw [hzz, KernelFacts.jInvariantFun_S_smul]
      have hnum : ‖KfunClear ℓ d τ z‖ ≤ C₂ * P := by
        rw [hPdef, ← mul_assoc]
        refine le_trans (hb₂ τ z (lt_of_lt_of_le hτ' hρρ₂) (lt_of_lt_of_le hz' hρρ₂)) ?_
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₂.le) (norm_nonneg _)
        exact le_of_eq (norm_sub_rev (z : ℂ) (τ : ℂ))
      have hlam1 : c₃ * ‖(τ : ℂ) - (z : ℂ)‖ ≤ ‖lambdaFun τ - lambdaFun z‖ :=
        hb₃ τ z (by simpa only [hI1] using lt_of_lt_of_le hτp hρρ₃)
          (by simpa only [hI1] using lt_of_lt_of_le hzp hρρ₃)
      have hSτ : ‖((ModularGroup.S • τ : ℍ) : ℂ) - Complex.I‖ < ρ₃ := by
        have h1 : ‖((ModularGroup.S • τ : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)‖
            ≤ 2 * ‖(τ : ℂ) - (UpperHalfPlane.I : ℂ)‖ :=
          norm_S_sub_I_le' τ (by linarith)
        rw [hI1] at h1
        linarith
      have hlS : c₃ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖
          ≤ ‖lambdaFun z - lambdaFun (ModularGroup.S • τ)‖ :=
        hb₃ z (ModularGroup.S • τ)
          (by simpa only [hI1] using lt_of_lt_of_le hzp hρρ₃) hSτ
      have hJ' : c₄ * ‖lambdaFun τ - lambdaFun z‖ *
          ‖lambdaFun τ + lambdaFun z - 1‖ ≤ Jv := by
        rw [hJvdef]
        exact hb₄ τ z (lt_of_lt_of_le hτ' hρρ₄) (lt_of_lt_of_le hz' hρρ₄)
      have hlSz : lambdaFun τ + lambdaFun z - 1
          = lambdaFun z - lambdaFun (ModularGroup.S • τ) := by
        rw [LogLambda.lambdaFun_S]
        have h := Rigidity.lambdaFun_add_lambdaSFun τ
        linear_combination h
      have hJlow : c₄ * c₃ ^ 2 * P ≤ Jv := by
        rw [hPdef, hJvdef]
        have h1 : c₄ * (c₃ * ‖(τ : ℂ) - (z : ℂ)‖) *
            (c₃ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖)
            ≤ c₄ * ‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖ := by
          calc c₄ * (c₃ * ‖(τ : ℂ) - (z : ℂ)‖) *
                (c₃ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖)
              ≤ (c₄ * ‖lambdaFun τ - lambdaFun z‖) *
                ‖lambdaFun z - lambdaFun (ModularGroup.S • τ)‖ :=
                mul_le_mul (mul_le_mul_of_nonneg_left hlam1 hc₄.le) hlS (by positivity)
                  (by positivity)
            _ = c₄ * ‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖ := by
                rw [hlSz]
        calc c₄ * c₃ ^ 2 * (‖(τ : ℂ) - (z : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖)
            = c₄ * (c₃ * ‖(τ : ℂ) - (z : ℂ)‖) *
              (c₃ * ‖(z : ℂ) - ((ModularGroup.S • τ : ℍ) : ℂ)‖) := by ring
          _ ≤ c₄ * ‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖ := h1
          _ ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
              rw [← hJvdef]; exact hJ'
      have hnorm : GP = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e *
          ‖jInvariantFun τ - jInvariantFun z‖ := by
        rw [hGPdef]; simpa [he] using norm_growthPrefactor d τ z
      have hτ5 : ‖(τ : ℂ) - Complex.I‖ < ρ₅ := lt_of_lt_of_le hτ' hρρ₅
      have hz5 : ‖(z : ℂ) - Complex.I‖ < ρ₅ := lt_of_lt_of_le hz' hρρ₅
      have hΔτ : δ ≤ ‖DeltaFun τ‖ := hb₅ τ (by simpa only [hI1] using hτ5)
      have hΔz : δ ≤ ‖DeltaFun z‖ := hb₅ z (by simpa only [hI1] using hz5)
      have hlow : D * P ≤ ‖growthPrefactor d τ z‖ := by
        have hBe : δ ^ e ≤ ‖DeltaFun z‖ ^ e := pow_le_pow_left₀ hδ.le hΔz e
        have h1 : δ * δ ^ e ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e :=
          mul_le_mul hΔτ hBe (pow_nonneg hδ.le e) (norm_nonneg _)
        calc D * P = (δ * δ ^ e) * (c₄ * c₃ ^ 2 * P) := by
              rw [hDdef, show δ ^ (1 + e) = δ * δ ^ e by rw [pow_add, pow_one]]; ring
          _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e) * Jv :=
              mul_le_mul h1 hJlow (mul_nonneg (mul_nonneg hc₄.le (pow_nonneg hc₃.le 2)) hPpos.le)
                (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) e))
          _ = GP := by rw [hnorm, hJvdef]
      have hgppos : 0 < GP := by rw [hGPdef]; exact lt_of_lt_of_le (mul_pos hDpos hPpos) hlow
      have hgp : ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / GP := by
        rw [Kfun_eq_KfunClear_div ℓ d hd τ z hJ, norm_div, hGPdef]
      have hstep : ‖KfunClear ℓ d τ z‖ * D ≤ C₂ * GP := by
        calc ‖KfunClear ℓ d τ z‖ * D ≤ (C₂ * P) * D := mul_le_mul_of_nonneg_right hnum hDpos.le
          _ = C₂ * (D * P) := by ring
          _ ≤ C₂ * GP := by rw [hGPdef]; exact mul_le_mul_of_nonneg_left hlow hC₂.le
      calc ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / GP := hgp
        _ ≤ C₂ / D := (div_le_div_iff₀ hgppos hDpos).mpr hstep
        _ ≤ max C₀ (C₂ / D) := le_max_right _ _
  · -- `τ₀ ≠ i`: the two branches are separated
    have ht₀ne : t₀ ≠ 1 := by
      intro ht1
      apply hI
      rcases hcases with h | h
      · rw [imagAxis_eq_I ht₀ ht1] at h; exact h.symm
      · rw [imagAxis_eq_I ht₀ ht1] at h
        have h2 : ModularGroup.S • UpperHalfPlane.I = ModularGroup.S • (ModularGroup.S • τ₀) := by
          rw [h]
        rw [S_smul_I', S_smul_S_smul'] at h2
        exact h2.symm
    rcases hcases with hz0 | hz0
    · -- diagonal branch, `z₀ = τ₀`
      obtain ⟨ρ₁, C₁, hρ₁, hC₁, hb₁⟩ := one_zero_diag_at ℓ d hd τ₀
      obtain ⟨ρ₂, c₂, hρ₂, hc₂, hb₂⟩ := exists_j_diag_lower ht₀ ht₀ne
      obtain ⟨ρ₃, δ, hρ₃, hδ, hb₃⟩ := exists_DeltaFun_lower τ₀
      obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_coin_bound ℓ d hd τ₀ (imagAxis t₀ ht₀)
      set e : ℕ := (if d = 8 then 1 else 2) with he
      set D : ℝ := δ ^ (1 + e) * c₂ with hDdef
      set ρim : ℝ := min (τ₀.im / 2) ((imagAxis t₀ ht₀ : ℍ).im / 2) with hρim
      have hρimpos : 0 < ρim := by
        rw [hρim]
        refine lt_min (by linarith [τ₀.im_pos]) (by rw [imagAxis_im']; linarith)
      set ρ : ℝ := min (min (min ρ₁ ρ₂) (min ρ₃ ρim)) 1 with hρdef
      have hρpos : 0 < ρ := lt_min (lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hρimpos)) one_pos
      have hρρ₁ : ρ ≤ ρ₁ :=
        le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
      have hρρ₂ : ρ ≤ ρ₂ :=
        le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
      have hρρ₃ : ρ ≤ ρ₃ :=
        le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_left _ _)
      have hρρim : ρ ≤ ρim :=
        le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_right _ _)
      have hρ1 : ρ ≤ 1 := min_le_right _ _
      have hρimτ : ρim ≤ τ₀.im / 2 := min_le_left _ _
      have hρimz : ρim ≤ (imagAxis t₀ ht₀ : ℍ).im / 2 := min_le_right _ _
      have hDpos : 0 < D := by rw [hDdef]; positivity
      refine ⟨ρ, max C₀ (C₁ / D), hρpos, le_max_of_le_left hC₀pos.le, fun τ z hτ hz => ?_⟩
      have hzτ : ‖(z : ℂ) - (τ₀ : ℂ)‖ < ρ := by rw [← hz0]; exact hz
      have hτz0 : ‖(τ : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ := by rw [hz0]; exact hτ
      by_cases hJ : jInvariantFun τ = jInvariantFun z
      · have hc := hC₀ τ z (dist_le_one_of_norm_lt (le_trans hρρim hρimτ) hτ)
          (dist_le_one_of_norm_lt (le_trans hρρim hρimz) hz) hJ
        exact le_trans hc (le_max_left _ _)
      · set P : ℝ := ‖(τ : ℂ) - (z : ℂ)‖ with hPdef
        set Jv : ℝ := ‖jInvariantFun τ - jInvariantFun z‖ with hJvdef
        set GP : ℝ := ‖growthPrefactor d τ z‖ with hGPdef
        have hPpos : 0 < P := by
          rw [hPdef]
          exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hJ (by rw [UpperHalfPlane.ext h])))
        have hnum : ‖KfunClear ℓ d τ z‖ ≤ C₁ * P := by
          rw [hPdef]
          exact hb₁ τ z (lt_of_lt_of_le hτ hρρ₁) (lt_of_lt_of_le hzτ hρρ₁)
        have hJlow : c₂ * P ≤ Jv := by
          rw [hPdef, hJvdef]
          exact hb₂ τ z (lt_of_lt_of_le hτz0 hρρ₂) (lt_of_lt_of_le hz hρρ₂)
        have hΔτ : δ ≤ ‖DeltaFun τ‖ := hb₃ τ (lt_of_lt_of_le hτ hρρ₃)
        have hΔz : δ ≤ ‖DeltaFun z‖ := hb₃ z (lt_of_lt_of_le hzτ hρρ₃)
        have hnorm : GP = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e *
            ‖jInvariantFun τ - jInvariantFun z‖ := by
          rw [hGPdef]; simpa [he] using norm_growthPrefactor d τ z
        have hlow : D * P ≤ ‖growthPrefactor d τ z‖ := by
          have hBe : δ ^ e ≤ ‖DeltaFun z‖ ^ e := pow_le_pow_left₀ hδ.le hΔz e
          have h1 : δ * δ ^ e ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e :=
            mul_le_mul hΔτ hBe (pow_nonneg hδ.le e) (norm_nonneg _)
          calc D * P = (δ * δ ^ e) * (c₂ * P) := by
                rw [hDdef, show δ ^ (1 + e) = δ * δ ^ e by rw [pow_add, pow_one]]; ring
            _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e) * Jv :=
                mul_le_mul h1 hJlow (mul_nonneg hc₂.le hPpos.le)
                (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) e))
            _ = GP := by rw [hnorm, hJvdef]
        have hgppos : 0 < GP := by rw [hGPdef]; exact lt_of_lt_of_le (mul_pos hDpos hPpos) hlow
        have hgp : ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / GP := by
          rw [Kfun_eq_KfunClear_div ℓ d hd τ z hJ, norm_div, hGPdef]
        have hstep : ‖KfunClear ℓ d τ z‖ * D ≤ C₁ * GP := by
          calc ‖KfunClear ℓ d τ z‖ * D ≤ (C₁ * P) * D := mul_le_mul_of_nonneg_right hnum hDpos.le
            _ = C₁ * (D * P) := by ring
            _ ≤ C₁ * GP := by rw [hGPdef]; exact mul_le_mul_of_nonneg_left hlow hC₁.le
        calc ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / GP := hgp
          _ ≤ C₁ / D := (div_le_div_iff₀ hgppos hDpos).mpr hstep
          _ ≤ max C₀ (C₁ / D) := le_max_right _ _
    · -- `S`-branch, `z₀ = S τ₀`
      have hτ₀S : τ₀ = ModularGroup.S • (imagAxis t₀ ht₀) := by
        rw [hz0, S_smul_S_smul']
      have ht₁ : (0:ℝ) < 1 / t₀ := by positivity
      have hne₁ : (1:ℝ) / t₀ ≠ 1 := by
        intro h
        apply ht₀ne
        field_simp at h
        linarith
      have hτ₀i : τ₀ = imagAxis (1 / t₀) ht₁ := by
        apply UpperHalfPlane.ext
        rw [hτ₀S, coe_S_smul', imagAxis_coe', imagAxis_coe']
        calc -(((t₀ : ℂ) * Complex.I))⁻¹ = -((Complex.I)⁻¹ * ((t₀ : ℝ) : ℂ)⁻¹) := by
              rw [_root_.mul_inv_rev]
          _ = -((-Complex.I) * ((t₀ : ℝ) : ℂ)⁻¹) := by rw [Complex.inv_I]
          _ = Complex.I * ((t₀ : ℝ) : ℂ)⁻¹ := by ring
          _ = ((1 / t₀ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      obtain ⟨ρ₁, C₁, hρ₁, hC₁, hb₁⟩ := one_zero_S_at ℓ d hd (imagAxis t₀ ht₀)
      obtain ⟨ρ₂, c₂, hρ₂, hc₂, hb₂⟩ := exists_j_diag_lower ht₁ hne₁
      obtain ⟨ρ₃, δ₁, hρ₃, hδ₁, hb₃⟩ := exists_DeltaFun_lower τ₀
      obtain ⟨ρ₄, δ₂, hρ₄, hδ₂, hb₄⟩ := exists_DeltaFun_lower (imagAxis t₀ ht₀)
      obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_coin_bound ℓ d hd τ₀ (imagAxis t₀ ht₀)
      set e : ℕ := (if d = 8 then 1 else 2) with he
      set D : ℝ := δ₁ * δ₂ ^ e * c₂ with hDdef
      set ρim : ℝ := min (τ₀.im / 2) ((imagAxis t₀ ht₀ : ℍ).im / 2) with hρim
      have hρimpos : 0 < ρim := by
        rw [hρim]
        refine lt_min (by linarith [τ₀.im_pos]) (by rw [imagAxis_im']; linarith)
      set ρJ : ℝ := min (min ρ₁ ρ₂ * (t₀ / 2) ^ 2) (t₀ / 2) with hρJ
      have hρJpos : 0 < ρJ := lt_min (by positivity) (by linarith)
      have hρJz : ρJ ≤ t₀ / 2 := min_le_right _ _
      have hρJρ : ρJ ≤ min ρ₁ ρ₂ * (t₀ / 2) ^ 2 := min_le_left _ _
      set ρ : ℝ := min (min (min ρ₁ ρ₂) (min (min ρ₃ ρ₄) ρJ)) (min (min 1 (ρ₁ / 2)) ρim)
        with hρdef
      have hρpos : 0 < ρ := by
        rw [hρdef]
        exact lt_min (lt_min (lt_min hρ₁ hρ₂) (lt_min (lt_min hρ₃ hρ₄) hρJpos))
          (lt_min (lt_min one_pos (by linarith)) hρimpos)
      have hρρ₁ : ρ ≤ ρ₁ :=
        le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
      have hρρ₂ : ρ ≤ ρ₂ :=
        le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
      have hρρ₃ : ρ ≤ ρ₃ :=
        le_trans (le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_left _ _))
          (min_le_left _ _)
      have hρρ₄ : ρ ≤ ρ₄ :=
        le_trans (le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_left _ _))
          (min_le_right _ _)
      have hρρJ : ρ ≤ ρJ :=
        le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_right _ _)
      have hρ1 : ρ ≤ 1 := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
      have hρ12 : ρ ≤ ρ₁ / 2 :=
        le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
      have hρρim : ρ ≤ ρim := le_trans (min_le_right _ _) (min_le_right _ _)
      have hρimτ : ρim ≤ τ₀.im / 2 := min_le_left _ _
      have hρimz : ρim ≤ (imagAxis t₀ ht₀ : ℍ).im / 2 := min_le_right _ _
      have hDpos : 0 < D := by rw [hDdef]; positivity
      refine ⟨ρ, max C₀ (C₁ / D), hρpos, le_max_of_le_left hC₀pos.le, fun τ z hτ hz => ?_⟩
      by_cases hJ : jInvariantFun τ = jInvariantFun z
      · have hc := hC₀ τ z (dist_le_one_of_norm_lt (le_trans hρρim hρimτ) hτ)
          (dist_le_one_of_norm_lt (le_trans hρρim hρimz) hz) hJ
        exact le_trans hc (le_max_left _ _)
      · set P : ℝ := ‖(τ : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ with hPdef
        set Jv : ℝ := ‖jInvariantFun τ - jInvariantFun z‖ with hJvdef
        set GP : ℝ := ‖growthPrefactor d τ z‖ with hGPdef
        have hPpos : 0 < P := by
          rw [hPdef]
          refine norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hJ ?_))
          have hzz : τ = ModularGroup.S • z := UpperHalfPlane.ext h
          rw [hzz, KernelFacts.jInvariantFun_S_smul]
        have hmpos : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
        have hSzτbase : ‖((ModularGroup.S • z : ℍ) : ℂ) - (τ₀ : ℂ)‖ < min ρ₁ ρ₂ / 2 := by
          rw [hτ₀S, norm_S_sub_S]
          have hzn : t₀ / 2 ≤ ‖(z : ℂ)‖ := by
            have h1 : ‖(z : ℂ)‖ ≥ ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ -
                ‖(z : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
              have h2 := (abs_le.mp (abs_norm_sub_norm_le (z : ℂ)
                ((imagAxis t₀ ht₀ : ℍ) : ℂ))).1
              linarith
            rw [norm_imagAxis t₀ ht₀] at h1
            linarith [lt_of_lt_of_le hz (le_trans hρρJ hρJz)]
          have hden : t₀ ^ 2 / 2 ≤ ‖(z : ℂ)‖ * ‖((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ := by
            rw [norm_imagAxis t₀ ht₀]
            nlinarith [hzn]
          have hnum : ‖(z : ℂ) - ((imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < min ρ₁ ρ₂ * (t₀ / 2) ^ 2 :=
            lt_of_lt_of_le hz (le_trans hρρJ hρJρ)
          rw [div_lt_iff₀ (lt_of_lt_of_le (by positivity : (0:ℝ) < t₀ ^ 2 / 2) hden)]
          nlinarith [hnum, hden, hmpos]
        have hSzτ : ‖((ModularGroup.S • z : ℍ) : ℂ) - (τ₀ : ℂ)‖ < ρ₂ :=
          lt_of_lt_of_le hSzτbase (by linarith [min_le_right ρ₁ ρ₂])
        have hSzτ₁ : ‖((ModularGroup.S • z : ℍ) : ℂ) - (τ₀ : ℂ)‖ < ρ₁ / 2 :=
          lt_of_lt_of_le hSzτbase (by linarith [min_le_left ρ₁ ρ₂])
        have hτSz : ‖(τ : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ < ρ₁ := by
          have h1 : ‖(τ : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖
              ≤ ‖(τ : ℂ) - (τ₀ : ℂ)‖ + ‖(τ₀ : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ :=
            norm_sub_le_three τ (ModularGroup.S • z) τ₀
          have h2 : ‖(τ₀ : ℂ) - ((ModularGroup.S • z : ℍ) : ℂ)‖ < ρ₁ / 2 := by
            rw [norm_sub_rev]; exact hSzτ₁
          linarith [lt_of_lt_of_le hτ hρ12, h1, h2]
        have hnumK : ‖KfunClear ℓ d τ z‖ ≤ C₁ * P := by
          rw [hPdef]
          exact hb₁ τ z (lt_of_lt_of_le hz hρρ₁) hτSz
        have hJlow : c₂ * P ≤ Jv := by
          rw [hPdef, hJvdef]
          have h := hb₂ (ModularGroup.S • z) τ (by rw [← hτ₀i]; exact hSzτ)
            (by rw [← hτ₀i]; exact lt_of_lt_of_le hτ hρρ₂)
          simpa only [KernelFacts.jInvariantFun_S_smul, norm_sub_rev] using h
        have hΔτ : δ₁ ≤ ‖DeltaFun τ‖ := hb₃ τ (lt_of_lt_of_le hτ hρρ₃)
        have hΔz : δ₂ ≤ ‖DeltaFun z‖ := hb₄ z (lt_of_lt_of_le hz hρρ₄)
        have hnorm : GP = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e *
            ‖jInvariantFun τ - jInvariantFun z‖ := by
          rw [hGPdef]; simpa [he] using norm_growthPrefactor d τ z
        have hlow : D * P ≤ ‖growthPrefactor d τ z‖ := by
          have hBe : δ₂ ^ e ≤ ‖DeltaFun z‖ ^ e := pow_le_pow_left₀ hδ₂.le hΔz e
          have h1 : δ₁ * δ₂ ^ e ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e :=
            mul_le_mul hΔτ hBe (pow_nonneg hδ₂.le e) (norm_nonneg _)
          calc D * P = (δ₁ * δ₂ ^ e) * (c₂ * P) := by rw [hDdef]; ring
            _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e) * Jv :=
                mul_le_mul h1 hJlow (mul_nonneg hc₂.le hPpos.le)
                (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) e))
            _ = GP := by rw [hnorm, hJvdef]
        have hgppos : 0 < GP := by rw [hGPdef]; exact lt_of_lt_of_le (mul_pos hDpos hPpos) hlow
        have hgp : ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / GP := by
          rw [Kfun_eq_KfunClear_div ℓ d hd τ z hJ, norm_div, hGPdef]
        have hstep : ‖KfunClear ℓ d τ z‖ * D ≤ C₁ * GP := by
          calc ‖KfunClear ℓ d τ z‖ * D ≤ (C₁ * P) * D := mul_le_mul_of_nonneg_right hnumK hDpos.le
            _ = C₁ * (D * P) := by ring
            _ ≤ C₁ * GP := by rw [hGPdef]; exact mul_le_mul_of_nonneg_left hlow hC₁.le
        calc ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / GP := hgp
          _ ≤ C₁ / D := (div_le_div_iff₀ hgppos hDpos).mpr hstep
          _ ≤ max C₀ (C₁ / D) := le_max_right _ _

/-! ## 9. From a Euclidean neighbourhood to the hyperbolic one -/

theorem finish (ℓ : LogLambdaData) (d : ℕ) {τ₀ z₀ : ℍ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hz₀ : z₀ = imagAxis t₀ ht₀)
    (key : ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ τ z : ℍ,
      ‖(τ : ℂ) - (τ₀ : ℂ)‖ < ρ → ‖(z : ℂ) - (z₀ : ℂ)‖ < ρ → ‖Kfun ℓ d τ z‖ ≤ C) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ),
      τ ∈ DomainD → 0 < t → dist τ τ₀ < r → |t - t₀| < r →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨ρ, C, hρ, hC, hkey⟩ := key
  have him : 0 < τ₀.im := τ₀.im_pos
  set R : ℝ := min (ρ / 2) (Real.log (1 + ρ / (2 * τ₀.im))) with hR
  have hRpos : 0 < R := by
    rw [hR]
    refine lt_min (by linarith) (Real.log_pos ?_)
    have h1 : 0 < ρ / (2 * τ₀.im) := div_pos hρ (by positivity)
    linarith
  refine ⟨R, hRpos, C, hC, fun τ t hτd ht hdist ht' => ?_⟩
  have hτeu : ‖(τ : ℂ) - (τ₀ : ℂ)‖ < ρ := by
    have h1 := UpperHalfPlane.dist_coe_le τ τ₀
    rw [dist_eq_norm] at h1
    have h2 : Real.exp (dist τ τ₀) ≤ 1 + ρ / (2 * τ₀.im) := by
      have h3 : dist τ τ₀ < Real.log (1 + ρ / (2 * τ₀.im)) :=
        lt_of_lt_of_le hdist (min_le_right _ _)
      calc Real.exp (dist τ τ₀) ≤ Real.exp (Real.log (1 + ρ / (2 * τ₀.im))) :=
            Real.exp_le_exp.mpr h3.le
        _ = 1 + ρ / (2 * τ₀.im) := Real.exp_log (by positivity)
    have h4 : τ₀.im * (Real.exp (dist τ τ₀) - 1) ≤ τ₀.im * (ρ / (2 * τ₀.im)) := by
      have h5 : Real.exp (dist τ τ₀) - 1 ≤ ρ / (2 * τ₀.im) := by linarith
      exact mul_le_mul_of_nonneg_left h5 him.le
    have h6 : τ₀.im * (ρ / (2 * τ₀.im)) = ρ / 2 := by
      field_simp
    rw [h6] at h4
    linarith
  have hzeu : ‖((imagAxis t ht : ℍ) : ℂ) - (z₀ : ℂ)‖ < ρ := by
    rw [hz₀, norm_imagAxis_sub t t₀ ht ht₀]
    exact lt_of_lt_of_le ht' (le_trans (min_le_left _ _) (by linarith))
  have := hkey τ (imagAxis t ht) hτeu hzeu
  simpa only [Kaxis, dif_pos ht] using this

end KL

open KL

theorem Kaxis_local_coincidence (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} (hτ₀ : τ₀ ∈ Work.Asymptotics.DomainD) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hcoin : Work.Kernels.jInvariantFun τ₀ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t₀ ht₀)) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 0 < t → dist τ τ₀ < r → |t - t₀| < r →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨ρ, C, hρ, hC, hkey⟩ := KL.key_bound ℓ d hd hτ₀ ht₀ hcoin
  exact KL.finish ℓ d ht₀ rfl ⟨ρ, C, hρ, hC, hkey⟩

end Work.Asymptotics
