import Mathlib
import Submission.Work.Asymptotics.KaxisMid.Basic
import Submission.Work.Asymptotics.KaxisMid.Classify
import Submission.Work.Asymptotics.KaxisMid.Main
import Submission.Work.Asymptotics.KaxisMid.Coincidence
import Submission.Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_two_zeros
import Submission.Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.KaxisMid.exists_diffQuotient_lower
import Submission.Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence
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
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Rigidity.LambdaBasic

/-!
# The local bound at a coincidence for the CKMRV kernel

This file proves `Work.Asymptotics.KaxisMid.exists_local_bound_coincidence`: the kernel
`K^{(d)}(τ,it)` of CKMRV Theorem 4.9 is bounded on a neighbourhood of a coincidence
`j τ = j (it)` in the parameter space `K × [ε,1]`.

The proof has two halves, both carried out below in full:

* the *generic* case `p.1 ≠ i`: the coincidence lies on one of the two branches `z = τ`, `z = S τ`
  of the coincidence locus (`Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero`), where the cleared kernel
  `Work.Kernels.KfunClear` vanishes (`Work.Asymptotics.KaxisMid.KfunClear_self_eq_zero`,
  `Work.Asymptotics.KaxisMid.KfunClear_smul_S_eq_zero`); the one-zero maximum-modulus bound in the `z`-variable
  combines with the non-vanishing difference quotient of `j` at `i p.2` (`p.2 ≠ 1`,
  `Work.Asymptotics.KaxisMid.exists_diffQuotient_lower`);
* the delicate case `p.1 = i`, where the two branches merge and `j'(i) = 0`: the cleared kernel
  vanishes quadratically, which is the two-zero bound applied in the first variable at `τ = i`
  and in the second variable at `z = i`, and `‖j τ - j z‖` dominates the product of the same two
  distances (`Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I` together with
  `Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz`).

The material of the two auxiliary namespaces below (`KbcAux2`, and `AtIAux` for the case
`p.1 = i`) is the corresponding part of the shared library, reproduced here so that this file is
self-contained up to the stable modules listed in the imports.  Every declaration is proved.
-/

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Metric Filter Complex
open Work.Kernels

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Auxiliary analytic facts on `ℍ` (one-zero bound, bounds for the cleared kernel) -/

namespace Work.Asymptotics.KaxisMid

namespace KbcAux2

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

end KbcAux2

end Work.Asymptotics.KaxisMid

namespace Work.Asymptotics.KaxisMid

namespace AtIAux


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
    KbcAux2.closedBall_subset_upper hr
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
    have h2 := KbcAux2.im_gt_sub_norm (a := z) (b := c) h
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
  obtain ⟨M, hM, hMb⟩ := KbcAux2.exists_bound_KfunClear_of_balls ℓ d hd UpperHalfPlane.I
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
      (KbcAux2.mdifferentiable_KfunClear_fst ℓ d hd z) (c := UpperHalfPlane.I) (r := 1 / 4)
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
      (KbcAux2.mdifferentiable_KfunClear_snd ℓ d hd τ) (c := UpperHalfPlane.I) (r := 1 / 4)
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
combination of `Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I` with
`Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz`. -/
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
`Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence`. -/
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

/-- The delicate case `p.1 = i` of `Work.Asymptotics.KaxisMid.exists_local_bound_coincidence`:
here the two coincidence branches `z = τ` and `z = S τ` of the CKMRV kernel merge and `j'(i) = 0`.
The two-zero bound `Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_two_zeros`, applied in the
*second* variable to `z ↦ KfunClear ℓ d τ z` (whose zeros are `z = τ` and `z = S τ`) when `τ ≠ i`,
and in the *first* variable to `τ ↦ KfunClear ℓ d τ z` (whose zeros are `τ = z` and `τ = S z`) when
`z ≠ i`, gives `‖KfunClear τ z‖ ≤ C ‖τ - z‖ ‖τ - S z‖` on a neighbourhood of `(i,i)`; combined with
`Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I` and
`Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz` (which bound `‖j τ - j z‖` below by the
same product of distances) this yields `‖KfunClear ℓ d τ z‖ ≤ C' ‖j τ - j z‖`, and dividing by the
growth prefactor gives the bound `‖Kfun ℓ d τ z‖ ≤ C' / (δ₁ δ₂^e)` off the coincidence; on the
coincidence itself the value is bounded by
`Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence`. -/
theorem exists_local_bound_at_I (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsub : K ⊆ Work.Asymptotics.DomainD) {ε : ℝ} (hε : 0 < ε)
    (p : UpperHalfPlane × ℝ) (hp : p ∈ Work.Asymptotics.KaxisMid.Pspace K ε)
    (hI : (p.1 : ℂ) = Complex.I)
    (hcoin : Work.Kernels.jInvariantFun p.1
      = Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε p hp)) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ (q : UpperHalfPlane × ℝ)
      (hq : q ∈ Work.Asymptotics.KaxisMid.Pspace K ε),
      ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < r → |q.2 - p.2| < r →
      ‖Work.Kernels.Kfun ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ ≤ C := by
  obtain ⟨ρ, C, hρ, hC, hkey⟩ := key_bound_I ℓ d hd
  have hI' : p.1 = UpperHalfPlane.I := UpperHalfPlane.ext (by rw [hI, UpperHalfPlane.coe_I])
  have hpD : p.1 ∈ DomainD := hsub (mem_Pspace.mp hp).1
  have hzre : ((pz hε p hp : ℍ) : ℂ).re = 0 := by rw [pz_coe hε p hp]; simp
  have hzp : pz hε p hp = UpperHalfPlane.I := by
    rcases eq_or_eq_S_of_re_eq_zero hpD hzre hcoin with h | h
    · rw [h, hI']
    · rw [h, hI', S_smul_I]
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ρ, hρ,
    fun q hq hq1 hq2 => ?_⟩
  have h1 : ‖(q.1 : ℂ) - Complex.I‖ < ρ := by rw [← hI]; exact hq1
  have h2 : ‖((pz hε q hq : ℍ) : ℂ) - Complex.I‖ < ρ := by
    have hnorm : ‖((pz hε q hq : ℍ) : ℂ) - ((pz hε p hp : ℍ) : ℂ)‖ = |q.2 - p.2| := by
      rw [pz_coe hε q hq, pz_coe hε p hp, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [show Complex.I = ((pz hε p hp : ℍ) : ℂ) from by rw [hzp, UpperHalfPlane.coe_I]]
    rw [hnorm]
    exact hq2
  exact le_trans (hkey q.1 (pz hε q hq) h1 h2) (le_max_left _ _)

end AtIAux


/-! ## The generic case `p.1 ≠ i` and the final assembly -/


open Work.Kernels

/-- The Euclidean distance between the attached contour points is the distance of the second
parameters. -/
lemma norm_pz_sub' {K : Set UpperHalfPlane} {ε : ℝ} (hε : 0 < ε) {q q' : UpperHalfPlane × ℝ}
    (hq : q ∈ Work.Asymptotics.KaxisMid.Pspace K ε) (hq' : q' ∈ Work.Asymptotics.KaxisMid.Pspace K ε) :
    ‖((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ)
        - ((Work.Asymptotics.KaxisMid.pz hε q' hq' : UpperHalfPlane) : ℂ)‖ = |q.2 - q'.2| := by
  rw [Work.Asymptotics.KaxisMid.pz_coe hε q hq, Work.Asymptotics.KaxisMid.pz_coe hε q' hq', ← sub_mul,
    ← Complex.ofReal_sub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- **The generic (non-`i`) local bound at a coincidence.**  `Z` is the branch of the coincidence
locus through the parameter point: `Z p.1 = pz hε p hp`, `KfunClear` vanishes along the branch and
`j` is constant along it, and `Z` is Lipschitz at `p.1`.  Off the coincidence the one-zero bound
`Work.Asymptotics.KbcAux2.one_zero_apply` for `z ↦ KfunClear ℓ d τ z` (zero on the branch) combines
with the lower bound for the `j`-difference (`exists_diffQuotient_lower`, applicable because
`p.2 ≠ 1` says that `z₀ = i p.2` is not the elliptic point `i`); on the coincidence the value is
controlled by `exists_bound_Kfun_of_coincidence`. -/
theorem exists_local_bound_branch_aux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {K : Set UpperHalfPlane} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε)
    (p : UpperHalfPlane × ℝ) (hp : p ∈ Work.Asymptotics.KaxisMid.Pspace K ε) (hne : p.2 ≠ 1)
    {Z : UpperHalfPlane → UpperHalfPlane} (hZ : Z p.1 = Work.Asymptotics.KaxisMid.pz hε p hp)
    (hZzero : ∀ τ : UpperHalfPlane, Work.Kernels.KfunClear ℓ d τ (Z τ) = 0)
    (hZj : ∀ τ : UpperHalfPlane,
      Work.Kernels.jInvariantFun (Z τ) = Work.Kernels.jInvariantFun τ)
    (hZlip : ∃ δZ cZ : ℝ, 0 < δZ ∧ 0 < cZ ∧ ∀ τ : UpperHalfPlane,
      ‖(τ : ℂ) - (p.1 : ℂ)‖ < δZ →
      ‖((Z τ : UpperHalfPlane) : ℂ) - ((Z p.1 : UpperHalfPlane) : ℂ)‖
        ≤ cZ * ‖(τ : ℂ) - (p.1 : ℂ)‖) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ (q : UpperHalfPlane × ℝ)
      (hq : q ∈ Work.Asymptotics.KaxisMid.Pspace K ε),
      ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < r → |q.2 - p.2| < r →
      ‖Work.Kernels.Kfun ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ ≤ C := by
  let z₀ : UpperHalfPlane := Work.Asymptotics.KaxisMid.pz hε p hp
  have hz₀pos : 0 < z₀.im := z₀.im_pos
  have hp1pos : 0 < p.1.im := p.1.im_pos
  obtain ⟨M, _hMpos, hMbd⟩ := KbcAux2.exists_bound_KfunClear_of_balls ℓ d hd p.1 z₀
    (R₁ := p.1.im / 2) (R₂ := z₀.im / 2) (by linarith) (by linarith)
  obtain ⟨ρ₀, hρ₀, c₀, hc₀, hlow⟩ :=
    Work.Asymptotics.KaxisMid.exists_diffQuotient_lower hε (Work.Asymptotics.KaxisMid.mem_Pspace.mp hp).2.1
      (Work.Asymptotics.KaxisMid.mem_Pspace.mp hp).2.2 hne
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Work.Asymptotics.KaxisMid.exists_lower_DeltaFun hK
  obtain ⟨δ₂, hδ₂, hδ₂b⟩ := Work.Asymptotics.KaxisMid.exists_lower_DeltaFun_Cseg hε
  obtain ⟨C₀, hC₀pos, hC₀b⟩ :=
    Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence ℓ d hd hK
      (Work.Asymptotics.KaxisMid.isCompact_Cseg hε)
  obtain ⟨δZ, cZ, hδZ, hcZ, hZlipb⟩ := hZlip
  refine ⟨max C₀ ((4 * M / z₀.im) / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2))),
    lt_of_lt_of_le hC₀pos (le_max_left _ _),
    min (min δZ (min (ρ₀ / 2) (z₀.im / 8)))
      (min (min (ρ₀ / (2 * cZ)) (z₀.im / (8 * cZ))) (p.1.im / 2)),
    ?_, fun q hq hq1 hq2 => ?_⟩
  · exact lt_min (lt_min hδZ (lt_min (by linarith) (by positivity)))
      (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  obtain ⟨hqK, hqεle, hqle1⟩ := Work.Asymptotics.KaxisMid.mem_Pspace.mp hq
  have hrδZ : ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < δZ :=
    lt_of_lt_of_le hq1 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hrρ2 : ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < ρ₀ / 2 :=
    lt_of_lt_of_le hq1 (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hrz8 : ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < z₀.im / 8 :=
    lt_of_lt_of_le hq1 (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hrcρ : ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < ρ₀ / (2 * cZ) :=
    lt_of_lt_of_le hq1
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hrc8 : ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < z₀.im / (8 * cZ) :=
    lt_of_lt_of_le hq1
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hrp : ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < p.1.im / 2 :=
    lt_of_lt_of_le hq1 (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the branch point `Z q.1` is close to `z₀`
  have hZclose : ‖((Z q.1 : UpperHalfPlane) : ℂ) - (z₀ : ℂ)‖
      ≤ cZ * ‖(q.1 : ℂ) - (p.1 : ℂ)‖ := by
    have h := hZlipb q.1 hrδZ
    rwa [hZ] at h
  have hZρ : ‖((Z q.1 : UpperHalfPlane) : ℂ) - (z₀ : ℂ)‖ < ρ₀ := by
    have h2 : cZ * ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < ρ₀ / 2 := by
      calc cZ * ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < cZ * (ρ₀ / (2 * cZ)) :=
            mul_lt_mul_of_pos_left hrcρ hcZ
        _ = ρ₀ / 2 := by field_simp
    have h3 := lt_of_le_of_lt hZclose h2
    linarith [hρ₀]
  have hZ4 : ‖((Z q.1 : UpperHalfPlane) : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 / 2 := by
    have h2 : cZ * ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < z₀.im / 8 := by
      calc cZ * ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < cZ * (z₀.im / (8 * cZ)) :=
            mul_lt_mul_of_pos_left hrc8 hcZ
        _ = z₀.im / 8 := by field_simp
    have h3 := lt_of_le_of_lt hZclose h2
    linarith [hz₀pos]
  -- the contour point `z` is close to `z₀`
  have hq2ρ2 : |q.2 - p.2| < ρ₀ / 2 :=
    lt_of_lt_of_le hq2 (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hq2z8 : |q.2 - p.2| < z₀.im / 8 :=
    lt_of_lt_of_le hq2 (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hzdist : ‖((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ) - (z₀ : ℂ)‖
      = |q.2 - p.2| := norm_pz_sub' hε hq hp
  have hzρ : ‖((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ) - (z₀ : ℂ)‖ < ρ₀ := by
    rw [hzdist]; linarith [hρ₀, hq2ρ2]
  have hz4 : ‖((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ) - (z₀ : ℂ)‖
      < z₀.im / 2 / 2 := by
    rw [hzdist]; linarith [hz₀pos, hq2z8]
  -- the one-zero bound in the second variable
  have hbd : ∀ w : UpperHalfPlane, ‖(w : ℂ) - (z₀ : ℂ)‖ ≤ z₀.im / 2 →
      ‖Work.Kernels.KfunClear ℓ d q.1 w‖ ≤ M := fun w hw =>
    hMbd q.1 w (le_of_lt hrp) hw
  have hone := KbcAux2.one_zero_apply (f := fun w : UpperHalfPlane => Work.Kernels.KfunClear ℓ d q.1 w)
    (KbcAux2.mdifferentiable_KfunClear_snd ℓ d hd q.1) (c := z₀) (r := z₀.im / 2) (M := M)
    (by linarith) (by linarith) hbd (w₀ := Z q.1) hZ4 (hZzero q.1)
  have hnum : ‖Work.Kernels.KfunClear ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖
      ≤ (4 * M / z₀.im) * ‖((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ)
          - ((Z q.1 : UpperHalfPlane) : ℂ)‖ := by
    have h := hone (Work.Asymptotics.KaxisMid.pz hε q hq) hz4
    have h2 : 2 * M / (z₀.im / 2) = 4 * M / z₀.im := by
      have hne : z₀.im ≠ 0 := ne_of_gt hz₀pos
      field_simp
      norm_num
    rwa [h2] at h
  -- the lower bound for the `j`-difference
  have hjlow : c₀ * ‖((Z q.1 : UpperHalfPlane) : ℂ)
      - ((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ)‖
      ≤ ‖Work.Kernels.jInvariantFun q.1
          - Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε q hq)‖ := by
    have h := hlow (Z q.1) (Work.Asymptotics.KaxisMid.pz hε q hq) hZρ hzρ
    rwa [hZj q.1] at h
  by_cases hJ : Work.Kernels.jInvariantFun q.1
      = Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε q hq)
  · refine le_trans (hC₀b q.1 (Work.Asymptotics.KaxisMid.pz hε q hq) hqK
      (Work.Asymptotics.KaxisMid.pz_mem_Cseg hε q hq) hJ) (le_max_left _ _)
  · have hJpos : 0 < ‖Work.Kernels.jInvariantFun q.1
        - Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε q hq)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hJ)
    have hden : (δ₁ * δ₂ ^ (if d = 8 then 1 else 2))
        * ‖Work.Kernels.jInvariantFun q.1
            - Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε q hq)‖
        ≤ ‖Work.Kernels.growthPrefactor d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ := by
      rw [Work.Asymptotics.KaxisMid.norm_growthPrefactor]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact mul_le_mul (hδ₁b q.1 hqK)
        (pow_le_pow_left₀ hδ₂.le
          (hδ₂b (Work.Asymptotics.KaxisMid.pz hε q hq) (Work.Asymptotics.KaxisMid.pz_mem_Cseg hε q hq)) _)
        (pow_nonneg hδ₂.le _) (norm_nonneg _)
    have hgppos : 0 < ‖Work.Kernels.growthPrefactor d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ :=
      lt_of_lt_of_le (mul_pos (mul_pos hδ₁ (pow_pos hδ₂ _)) hJpos) hden
    have hKfun_eq : ‖Work.Kernels.Kfun ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖
        = ‖Work.Kernels.KfunClear ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖
          / ‖Work.Kernels.growthPrefactor d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ := by
      have hgpne : Work.Kernels.growthPrefactor d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq) ≠ 0 :=
        Work.Asymptotics.growthPrefactor_ne_zero d hJ
      have h' : Work.Kernels.Kfun ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)
          = Work.Kernels.KfunClear ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)
            / Work.Kernels.growthPrefactor d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq) := by
        rw [eq_div_iff hgpne, mul_comm]
        exact (Work.Asymptotics.KfunClear_eq_growthPrefactor_mul ℓ d hd hJ).symm
      rw [h', norm_div]
    have hone' : ‖Work.Kernels.KfunClear ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖
        ≤ (4 * M / z₀.im / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2)))
          * ‖Work.Kernels.growthPrefactor d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ := by
      have h1 : ‖((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ)
            - ((Z q.1 : UpperHalfPlane) : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun q.1
              - Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε q hq)‖ / c₀ := by
        rw [le_div_iff₀ hc₀, norm_sub_rev, mul_comm]
        exact hjlow
      calc ‖Work.Kernels.KfunClear ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖
          ≤ (4 * M / z₀.im) * ‖((Work.Asymptotics.KaxisMid.pz hε q hq : UpperHalfPlane) : ℂ)
              - ((Z q.1 : UpperHalfPlane) : ℂ)‖ := hnum
        _ ≤ (4 * M / z₀.im) * (‖Work.Kernels.jInvariantFun q.1
              - Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε q hq)‖ / c₀) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (4 * M / z₀.im / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2)))
              * ((δ₁ * δ₂ ^ (if d = 8 then 1 else 2))
                * ‖Work.Kernels.jInvariantFun q.1
                    - Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε q hq)‖) := by
            field_simp
        _ ≤ (4 * M / z₀.im / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2)))
              * ‖Work.Kernels.growthPrefactor d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    rw [hKfun_eq]
    refine le_trans ((div_le_iff₀ hgppos).mpr hone') (le_max_right _ _)

/-- **The local bound at a coincidence.**  Let `K ⊆ 𝒟` be compact, `ε > 0`, and let
`p = (τ₀,t₀) ∈ K × [ε,1]` with `j τ₀ = j (i t₀)`.  Then the kernel `K^{(d)}(τ,it)` of CKMRV
Theorem 4.9 is bounded by a constant on a neighbourhood of `p` in the parameter space — the
pole of `z ↦ K(τ,z)` at the coincidence is removable (`Work.Residues.KPlusClear_diag`,
`Work.Asymptotics.KClear_S_vanishing`), so the cleared kernel divided by the divisor
`Δ(τ)Δ(z)^e (j τ - j z)` stays bounded there.  In particular the delicate case `p = (i,1)`,
where the two coincidence branches `z = τ` and `z = S τ` merge and `j'(i) = 0`, must (and can)
be handled by `Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_two_zeros` together with
`Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I` and
`Work.Asymptotics.KaxisMid.exists_lambdaFun_lipschitz`; the branch
`τ₀ ≠ i` is handled by `Work.Asymptotics.KaxisMid.exists_diffQuotient_lower` together with
the one-zero bound `Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_zero`
(in `Submission.Work.Asymptotics.KaxisMid.Coincidence`). -/
theorem exists_local_bound_coincidence (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsub : K ⊆ Work.Asymptotics.DomainD) {ε : ℝ} (hε : 0 < ε)
    (p : UpperHalfPlane × ℝ) (hp : p ∈ Work.Asymptotics.KaxisMid.Pspace K ε)
    (hcoin : Work.Kernels.jInvariantFun p.1
      = Work.Kernels.jInvariantFun (Work.Asymptotics.KaxisMid.pz hε p hp)) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ (q : UpperHalfPlane × ℝ)
      (hq : q ∈ Work.Asymptotics.KaxisMid.Pspace K ε),
      ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < r → |q.2 - p.2| < r →
      ‖Work.Kernels.Kfun ℓ d q.1 (Work.Asymptotics.KaxisMid.pz hε q hq)‖ ≤ C := by
  by_cases hI : (p.1 : ℂ) = Complex.I
  · -- the elliptic point `i`
    exact AtIAux.exists_local_bound_at_I ℓ d hd hK hsub hε p hp hI hcoin
  · -- `p.1 ≠ i`: the coincidence lies on one of the two branches `z = τ`, `z = S τ`
    have hre : ((Work.Asymptotics.KaxisMid.pz hε p hp : UpperHalfPlane) : ℂ).re = 0 := by
      rw [Work.Asymptotics.KaxisMid.pz_coe]; simp
    have ht_ne : p.2 ≠ 1 := by
      intro h1
      have hzI : Work.Asymptotics.KaxisMid.pz hε p hp = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext
        rw [Work.Asymptotics.KaxisMid.pz_coe, h1, UpperHalfPlane.coe_I]
        norm_num
      rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero (hsub (Work.Asymptotics.KaxisMid.mem_Pspace.mp hp).1)
          hre hcoin with h | h
      · exact hI (by rw [← h, hzI, UpperHalfPlane.coe_I])
      · have h2 : ModularGroup.S • p.1 = UpperHalfPlane.I := by rw [← h]; exact hzI
        have h3 : p.1 = UpperHalfPlane.I := by
          have h4 := congrArg (fun w : UpperHalfPlane => ModularGroup.S • w) h2
          rwa [S_smul_S_smul, AtIAux.S_smul_I] at h4
        exact hI (by rw [h3, UpperHalfPlane.coe_I])
    rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero (hsub (Work.Asymptotics.KaxisMid.mem_Pspace.mp hp).1)
        hre hcoin with h | h
    · -- the diagonal branch `z = τ`
      refine exists_local_bound_branch_aux ℓ d hd hK hε p hp ht_ne (Z := id) h.symm ?_ ?_ ?_
      · intro τ; exact Work.Asymptotics.KaxisMid.KfunClear_self_eq_zero ℓ d hd τ
      · intro τ; rfl
      · exact ⟨1, 1, one_pos, one_pos, fun τ _ => le_of_eq (one_mul _).symm⟩
    · -- the `S`-branch `z = S τ`
      refine exists_local_bound_branch_aux ℓ d hd hK hε p hp ht_ne
        (Z := fun τ : UpperHalfPlane => ModularGroup.S • τ) h.symm ?_ ?_ ?_
      · intro τ; exact Work.Asymptotics.KaxisMid.KfunClear_smul_S_eq_zero ℓ d hd τ
      · intro τ; exact Work.Kernels.KernelFacts.jInvariantFun_S_smul τ
      · have hN : 0 < ‖(p.1 : ℂ)‖ := norm_pos_iff.mpr (UpperHalfPlane.ne_zero p.1)
        refine ⟨‖(p.1 : ℂ)‖ / 2, 2 / ‖(p.1 : ℂ)‖ ^ 2, by positivity,
          div_pos two_pos (pow_pos hN 2), fun τ hτ => ?_⟩
        have hτN : ‖(p.1 : ℂ)‖ / 2 < ‖(τ : ℂ)‖ := by
          have h1 := norm_sub_norm_le (p.1 : ℂ) (τ : ℂ)
          rw [norm_sub_rev] at h1
          linarith
        rw [KbcAux2.norm_S_sub_S]
        have hle : 1 / (‖(τ : ℂ)‖ * ‖(p.1 : ℂ)‖) ≤ 2 / ‖(p.1 : ℂ)‖ ^ 2 := by
          rw [div_le_div_iff₀
            (mul_pos (norm_pos_iff.mpr (UpperHalfPlane.ne_zero τ)) hN) (pow_pos hN 2)]
          nlinarith [hτN, hN, norm_nonneg (τ : ℂ)]
        calc ‖(τ : ℂ) - (p.1 : ℂ)‖ / (‖(τ : ℂ)‖ * ‖(p.1 : ℂ)‖)
            = ‖(τ : ℂ) - (p.1 : ℂ)‖ * (1 / (‖(τ : ℂ)‖ * ‖(p.1 : ℂ)‖)) := by ring
          _ ≤ ‖(τ : ℂ) - (p.1 : ℂ)‖ * (2 / ‖(p.1 : ℂ)‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hle (norm_nonneg _)
          _ = 2 / ‖(p.1 : ℂ)‖ ^ 2 * ‖(τ : ℂ) - (p.1 : ℂ)‖ := by ring
end Work.Asymptotics.KaxisMid
