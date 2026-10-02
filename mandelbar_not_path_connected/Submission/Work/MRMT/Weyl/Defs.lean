/-
Support material for Weyl's lemma (`Work.MRMT.Weyl.weyl_lemma_continuous`).

* `Work.MRMT.Weyl.moll`   — mollification of a function `ℂ → ℂ` against a real-valued kernel;
* `isDbarDeriv_dzbar`     — for a smooth function, the distributional `∂̄` agrees with the pointwise
  Wirtinger derivative (integration by parts in the two real directions);
* `differentiableAt_of_dzbar_eq_zero` — a real-differentiable function with vanishing `∂̄` is complex
  differentiable (Cauchy–Riemann);
* `hasCompactSupport_dzbar_testFunction` — `∂̄` of a test function still has compact support;
* `bump`, `tendsto_rOut_bump` — a sequence of bump functions at `0` whose outer radii tend to `0`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

noncomputable section

open Work.MRMT

/-- Mollification of `f : ℂ → ℂ` against a real valued kernel `ρ : ℂ → ℝ`, realised as the
convolution `ρ ⋆[lsmul ℝ ℝ] f`. -/
def moll (ρ : ℂ → ℝ) (f : ℂ → ℂ) : ℂ → ℂ :=
  MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) (volume : MeasureTheory.Measure ℂ)

theorem moll_apply (ρ : ℂ → ℝ) (f : ℂ → ℂ) (x : ℂ) :
    moll ρ f x = ∫ y, (ρ y : ℂ) * f (x - y) := by
  simp only [moll, MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
    RCLike.real_smul_eq_coe_mul]
  rfl

/-- Mollification preserves smoothness: the convolution of a locally integrable function with a
smooth compactly supported kernel is smooth. -/
theorem contDiff_moll {ρ : ℂ → ℝ} {f : ℂ → ℂ} {N : ℕ∞} (hρ : ContDiff ℝ N ρ)
    (hρcs : HasCompactSupport ρ) (hf : LocallyIntegrable f volume) :
    ContDiff ℝ N (moll ρ f) := by
  have h := hρcs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := N) hρ hf
  simpa only [moll] using h

/-- For a smooth function `u : ℂ → ℂ` (no support hypothesis is needed, since test functions are
compactly supported), the distributional `∂̄`-derivative of `u` is the pointwise Wirtinger
derivative `dzbar u`.

This is integration by parts in the two real directions `1` and `I`, using
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. -/
theorem continuous_dzbar_of_contDiff {u : ℂ → ℂ} {n : WithTop ℕ∞} (hu : ContDiff ℝ n u)
    (hn : n ≠ 0) : Continuous (dzbar u) := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv hn
  unfold dzbar
  exact ((hd.clm_apply continuous_const).add
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

theorem isDbarDeriv_dzbar {u : ℂ → ℂ} {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) (hn : n ≠ 0) :
    IsDbarDeriv u (dzbar u) := by
  have hdzu_cont : Continuous (dzbar u) := continuous_dzbar_of_contDiff hu hn
  refine ⟨hu.continuous.locallyIntegrable, hdzu_cont.locallyIntegrable, ?_⟩
  intro ψ
  set ψf : ℂ → ℂ := (ψ : ℂ → ℂ) with hψf
  have hψ_cont : Continuous ψf := by rw [hψf]; exact ψ.continuous
  have hψ_cs : HasCompactSupport ψf := by rw [hψf]; exact ψ.hasCompactSupport
  have hfψ_cont : Continuous (fun z => fderiv ℝ ψf z) := by
    rw [hψf]; exact ψ.contDiff.continuous_fderiv (by simp)
  have hfψ_diff : ∀ z, DifferentiableAt ℝ ψf z := by
    intro z; rw [hψf]; exact (ψ.contDiff.differentiable (by simp)).differentiableAt
  have hfψ_deriv_cs : HasCompactSupport (fun z => fderiv ℝ ψf z) := hψ_cs.fderiv ℝ
  have hfu_cont : Continuous (fun z => fderiv ℝ u z) := hu.continuous_fderiv hn
  have hfu_diff : ∀ z, DifferentiableAt ℝ u z := fun z => (hu.differentiable hn).differentiableAt
  have heval_cs (v : ℂ) : HasCompactSupport (fun z => fderiv ℝ ψf z v) :=
    hfψ_deriv_cs.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) (by simp)
  have hint_uψ : Integrable (fun z => u z * ψf z) :=
    Continuous.integrable_of_hasCompactSupport (hu.continuous.mul hψ_cont) hψ_cs.mul_left
  have hint_duψ (v : ℂ) : Integrable (fun z => fderiv ℝ u z v * ψf z) :=
    Continuous.integrable_of_hasCompactSupport
      ((hfu_cont.clm_apply continuous_const).mul hψ_cont) hψ_cs.mul_left
  have hint_udψ (v : ℂ) : Integrable (fun z => u z * fderiv ℝ ψf z v) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous.mul (hfψ_cont.clm_apply continuous_const)) (heval_cs v).mul_left
  have hIBP (v : ℂ) :
      ∫ z, u z * fderiv ℝ ψf z v = - ∫ z, fderiv ℝ u z v * ψf z :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure ℂ))
      (hint_duψ v) (hint_udψ v) (hint_uψ) (fun z _ => hfu_diff z) (fun z _ => hfψ_diff z)
  have hptL : (fun z => u z * dzbar ψf z) =
      (fun z => (u z * fderiv ℝ ψf z 1 + Complex.I * (u z * fderiv ℝ ψf z Complex.I)) *
        (2 : ℂ)⁻¹) := by
    funext z; simp only [dzbar]; ring
  have hptR : (fun z => dzbar u z * ψf z) =
      (fun z => (fderiv ℝ u z 1 * ψf z + Complex.I * (fderiv ℝ u z Complex.I * ψf z)) *
        (2 : ℂ)⁻¹) := by
    funext z; simp only [dzbar]; ring
  have hint1 : Integrable (fun z => u z * dzbar ψf z) := by
    rw [hptL]
    exact ((hint_udψ 1).add ((hint_udψ Complex.I).const_mul Complex.I)).mul_const _
  have hint2 : Integrable (fun z => dzbar u z * ψf z) := by
    rw [hptR]
    exact ((hint_duψ 1).add ((hint_duψ Complex.I).const_mul Complex.I)).mul_const _
  refine ⟨hint1, hint2, ?_⟩
  have hL : ∫ z, u z * dzbar ψf z =
      ((∫ z, u z * fderiv ℝ ψf z 1) + Complex.I * ∫ z, u z * fderiv ℝ ψf z Complex.I) *
        (2 : ℂ)⁻¹ := by
    rw [hptL, integral_mul_const,
      integral_add (hint_udψ 1) ((hint_udψ Complex.I).const_mul Complex.I), integral_const_mul]
  have hR : ∫ z, dzbar u z * ψf z =
      ((∫ z, fderiv ℝ u z 1 * ψf z) + Complex.I * ∫ z, fderiv ℝ u z Complex.I * ψf z) *
        (2 : ℂ)⁻¹ := by
    rw [hptR, integral_mul_const,
      integral_add (hint_duψ 1) ((hint_duψ Complex.I).const_mul Complex.I), integral_const_mul]
  rw [hL, hR, hIBP 1, hIBP Complex.I]
  ring

/-- A real-differentiable function with vanishing Wirtinger derivative `∂̄` is complex
differentiable (the Cauchy–Riemann equation). -/
theorem differentiableAt_of_dzbar_eq_zero {u : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ u z)
    (h : dzbar u z = 0) : DifferentiableAt ℂ u z := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hd, ?_⟩
  have hL : fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I = 0 := by
    have h2 := h; simp only [dzbar] at h2
    exact (div_eq_zero_iff.mp h2).resolve_right (by norm_num)
  have hI : Complex.I * fderiv ℝ u z Complex.I = - fderiv ℝ u z 1 := by
    linear_combination hL
  have h1 : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have h2 : (-Complex.I) * (Complex.I * fderiv ℝ u z Complex.I) = fderiv ℝ u z Complex.I := by
    rw [← mul_assoc, h1, one_mul]
  have hmain : fderiv ℝ u z Complex.I = Complex.I * fderiv ℝ u z 1 := by
    nth_rewrite 1 [← h2]
    rw [hI]; ring
  simpa using hmain

/-- The Wirtinger derivative `∂̄ψ` of a test function has compact support. -/
theorem hasCompactSupport_dzbar_testFunction (ψ : 𝓓(⊤, ℂ)) :
    HasCompactSupport (dzbar (ψ : ℂ → ℂ)) := by
  have hF : HasCompactSupport (fun z => fderiv ℝ (ψ : ℂ → ℂ) z) :=
    ψ.hasCompactSupport.fderiv ℝ
  have h := hF.comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (L 1 + Complex.I * L Complex.I) * (2 : ℂ)⁻¹) (by simp)
  have key : ((fun L : ℂ →L[ℝ] ℂ => (L 1 + Complex.I * L Complex.I) * (2 : ℂ)⁻¹) ∘
      fun z => fderiv ℝ (ψ : ℂ → ℂ) z) = dzbar (ψ : ℂ → ℂ) := by
    funext z; simp only [Function.comp_apply, dzbar, div_eq_mul_inv]
  rwa [key] at h

/-- A sequence of bump functions at `0 : ℂ` whose outer radii tend to `0`. -/
def bump (n : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1),
    by positivity,
    one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩

theorem tendsto_rOut_bump : Tendsto (fun n : ℕ => (bump n).rOut) atTop (𝓝 0) := by
  simp only [bump]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Uniform convergence on compact subsets of the bump-mollifications of a continuous function. -/
theorem tendstoUniformlyOn_moll {f : ℂ → ℂ} (hf : Continuous f) {U : Set ℂ} (hU : IsOpen U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n : ℕ => (φ n).rOut) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => moll ((φ n).normed volume) f) f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKc : IsCompact (Metric.cthickening δ K) := hK.cthickening
  have huc : UniformContinuousOn f (Metric.cthickening δ K) :=
    hKc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hη'⟩ := huc (ε / 2) (half_pos hε)
  have hmin : 0 < min η δ := lt_min hη hδ
  filter_upwards [hφ.eventually (eventually_lt_nhds hmin)] with n hn
  intro x hx
  have hx' : x ∈ Metric.cthickening δ K := Metric.self_subset_cthickening K hx
  have hclose : ∀ y ∈ Metric.ball x (φ n).rOut, dist (f y) (f x) ≤ ε / 2 := by
    intro y hy
    have hyr : dist y x < (φ n).rOut := hy
    have hyδ : dist y x < δ :=
      hyr.trans_le (le_of_lt (lt_of_lt_of_le hn (min_le_right η δ)))
    have hyη : dist y x < η :=
      hyr.trans_le (le_of_lt (lt_of_lt_of_le hn (min_le_left η δ)))
    have hy' : y ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le y x δ K hx hyδ.le
    exact (hη' y hy' x hx' hyη).le
  have h := ContDiffBump.dist_normed_convolution_le
    (μ := (volume : MeasureTheory.Measure ℂ)) (φ := φ n) (x₀ := x) (ε := ε / 2)
    hf.aestronglyMeasurable hclose
  have h2 : dist (f x) (moll ((φ n).normed volume) f x) ≤ ε / 2 := by
    simpa only [moll, dist_comm] using h
  linarith

/-- Mollification of a continuous function by a family of bumps with `rOut → 0` converges locally
uniformly to the function. -/
theorem tendstoLocallyUniformlyOn_moll {f : ℂ → ℂ} (hf : Continuous f)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n : ℕ => (φ n).rOut) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun n => moll ((φ n).normed volume) f) f atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K hK hKc
  exact tendstoUniformlyOn_moll hf isOpen_univ hKc (Set.subset_univ K) φ hφ

end

end Work.MRMT.Weyl
