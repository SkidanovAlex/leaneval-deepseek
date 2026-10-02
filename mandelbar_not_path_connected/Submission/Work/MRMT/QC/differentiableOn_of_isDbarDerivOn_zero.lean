/-
Copyright: Work.MRMT (mandelbar) subproject.

# Weyl's lemma in complex form: a continuous function with vanishing weak `∂̄` is holomorphic

This file proves `Work.MRMT.QC.differentiableOn_of_isDbarDerivOn_zero`: if `f : ℂ → ℂ` is
continuous on an open set `U` and its weak (distributional) `∂̄`-derivative on `U` vanishes,
then `f` is complex differentiable on `U`.

The proof is the classical mollification argument.  For a smooth mollifier `f₀` supported in a
small ball, the convolution

  `F z = ∫ t, f₀ t • fl (z - t)`

is smooth (`HasCompactSupport.hasFDerivAt_convolution_left`), and its weak `∂̄` equals the
convolution of the weak `∂̄` of `fl` with `f₀`; testing the defining distributional equation
against the reflected mollifier `u ↦ f₀ (x - u)` shows `∂̄ F x = 0` (this uses the chain rule
`dzbar_comp_sub` and the measure preserving substitution `t ↦ x - t`).  As `F` is smooth, the
Cauchy–Riemann equation `differentiableAt_complex_iff_differentiableAt_real` then makes `F`
holomorphic.  Finally `F` tends to `f` locally uniformly as the support of the mollifier shrinks
(`ContDiffBump.dist_normed_convolution_le`), so Weierstrass' theorem
(`TendstoLocallyUniformlyOn.differentiableOn`) gives the result.
-/
import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution ContDiff

namespace Work.MRMT.QC

/-! ## Elementary calculus lemmas about `dzbar` -/

/-- The `ℝ`-bilinear map `(r, z) ↦ r • z` from `ℝ × ℂ` to `ℂ`. -/
def lsmulRC : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ

@[simp] theorem lsmulRC_apply (r : ℝ) (z : ℂ) : lsmulRC r z = r • z := rfl

/-- `dzbar` of a real-valued function, coerced to `ℂ`. -/
theorem dzbar_ofReal_comp (φ : ℂ → ℝ) (z : ℂ) (h : DifferentiableAt ℝ φ z) :
    Work.MRMT.dzbar (fun w => (φ w : ℂ)) z
      = ((fderiv ℝ φ z 1 : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2 := by
  have h1 : fderiv ℝ (fun w => (φ w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ φ z) := by
    have h2 : HasFDerivAt (fun w => (φ w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z h.hasFDerivAt
    exact h2.fderiv
  rw [Work.MRMT.dzbar, h1]
  simp

/-- Chain rule for `dzbar` under the reflection `y ↦ c - y`. -/
theorem dzbar_comp_sub (g : ℂ → ℂ) (c y : ℂ) (hg : DifferentiableAt ℝ g (c - y)) :
    Work.MRMT.dzbar (fun y => g (c - y)) y = - Work.MRMT.dzbar g (c - y) := by
  have hd : DifferentiableAt ℝ (fun y : ℂ => c - y) y := by fun_prop
  have h1 : HasFDerivAt (fun y : ℂ => g (c - y))
      ((fderiv ℝ g (c - y)).comp (fderiv ℝ (fun y : ℂ => c - y) y)) y :=
    hg.hasFDerivAt.comp y hd.hasFDerivAt
  have h2 : fderiv ℝ (fun y : ℂ => c - y) y = -1 := by
    rw [fderiv_const_sub]
    rw [show (fun y : ℂ => y) = id from rfl]
    rw [fderiv_id]
    rfl
  rw [Work.MRMT.dzbar, Work.MRMT.dzbar, h1.fderiv, h2]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg, one_apply_eq_self]
  ring

/-- The map `t ↦ c - t` preserves Lebesgue measure on `ℂ`. -/
theorem integral_comp_sub_const' (g : ℂ → ℂ) (x : ℂ) (hg : Continuous g) :
    ∫ t, g (x - t) = ∫ u, g u := by
  conv_rhs => rw [← Measure.measurePreserving_sub_left (volume : Measure ℂ) x |>.map_eq]
  rw [MeasureTheory.integral_map]
  · exact (continuous_const.sub continuous_id).aemeasurable
  · exact hg.measurable.aestronglyMeasurable

/-- Substitution `t ↦ x - t` in a convolution integral. -/
theorem integral_mul_comp_sub_const (H : ℂ → ℂ) (hH : Continuous H) (g : ℂ → ℂ)
    (hg : Continuous g) (x : ℂ) :
    ∫ t, H t * g (x - t) = ∫ u, H (x - u) * g u := by
  have h := integral_comp_sub_const' (fun t : ℂ => H (x - t) * g t) x
    ((hH.comp (continuous_const.sub continuous_id)).mul hg)
  simpa only [sub_sub_cancel] using h

/-- `dzbar` of a continuously differentiable function is continuous. -/
theorem continuous_dzbar {g : ℂ → ℂ} (hg : Continuous (fderiv ℝ g)) :
    Continuous (Work.MRMT.dzbar g) := by
  have h1 : Continuous (fun z => (fderiv ℝ g z) (1 : ℂ)) := hg.clm_apply continuous_const
  have h2 : Continuous (fun z => (fderiv ℝ g z) Complex.I) := hg.clm_apply continuous_const
  have h3 : Work.MRMT.dzbar g
      = fun z => ((fderiv ℝ g z) 1 + Complex.I * (fderiv ℝ g z) Complex.I) / 2 := rfl
  rw [h3]
  exact (h1.add (continuous_const.mul h2)).div_const 2

/-- The Fréchet derivative of `φ` viewed as a complex-valued function. -/
theorem continuous_fderiv_ofReal_comp {φ : ℂ → ℝ} (h : ContDiff ℝ 1 φ) :
    Continuous (fderiv ℝ (fun w : ℂ => (φ w : ℂ))) := by
  have hd : ∀ z, fderiv ℝ (fun w : ℂ => (φ w : ℂ)) z
      = (ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM (fderiv ℝ φ z) := by
    intro z
    have h2 : HasFDerivAt (fun w : ℂ => (φ w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (((h.differentiable (by simp)).differentiableAt).hasFDerivAt)
    rw [h2.fderiv]
    rfl
  rw [show fderiv ℝ (fun w : ℂ => (φ w : ℂ))
      = fun z => (ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM (fderiv ℝ φ z)
      from funext hd]
  exact (((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).continuous.comp
    (h.continuous_fderiv (by simp)))

/-! ## Integrability of mollification integrands -/

/-- Integrability of `t ↦ A t • B (x - t)` for `B` continuous with compact support. -/
theorem integrable_smul_comp_sub {A : ℂ → ℝ} (hA : Continuous A) {B : ℂ → ℂ}
    (hB : Continuous B) (hBc : HasCompactSupport B) (x : ℂ) :
    Integrable (fun t => A t • B (x - t)) volume := by
  refine Continuous.integrable_of_hasCompactSupport (μ := volume)
    (hA.smul (hB.comp (continuous_const.sub continuous_id))) ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := (fun t : ℂ => x - t) '' tsupport B) ?_ ?_
  · exact hBc.isCompact.image (continuous_const.sub continuous_id)
  · intro t ht
    rw [Function.mem_support] at ht
    exact ⟨x - t, subset_tsupport B (fun hz => ht (by simp [hz])), by simp⟩

/-- Integrability of `t ↦ A t (B (x - t))` for `A` continuous operator-valued and `B`
continuous with compact support. -/
theorem integrable_clm_apply_comp_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ℂ → (ℂ →L[ℝ] F)} (hA : Continuous A) {B : ℂ → ℂ}
    (hB : Continuous B) (hBc : HasCompactSupport B) (x : ℂ) :
    Integrable (fun t => A t (B (x - t))) volume := by
  refine Continuous.integrable_of_hasCompactSupport (μ := volume)
    (hA.clm_apply (hB.comp (continuous_const.sub continuous_id))) ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := (fun t : ℂ => x - t) '' tsupport B) ?_ ?_
  · exact hBc.isCompact.image (continuous_const.sub continuous_id)
  · intro t ht
    rw [Function.mem_support] at ht
    exact ⟨x - t, subset_tsupport B (fun hz => ht (by simp [hz])), by simp⟩

/-! ## `∂̄ = 0` on a smooth function implies complex differentiability -/

/-- A real-differentiable function whose `dzbar` vanishes is complex differentiable. -/
theorem differentiableAt_of_dzbar_eq_zero {g : ℂ → ℂ} {x : ℂ} (hd : DifferentiableAt ℝ g x)
    (hz : Work.MRMT.dzbar g x = 0) : DifferentiableAt ℂ g x := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hd, ?_⟩
  have h2 : (fderiv ℝ g x) 1 + Complex.I * (fderiv ℝ g x) Complex.I = 0 := by
    have h := hz
    rw [Work.MRMT.dzbar, div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · norm_num at h
  have h6 : Complex.I * (Complex.I * (fderiv ℝ g x) Complex.I) = -(fderiv ℝ g x) Complex.I := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  have key := congrArg (fun w : ℂ => Complex.I * w) h2
  rw [mul_add, mul_zero, h6] at key
  rw [smul_eq_mul]
  have key' : Complex.I * (fderiv ℝ g x) 1 - (fderiv ℝ g x) Complex.I = 0 := by
    rw [sub_eq_add_neg]; exact key
  exact (sub_eq_zero.mp key').symm

/-! ## Localisation: multiplying by a bump function -/

/-- If `χ` is continuous with `tsupport χ ⊆ U` and `f` is continuous on the open set `U`, then
`z ↦ χ z • f z` is continuous on all of `ℂ`. -/
theorem continuous_smul_of_tsupport_subset {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) {χ : ℂ → ℝ} (hχc : Continuous χ) (hχ : tsupport χ ⊆ U) :
    Continuous (fun z => (χ z : ℂ) * f z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · have hfz : ContinuousAt f z := hf.continuousAt (hU.mem_nhds (hχ hz))
    exact ((Complex.continuous_ofReal.continuousAt.comp hχc.continuousAt)).mul hfz
  · have hev : (fun w : ℂ => (χ w : ℂ) * f w) =ᶠ[𝓝 z] 0 := by
      have ho : (tsupport χ)ᶜ ∈ 𝓝 z := (isClosed_tsupport χ).isOpen_compl.mem_nhds hz
      filter_upwards [ho] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw]
      simp
    exact continuousAt_const.congr hev.symm

/-- `z ↦ χ z • f z` has compact support whenever `χ` does. -/
theorem hasCompactSupport_smul_of_tsupport_subset {f : ℂ → ℂ} {χ : ℂ → ℝ}
    (hχs : HasCompactSupport χ) : HasCompactSupport (fun z => (χ z : ℂ) * f z) := by
  refine HasCompactSupport.of_support_subset_isCompact hχs.isCompact ?_
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hc
  exact hz (by rw [image_eq_zero_of_notMem_tsupport hc]; simp)

/-! ## The mollified function -/

/-- The mollification `z ↦ ∫ t, f₀ t • f₁ (z - t)` of `f₁` by a smooth compactly supported
kernel `f₀` is real differentiable, with derivative given by the convolution of `fderiv ℝ f₀`
with `f₁`. -/
theorem hasFDerivAt_mollify {f₁ : ℂ → ℂ} (h₁c : Continuous f₁)
    {f₀ : ℂ → ℝ} (hf₀ : ContDiff ℝ ∞ f₀) (hcf₀ : HasCompactSupport f₀) (x : ℂ) :
    HasFDerivAt (fun z => ∫ t, f₀ t • f₁ (z - t))
      ((fderiv ℝ f₀ ⋆[ContinuousLinearMap.precompL ℂ lsmulRC, (volume : Measure ℂ)] f₁) x) x := by
  have h := hcf₀.hasFDerivAt_convolution_left lsmulRC (hf₀.of_le (by norm_num))
    (h₁c.locallyIntegrable (μ := volume)) x
  have h2 : (fun z => ∫ t, f₀ t • f₁ (z - t))
      = (f₀ ⋆[lsmulRC, (volume : Measure ℂ)] f₁) := by
    funext z
    simp only [lsmulRC]
    rw [MeasureTheory.convolution_lsmul]
  rw [h2]; exact h

/-- **The heart of Weyl's lemma.**  If the weak `∂̄`-derivative of `f` on the open set `U`
vanishes, then the mollification of `f₁` (which agrees with `f` near `x`) by a smooth kernel
`f₀` supported in the ball of radius `R` around `0` has vanishing `∂̄` at `x`, provided the ball
of radius `R` around `x` lies in `U`. -/
theorem dzbar_convolution_eq_zero
    {f₁ f : ℂ → ℂ} {U : Set ℂ} (h₁c : Continuous f₁) (h₁s : HasCompactSupport f₁)
    (h : IsDbarDerivOn f (fun _ => 0) U)
    {f₀ : ℂ → ℝ} (hf₀ : ContDiff ℝ ∞ f₀) (hcf₀ : HasCompactSupport f₀)
    {R : ℝ} (hR : Function.support f₀ ⊆ Metric.closedBall (0 : ℂ) R)
    {x : ℂ} (hsub : ∀ u ∈ Metric.closedBall (0 : ℂ) R, x - u ∈ U)
    (hag : ∀ u ∈ Metric.closedBall (0 : ℂ) R, f₁ (x - u) = f (x - u)) :
    Work.MRMT.dzbar (fun z => ∫ t, f₀ t • f₁ (z - t)) x = 0 := by
  have h1f₀ : ContDiff ℝ 1 f₀ := hf₀.of_le (by norm_num)
  have hFd := hasFDerivAt_mollify h₁c hf₀ hcf₀ x
  have hKint : Integrable (fun t : ℂ =>
      (ContinuousLinearMap.precompL ℂ lsmulRC (fderiv ℝ f₀ t)) (f₁ (x - t))) volume :=
    integrable_clm_apply_comp_sub (F := ℂ →L[ℝ] ℂ) (B := f₁)
      (A := fun t : ℂ => (ContinuousLinearMap.precompL ℂ lsmulRC) (fderiv ℝ f₀ t))
      ((ContinuousLinearMap.precompL ℂ lsmulRC).continuous.comp (h1f₀.continuous_fderiv (by simp)))
      h₁c h₁s x
  have hD1 : ((fderiv ℝ f₀ ⋆[ContinuousLinearMap.precompL ℂ lsmulRC, (volume : Measure ℂ)] f₁) x) 1
      = ∫ t, ((fderiv ℝ f₀ t) 1) • f₁ (x - t) := by
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hKint]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.precompL_apply, lsmulRC_apply]
  have hDI : ((fderiv ℝ f₀ ⋆[ContinuousLinearMap.precompL ℂ lsmulRC, (volume : Measure ℂ)] f₁) x) Complex.I
      = ∫ t, ((fderiv ℝ f₀ t) Complex.I) • f₁ (x - t) := by
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hKint]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.precompL_apply, lsmulRC_apply]
  have hA1int : Integrable (fun t : ℂ => ((fderiv ℝ f₀ t) 1) • f₁ (x - t)) volume :=
    integrable_smul_comp_sub (A := fun t : ℂ => (fderiv ℝ f₀ t) 1)
      ((h1f₀.continuous_fderiv (by simp)).clm_apply continuous_const) h₁c h₁s x
  have hA2int : Integrable (fun t : ℂ => ((fderiv ℝ f₀ t) Complex.I) • f₁ (x - t)) volume :=
    integrable_smul_comp_sub (A := fun t : ℂ => (fderiv ℝ f₀ t) Complex.I)
      ((h1f₀.continuous_fderiv (by simp)).clm_apply continuous_const) h₁c h₁s x
  have hdz : Work.MRMT.dzbar (fun z => ∫ t, f₀ t • f₁ (z - t)) x
      = ∫ t, (Work.MRMT.dzbar (fun w => (f₀ w : ℂ)) t) * f₁ (x - t) := by
    rw [Work.MRMT.dzbar, hFd.fderiv, hD1, hDI]
    rw [← integral_const_mul, ← integral_add hA1int (hA2int.const_mul _)]
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [dzbar_ofReal_comp f₀ t ((hf₀.differentiable (by simp)).differentiableAt)]
    simp only [Complex.real_smul]
    ring
  have hψsub : tsupport (fun u : ℂ => (f₀ (x - u) : ℂ))
      ⊆ {u : ℂ | x - u ∈ Metric.closedBall (0 : ℂ) R} := by
    refine closure_minimal ?_
      (Metric.isClosed_closedBall.preimage (continuous_const.sub continuous_id))
    intro u hu
    rw [Function.mem_support] at hu
    exact hR (fun hz => hu (by simp [hz]))
  have hψcd : ContDiff ℝ ∞ (fun u : ℂ => (f₀ (x - u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf₀.comp (by fun_prop))
  have hψcs : HasCompactSupport (fun u : ℂ => (f₀ (x - u) : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun u : ℂ => x - u) '' tsupport f₀) ?_ ?_
    · exact hcf₀.isCompact.image (continuous_const.sub continuous_id)
    · intro u hu
      rw [Function.mem_support] at hu
      exact ⟨x - u, subset_tsupport f₀ (fun hz => hu (by simp [hz])), by simp⟩
  have hψts : tsupport (fun u : ℂ => (f₀ (x - u) : ℂ)) ⊆ U := by
    intro u hu
    have h4 := hsub (x - u) (hψsub hu)
    rwa [sub_sub_cancel] at h4
  set ψ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ :=
    (⟨fun u : ℂ => (f₀ (x - u) : ℂ), hψcd, hψcs, fun _ _ => trivial⟩ :
      TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤) with hψdef
  have hψcoe : (ψ : ℂ → ℂ) = fun u : ℂ => (f₀ (x - u) : ℂ) := rfl
  have hweak : ∫ z, f z * Work.MRMT.dzbar (ψ : ℂ → ℂ) z = 0 := by
    have hw := (h.2.2 ψ (by rw [hψcoe]; exact hψts)).2.2
    simpa using hw
  rw [hdz]
  rw [integral_mul_comp_sub_const (Work.MRMT.dzbar (fun w : ℂ => (f₀ w : ℂ)))
    (continuous_dzbar (g := fun w : ℂ => (f₀ w : ℂ))
      (continuous_fderiv_ofReal_comp h1f₀)) f₁ h₁c x]
  have hchain : ∫ u, Work.MRMT.dzbar (fun w => (f₀ w : ℂ)) (x - u) * f₁ u
      = - ∫ u, f₁ u * Work.MRMT.dzbar (ψ : ℂ → ℂ) u := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall (fun u => ?_))
    dsimp only
    have hcr : Work.MRMT.dzbar (fun y : ℂ => (f₀ (x - y) : ℂ)) u
        = - Work.MRMT.dzbar (fun w : ℂ => (f₀ w : ℂ)) (x - u) :=
      dzbar_comp_sub (fun w : ℂ => (f₀ w : ℂ)) x u
        (Complex.ofRealCLM.differentiableAt.comp _
          ((hf₀.differentiable (by simp)).differentiableAt))
    simp only [hψcoe, hcr]
    ring
  rw [hchain]
  have hpoint : ∀ u : ℂ, f₁ u * Work.MRMT.dzbar (ψ : ℂ → ℂ) u
      = f u * Work.MRMT.dzbar (ψ : ℂ → ℂ) u := by
    intro u
    by_cases hH : Work.MRMT.dzbar (ψ : ℂ → ℂ) u = 0
    · simp [hH]
    · have hu : u ∈ tsupport (ψ : ℂ → ℂ) := by
        by_contra hcon
        have hev : (ψ : ℂ → ℂ) =ᶠ[𝓝 u] 0 := by
          filter_upwards [(isClosed_tsupport (ψ : ℂ → ℂ)).isOpen_compl.mem_nhds hcon] with w hw
          exact image_eq_zero_of_notMem_tsupport hw
        have hd : fderiv ℝ (ψ : ℂ → ℂ) u = 0 := by rw [hev.fderiv_eq]; simp
        exact hH (by rw [Work.MRMT.dzbar, hd]; simp)
      have h4 : x - u ∈ Metric.closedBall (0 : ℂ) R := by
        rw [hψcoe] at hu
        exact hψsub hu
      have h5 : f₁ u = f u := by
        have := hag (x - u) h4
        rwa [sub_sub_cancel] at this
      rw [h5]
  rw [integral_congr_ae (Eventually.of_forall hpoint), hweak, neg_zero]

/-! ## The main theorem -/

/-- An element `u` of the ball of radius `r` around `0` shifted by `z`. -/
theorem sub_mem_closedBall_sub {z u : ℂ} {r : ℝ} (h : u ∈ Metric.closedBall (0 : ℂ) r) :
    z - u ∈ Metric.closedBall z r := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [show (z - u) - z = -u by ring, norm_neg]
  exact h

/-- **Weyl's lemma, complex form.**  A continuous function on an open set whose weak
`∂̄`-derivative vanishes is holomorphic there. -/
theorem differentiableOn_of_isDbarDerivOn_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) (h : IsDbarDerivOn f (fun _ => 0) U) :
    DifferentiableOn ℂ f U := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  -- a bump around `x₀`, equal to `1` near `x₀` and supported well inside `U`
  let χ : ContDiffBump x₀ := ⟨ε / 2, 3 * ε / 4, by linarith, by linarith⟩
  have hχrOut : χ.rOut = 3 * ε / 4 := rfl
  have hχrIn : χ.rIn = ε / 2 := rfl
  have hχts : tsupport (χ : ℂ → ℝ) ⊆ U := by
    rw [ContDiffBump.tsupport_eq, hχrOut]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hεU
  -- the localised function
  let fl : ℂ → ℂ := fun z => (χ z : ℂ) * f z
  have hflc : Continuous fl := continuous_smul_of_tsupport_subset hU hf χ.continuous hχts
  have hfls : HasCompactSupport fl := hasCompactSupport_smul_of_tsupport_subset χ.hasCompactSupport
  have hfle : ∀ z ∈ Metric.closedBall x₀ χ.rIn, fl z = f z := by
    intro z hz
    show (χ z : ℂ) * f z = f z
    rw [ContDiffBump.one_of_mem_closedBall χ hz, Complex.ofReal_one, one_mul]
  -- the mollifiers
  let D : ℕ → ℝ := fun n => ε / (16 * ((n : ℝ) + 1))
  have hDpos : ∀ n, 0 < D n := fun n => by
    show 0 < ε / (16 * ((n : ℝ) + 1))
    positivity
  have hDle : ∀ n, D n ≤ ε / 16 := fun n => by
    show ε / (16 * ((n : ℝ) + 1)) ≤ ε / 16
    rw [div_le_div_iff_of_pos_left hε (by positivity) (by norm_num)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨D n / 2, D n, by have := hDpos n; linarith, by have := hDpos n; linarith⟩
  have hφrOut : ∀ n, (φ n).rOut = D n := fun n => rfl
  let F : ℕ → ℂ → ℂ := fun n z => ∫ t, (φ n).normed volume t • fl (z - t)
  -- each `F n` is holomorphic on a small ball around `x₀`
  have hFdiff : ∀ n, DifferentiableOn ℂ (F n) (Metric.ball x₀ (ε / 8)) := by
    intro n z hz
    have hzu : ∀ u ∈ Metric.closedBall (0 : ℂ) (φ n).rOut,
        z - u ∈ Metric.closedBall x₀ (ε / 2) := by
      intro u hu
      have h1 : dist (z - u) z ≤ (φ n).rOut := Metric.mem_closedBall.mp (sub_mem_closedBall_sub hu)
      have h4 : (φ n).rOut ≤ ε / 16 := by rw [hφrOut n]; exact hDle n
      have h3 : dist z x₀ < ε / 8 := Metric.mem_ball.mp hz
      rw [Metric.mem_closedBall]
      linarith [dist_triangle (z - u) z x₀]
    have hsub : ∀ u ∈ Metric.closedBall (0 : ℂ) (φ n).rOut, z - u ∈ U := by
      intro u hu
      exact (Metric.closedBall_subset_ball (by linarith)).trans hεU (hzu u hu)
    have hag : ∀ u ∈ Metric.closedBall (0 : ℂ) (φ n).rOut, fl (z - u) = f (z - u) :=
      fun u hu => hfle (z - u) (hzu u hu)
    have hdz : Work.MRMT.dzbar (F n) z = 0 := by
      refine dzbar_convolution_eq_zero hflc hfls h
        (f₀ := (φ n).normed volume) ((φ n).contDiff_normed (n := ⊤))
        ((φ n).hasCompactSupport.mono (by
          rw [ContDiffBump.support_normed_eq (f := φ n) (μ := volume),
            ContDiffBump.support_eq])) ?_ hsub hag
      rw [ContDiffBump.support_normed_eq (f := φ n) (μ := volume)]
      exact Metric.ball_subset_closedBall
    have hfd := hasFDerivAt_mollify hflc ((φ n).contDiff_normed (n := ⊤))
      ((φ n).hasCompactSupport.mono (by
        rw [ContDiffBump.support_normed_eq (f := φ n) (μ := volume),
          ContDiffBump.support_eq])) z
    exact (differentiableAt_of_dzbar_eq_zero hfd.differentiableAt hdz).differentiableWithinAt
  -- the `F n` converge to `f` locally uniformly
  have hconv : TendstoLocallyUniformlyOn F f atTop (Metric.ball x₀ (ε / 8)) := by
    have hunif : TendstoUniformlyOn F fl atTop Set.univ := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε' hε'
      obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp
        (hflc.uniformContinuous_of_tendsto_cocompact hfls.is_zero_at_infty)
        (ε' / 2) (by linarith)
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ε / (16 * δ) ≤ (N : ℝ) := exists_nat_ge _
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hDr : D n ≤ δ := by
        show ε / (16 * ((n : ℝ) + 1)) ≤ δ
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * ((n : ℝ) + 1))]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * δ)] at hN
        nlinarith [hN, hnR]
      refine fun x _ => ?_
      have hbd : ∀ y ∈ Metric.ball x (φ n).rOut, dist (fl y) (fl x) ≤ ε' / 2 := by
        intro y hy
        rw [Metric.mem_ball] at hy
        exact le_of_lt (hδ (lt_of_lt_of_le hy (by rw [hφrOut]; exact hDr)))
      have hb := ContDiffBump.dist_normed_convolution_le (φ := φ n) (μ := volume) (g := fl)
        (x₀ := x) (ε := ε' / 2) hflc.aestronglyMeasurable hbd
      have hb' : dist (F n x) (fl x) ≤ ε' / 2 := hb
      rw [dist_comm]
      linarith [hb']
    have h1 : TendstoUniformlyOn F fl atTop (Metric.ball x₀ (ε / 8)) :=
      hunif.mono (Set.subset_univ _)
    have h2 : TendstoUniformlyOn F f atTop (Metric.ball x₀ (ε / 8)) :=
      h1.congr_right (fun z hz => hfle z (by
        rw [hχrIn]
        exact Metric.closedBall_subset_closedBall (by linarith)
          (Metric.ball_subset_closedBall hz)))
    exact h2.tendstoLocallyUniformlyOn
  have hlim : DifferentiableOn ℂ f (Metric.ball x₀ (ε / 8)) :=
    hconv.differentiableOn (Eventually.of_forall hFdiff) Metric.isOpen_ball
  exact (hlim.differentiableAt (Metric.ball_mem_nhds x₀ (by linarith))).differentiableWithinAt

end Work.MRMT.QC
