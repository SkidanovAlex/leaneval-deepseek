/-
Weyl's lemma, global form: a continuous function whose weak `∂̄`-derivative vanishes
is complex differentiable everywhere.

The proof mollifies `f` against a sequence of bump functions whose outer radii tend to `0`.
Each mollification `moll ρ f` is smooth and has vanishing `∂̄`-derivative; hence it is
holomorphic.  A locally uniform limit of holomorphic functions is holomorphic (Weierstrass),
and the mollifications converge locally uniformly to `f` because `f` is continuous.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

set_option maxHeartbeats 1000000

noncomputable section

open Work.MRMT

/-- The Wirtinger derivative `∂̄` of the complex-valued version of a real-valued function,
in terms of the real Fréchet derivative of the original function. -/
lemma dzbar_ofReal (ρ : ℂ → ℝ) (t : ℂ) :
    dzbar (fun z => (ρ z : ℂ)) t =
      (((fderiv ℝ ρ t 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ ρ t Complex.I : ℝ) : ℂ)) / 2 := by
  have key : fderiv ℝ (fun z : ℂ => (ρ z : ℂ)) t = Complex.ofRealCLM.comp (fderiv ℝ ρ t) := by
    by_cases hd : DifferentiableAt ℝ ρ t
    · have h : HasFDerivAt (fun z : ℂ => (ρ z : ℂ))
          (Complex.ofRealCLM.comp (fderiv ℝ ρ t)) t := by
        simpa [Function.comp_def] using
          (ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM).comp t hd.hasFDerivAt
      exact h.fderiv
    · have hd' : ¬ DifferentiableAt ℝ (fun z : ℂ => (ρ z : ℂ)) t := fun hh =>
        hd (by simpa [Function.comp_def] using Complex.reCLM.differentiableAt.comp t hh)
      rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']
      simp
  rw [dzbar, key]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- Chain rule for `∂̄` under the reflection `s ↦ x - s` (an anti-holomorphic isometry). -/
lemma dzbar_comp_sub {g : ℂ → ℂ} {x t : ℂ} (hg : DifferentiableAt ℝ g (x - t)) :
    dzbar (fun s => g (x - s)) t = - dzbar g (x - t) := by
  have hf : DifferentiableAt ℝ (fun s : ℂ => x - s) t := by
    simpa using (differentiableAt_id (𝕜 := ℝ) (x := t)).const_sub x
  have hderiv : fderiv ℝ (fun s : ℂ => x - s) t = -(ContinuousLinearMap.id ℝ ℂ) := by
    have h : HasFDerivAt (fun s : ℂ => x - s) (-(ContinuousLinearMap.id ℝ ℂ)) t := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) t).const_sub x
    exact h.fderiv
  have hcomp : fderiv ℝ (fun s : ℂ => g (x - s)) t
      = (fderiv ℝ g (x - t)).comp (fderiv ℝ (fun s : ℂ => x - s) t) := by
    have h := fderiv_comp (𝕜 := ℝ) (x := t) (f := fun s : ℂ => x - s) (g := g) hg hf
    simpa only [ContinuousLinearMap.compSL_apply, Function.comp_def]
  rw [dzbar, dzbar, hcomp, hderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]
  ring

/-- If `IsDbarDeriv f 0` and `Φ` is smooth with compact support, then
`∫ t, ∂̄Φ(t) * f (x - t) = 0` for every `x`: the reflected kernel `s ↦ Φ (x - s)` is a test
function, and `∂̄` of a reflection is the negative of the reflection of `∂̄`. -/
lemma integral_dzbar_mul_eq_zero {Φ f : ℂ → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦcs : HasCompactSupport Φ) (h : IsDbarDeriv f (fun _ => 0)) (x : ℂ) :
    ∫ t, (dzbar Φ t) * f (x - t) = 0 := by
  have hdΦ : ∀ t : ℂ, DifferentiableAt ℝ Φ (x - t) := fun t =>
    (hΦ.differentiable (by simp)).differentiableAt
  have hsub : ∫ t, (dzbar Φ t) * f (x - t) = ∫ t, (dzbar Φ (x - t)) * f t := by
    have h' := integral_sub_left_eq_self (fun u : ℂ => (dzbar Φ (x - u)) * f u) volume x
    simpa [sub_sub_self] using h'
  have hRefcs : HasCompactSupport (fun s : ℂ => Φ (x - s)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun s : ℂ => x - s) ⁻¹' tsupport Φ) ?_ ?_
    · exact (Homeomorph.subLeft x).isCompact_preimage.mpr hΦcs
    · intro s hs
      exact subset_tsupport Φ (by simpa using hs)
  have hRefcd : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℂ => Φ (x - s)) :=
    hΦ.comp (contDiff_const.sub contDiff_id)
  let ψ : 𝓓(⊤, ℂ) :=
    { toFun := fun s => Φ (x - s)
      contDiff' := hRefcd
      hasCompactSupport' := hRefcs
      tsupport_subset' := fun _ _ => trivial }
  have hcoe : (ψ : ℂ → ℂ) = fun s => Φ (x - s) := rfl
  have htest : ∫ z, f z * dzbar (fun s : ℂ => Φ (x - s)) z = 0 := by
    have h0 : ∫ z, f z * dzbar (ψ : ℂ → ℂ) z = 0 := by
      have h1 := (h.2.2 ψ).2.2
      simpa using h1
    rwa [hcoe] at h0
  have hchain : ∀ t : ℂ, dzbar (fun s : ℂ => Φ (x - s)) t = - dzbar Φ (x - t) :=
    fun t => dzbar_comp_sub (hdΦ t)
  calc ∫ t, (dzbar Φ t) * f (x - t)
      = ∫ t, (dzbar Φ (x - t)) * f t := hsub
    _ = -∫ t, (dzbar (fun s : ℂ => Φ (x - s)) t) * f t := by
        rw [← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show dzbar Φ (x - t) * f t = -(dzbar (fun s : ℂ => Φ (x - s)) t * f t)
        rw [hchain t]; ring
    _ = -∫ t, f t * (dzbar (fun s : ℂ => Φ (x - s)) t) := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
    _ = 0 := by rw [htest, neg_zero]

/-- The `∂̄`-derivative of a mollification `moll ρ f` is the integral of the kernel derivative
against `f`: `∂̄(ρ ⋆ f)(x) = ∫ t, ∂̄ρ(t) * f (x - t)`. -/
lemma dzbar_moll {ρ : ℂ → ℝ} {f : ℂ → ℂ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρcs : HasCompactSupport ρ) (hf : Continuous f) (x : ℂ) :
    dzbar (moll ρ f) x = ∫ t, (dzbar (fun z => (ρ z : ℂ)) t) * f (x - t) := by
  have hli : LocallyIntegrable f volume := hf.locallyIntegrable
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hD : HasFDerivAt (moll ρ f)
      (((fderiv ℝ ρ) ⋆[ContinuousLinearMap.precompL ℂ
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ), volume] f) x) x := by
    have h := hρcs.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) hρ1 hli x
    simpa only [moll] using h
  set F : ℂ → (ℂ →L[ℝ] ℂ) := fun t =>
    (ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
      (fderiv ℝ ρ t) (f (x - t)) with hFdef
  have hFeq : ((fderiv ℝ ρ) ⋆[ContinuousLinearMap.precompL ℂ
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ), volume] f) x
      = ∫ t, F t := by
    rw [hFdef]
    rfl
  have hFcont : Continuous F := by
    have h1 : Continuous fun t : ℂ =>
        (ContinuousLinearMap.precompL ℂ
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) (fderiv ℝ ρ t) :=
      continuous_const.clm_apply (hρ.continuous_fderiv (by simp))
    have h2 : Continuous fun t : ℂ => f (x - t) :=
      hf.comp (continuous_const.sub continuous_id)
    exact h1.clm_apply h2
  have hFcs : HasCompactSupport F := by
    refine (hρcs.fderiv ℝ).mono ?_
    intro t ht
    by_contra h0
    rw [Function.mem_support, not_not] at h0
    exact ht (by simp [hFdef, h0])
  have hFint : Integrable F volume := hFcont.integrable_of_hasCompactSupport hFcs
  have e1 : (fderiv ℝ (moll ρ f) x) 1 = ∫ t, ((fderiv ℝ ρ t) 1) * f (x - t) := by
    rw [hD.fderiv, hFeq, ContinuousLinearMap.integral_apply hFint]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hFdef, ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
      RCLike.real_smul_eq_coe_mul]
    rfl
  have e2 : (fderiv ℝ (moll ρ f) x) Complex.I
      = ∫ t, ((fderiv ℝ ρ t) Complex.I) * f (x - t) := by
    rw [hD.fderiv, hFeq, ContinuousLinearMap.integral_apply hFint]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hFdef, ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
      RCLike.real_smul_eq_coe_mul]
    rfl
  have hA1cs : HasCompactSupport (fun t : ℂ => (((fderiv ℝ ρ t) 1 : ℝ) : ℂ)) :=
    (hρcs.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℝ => ((T 1 : ℝ) : ℂ)) (by simp)
  have hA2cs : HasCompactSupport (fun t : ℂ => (((fderiv ℝ ρ t) Complex.I : ℝ) : ℂ)) :=
    (hρcs.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℝ => ((T Complex.I : ℝ) : ℂ)) (by simp)
  have hA1cont : Continuous (fun t : ℂ => (((fderiv ℝ ρ t) 1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp
      ((hρ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hA2cont : Continuous (fun t : ℂ => (((fderiv ℝ ρ t) Complex.I : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp
      ((hρ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hfshift : Continuous fun t : ℂ => f (x - t) :=
    hf.comp (continuous_const.sub continuous_id)
  have hI1 : Integrable (fun t : ℂ => ((fderiv ℝ ρ t) 1) * f (x - t)) :=
    (hA1cont.mul hfshift).integrable_of_hasCompactSupport hA1cs.mul_right
  have hI2 : Integrable (fun t : ℂ => ((fderiv ℝ ρ t) Complex.I) * f (x - t)) :=
    (hA2cont.mul hfshift).integrable_of_hasCompactSupport hA2cs.mul_right
  have hI2' : Integrable (fun t : ℂ => Complex.I * (((fderiv ℝ ρ t) Complex.I) * f (x - t))) :=
    hI2.const_mul Complex.I
  have hpt : ∀ t : ℂ, ((fderiv ℝ ρ t) 1) * f (x - t)
        + Complex.I * (((fderiv ℝ ρ t) Complex.I) * f (x - t))
      = 2 * ((dzbar (fun z => (ρ z : ℂ)) t) * f (x - t)) := by
    intro t
    rw [dzbar_ofReal]
    ring
  have key : (∫ t, ((fderiv ℝ ρ t) 1) * f (x - t))
        + Complex.I * ∫ t, ((fderiv ℝ ρ t) Complex.I) * f (x - t)
      = 2 * ∫ t, (dzbar (fun z => (ρ z : ℂ)) t) * f (x - t) := by
    rw [← integral_const_mul Complex.I (fun t => ((fderiv ℝ ρ t) Complex.I) * f (x - t)),
      ← integral_add hI1 hI2', integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  rw [dzbar, e1, e2, key]
  ring

/-- The `∂̄`-derivative of a mollification of a weakly holomorphic continuous function
vanishes everywhere. -/
lemma dzbar_moll_eq_zero {ρ : ℂ → ℝ} {f : ℂ → ℂ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρcs : HasCompactSupport ρ) (hf : Continuous f) (h : IsDbarDeriv f (fun _ => 0)) (x : ℂ) :
    dzbar (moll ρ f) x = 0 := by
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (ρ z : ℂ)) :=
    (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp hρ
  have hΦcs : HasCompactSupport (fun z : ℂ => (ρ z : ℂ)) :=
    hρcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  rw [dzbar_moll hρ hρcs hf x]
  exact integral_dzbar_mul_eq_zero hΦcd hΦcs h x

/-- **Weyl's lemma**: a continuous function with vanishing weak `∂̄`-derivative is entire. -/
theorem differentiable_of_isDbarDeriv {f : ℂ → ℂ} (hf : Continuous f)
    (h : IsDbarDeriv f (fun _ => 0)) : Differentiable ℂ f := by
  have hli : LocallyIntegrable f volume := h.1
  have hdiff : ∀ n : ℕ, Differentiable ℂ (moll ((bump n).normed volume) f) := by
    intro n
    have hρ : ContDiff ℝ (⊤ : ℕ∞) ((bump n).normed volume) :=
      (bump n).contDiff_normed (μ := volume) (n := ⊤)
    have hρcs : HasCompactSupport ((bump n).normed volume) := (bump n).hasCompactSupport_normed
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (moll ((bump n).normed volume) f) :=
      contDiff_moll hρ hρcs hli
    intro x
    refine differentiableAt_of_dzbar_eq_zero ((hcd.differentiable (by simp)).differentiableAt)
      (dzbar_moll_eq_zero hρ hρcs hf h x)
  have hconv : TendstoLocallyUniformlyOn
      (fun n : ℕ => moll ((bump n).normed volume) f) f atTop Set.univ :=
    tendstoLocallyUniformlyOn_moll hf bump tendsto_rOut_bump
  have hdOn : DifferentiableOn ℂ f Set.univ :=
    hconv.differentiableOn (Eventually.of_forall fun n => (hdiff n).differentiableOn) isOpen_univ
  rwa [differentiableOn_univ] at hdOn

end

end Work.MRMT.Weyl
