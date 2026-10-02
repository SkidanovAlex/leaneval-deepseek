import Mathlib
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Weyl

noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

set_option maxHeartbeats 4000000

/-- The continuous `ℝ`-linear functional `A ↦ (A 1 + i·A i)/2` on `ℂ →L[ℝ] ℂ`, i.e. the map
sending an `ℝ`-linear endomorphism of `ℂ` to its Wirtinger `∂̄`-value.  Bundling it as a
continuous linear map lets us commute it with Bochner integrals. -/
noncomputable def dzbarCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2:ℝ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (1:ℂ) +
    (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

theorem dzbarCLM_apply (A : ℂ →L[ℝ] ℂ) : dzbarCLM A = (A 1 + Complex.I * A Complex.I)/2 := by
  simp only [dzbarCLM, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply', Complex.real_smul]
  push_cast
  ring

/-- The Wirtinger `∂̄` of the reflection `t ↦ ρ (z - t)` of a real-valued function `ρ`:
the chain rule for `t ↦ z - t` (which is complex linear with derivative `-1`). -/
theorem dzbar_reflect {ρ : ℂ → ℝ} (hρ : Differentiable ℝ ρ) (z t : ℂ) :
    Work.MRMT.dzbar (fun s => (ρ (z - s) : ℂ)) t =
      - ((((fderiv ℝ ρ (z - t) 1 : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ ρ (z - t) Complex.I : ℝ) : ℂ)) / 2) := by
  have hσ : HasFDerivAt (fun s : ℂ => z - s) (-1 : ℂ →L[ℝ] ℂ) t :=
    (hasFDerivAt_id t).const_sub z
  have hin : HasFDerivAt (fun s : ℂ => ρ (z - s))
      ((fderiv ℝ ρ (z - t)).comp (-1 : ℂ →L[ℝ] ℂ)) t :=
    ((hρ.differentiableAt (x := z - t)).hasFDerivAt).comp t hσ
  have hF : HasFDerivAt (fun s : ℂ => (ρ (z - s) : ℂ))
      ((Complex.ofRealCLM).comp ((fderiv ℝ ρ (z - t)).comp (-1 : ℂ →L[ℝ] ℂ))) t :=
    (Complex.ofRealCLM.hasFDerivAt (x := ρ (z - t))).comp t hin
  rw [Work.MRMT.dzbar, hF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, neg_apply,
    one_apply_eq_self, map_neg]
  ring

/-- The weak `∂̄`-derivative relation is insensitive to changing the representing function on
the nose: if `g` and `g'` agree pointwise then `IsDbarDeriv f g` implies `IsDbarDeriv f g'`. -/
theorem isDbarDeriv_congr {f g g' : ℂ → ℂ} (h : Work.MRMT.IsDbarDeriv f g)
    (hgg' : ∀ z, g z = g' z) : Work.MRMT.IsDbarDeriv f g' := by
  refine ⟨h.1, h.2.1.congr (Filter.Eventually.of_forall (fun z => hgg' z)), ?_⟩
  intro φ
  obtain ⟨h1, h2, h3⟩ := h.2.2 φ
  refine ⟨h1, h2.congr (Filter.Eventually.of_forall (fun z => ?_)), ?_⟩
  · show g z * (φ : ℂ → ℂ) z = g' z * (φ : ℂ → ℂ) z
    rw [hgg' z]
  · rw [h3]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      show g z * (φ : ℂ → ℂ) z = g' z * (φ : ℂ → ℂ) z
      rw [hgg' z])

/-- If `f` satisfies the weak Cauchy--Riemann equation `∂̄ f = 0` in the distributional sense
(`IsDbarDeriv f 0`), then so does its mollification against any smooth compactly supported real
kernel `ρ`. Proof by Fubini: for a test function `ψ`,
`∫ (ρ ⋆ f)(z) ∂̄ψ(z) dz = ∫ ρ(y) (∫ f(w) ∂̄(ψ(· + y))(w) dw) dy = 0`,
using that `w ↦ ψ(w + y)` is again a test function and that `∂̄` commutes with translations.
(Note `ContDiff ℝ (⊤ : ℕ∞)` is `C^∞`, the level produced by `ContDiffBump.contDiff_normed`.) -/
theorem isDbarDeriv_moll_contDiff {f : ℂ → ℂ} (hf : Work.MRMT.IsDbarDeriv f (fun _ => 0))
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ) :
    Work.MRMT.IsDbarDeriv (Work.MRMT.Weyl.moll ρ f) (fun _ => 0) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hloc : LocallyIntegrable f volume := hf.1
  have hmoll_smooth : ContDiff ℝ (⊤ : ℕ∞) (Work.MRMT.Weyl.moll ρ f) :=
    Work.MRMT.Weyl.contDiff_moll hρ hρcs hloc
  -- the mollification is smooth and has vanishing Wirtinger derivative
  have hzero : ∀ z, Work.MRMT.dzbar (Work.MRMT.Weyl.moll ρ f) z = 0 := by
    intro z
    -- identify the convolution with the one for which the derivative w.r.t. the smooth
    -- factor `ρ` is available
    have hmoll : Work.MRMT.Weyl.moll ρ f =
        f ⋆[((ContinuousLinearMap.lsmul ℝ ℝ).flip), volume] ρ := by
      rw [Work.MRMT.Weyl.moll]
      exact (MeasureTheory.convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)).symm
    have hh := hρcs.hasFDerivAt_convolution_right
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip) hloc hρ1 z
    have hcont_drho : Continuous (fderiv ℝ ρ) := hρ1.continuous_fderiv (by norm_num)
    have hint := (hρcs.fderiv ℝ).convolutionExists_right
        ((ContinuousLinearMap.lsmul ℝ ℝ).flip.precompR ℂ) hloc hcont_drho z
    -- the test function `t ↦ ρ (z - t)`
    let TF : 𝓓(⊤, ℂ) := ⟨fun t => (ρ (z - t) : ℂ),
      (Complex.ofRealCLM).contDiff.comp (hρ.comp (by fun_prop)),
      (hρcs.comp_homeomorph (Homeomorph.subLeft z)).comp_left
        (g := Complex.ofRealCLM) (by simp),
      by intro t _; trivial⟩
    have hTF : (TF : ℂ → ℂ) = fun t => (ρ (z - t) : ℂ) := rfl
    have hTF_deriv : ∀ t, Work.MRMT.dzbar (TF : ℂ → ℂ) t =
        - ((((fderiv ℝ ρ (z - t) 1 : ℝ) : ℂ) +
          Complex.I * ((fderiv ℝ ρ (z - t) Complex.I : ℝ) : ℂ)) / 2) := by
      intro t
      rw [hTF]
      exact Work.MRMT.Weyl.dzbar_reflect (hρ.differentiable (by simp)) z t
    -- the weak Cauchy--Riemann equation tested against `TF`
    have hweak : ∫ t, f t * Work.MRMT.dzbar (TF : ℂ → ℂ) t = 0 := by
      obtain ⟨-, -, h3⟩ := hf.2.2 TF
      rw [h3]
      simp
    -- the Wirtinger derivative of the mollification, computed by differentiating under the
    -- integral sign (`HasCompactSupport.hasFDerivAt_convolution_right`)
    have hdz : Work.MRMT.dzbar (Work.MRMT.Weyl.moll ρ f) z =
        ∫ t, ((((fderiv ℝ ρ (z - t) 1 : ℝ) : ℂ) +
          Complex.I * ((fderiv ℝ ρ (z - t) Complex.I : ℝ) : ℂ)) / 2) * f t := by
      rw [Work.MRMT.dzbar]
      rw [show ((fderiv ℝ (Work.MRMT.Weyl.moll ρ f) z) 1 +
            Complex.I * (fderiv ℝ (Work.MRMT.Weyl.moll ρ f) z) Complex.I)/2
          = Work.MRMT.Weyl.dzbarCLM (fderiv ℝ (Work.MRMT.Weyl.moll ρ f) z) from
        (Work.MRMT.Weyl.dzbarCLM_apply _).symm]
      rw [hmoll, hh.fderiv, MeasureTheory.convolution_def]
      have key : Work.MRMT.Weyl.dzbarCLM
          (∫ t, (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.lsmul ℝ ℝ).flip
              (f t)) (fderiv ℝ ρ (z - t)))
          = ∫ t, Work.MRMT.Weyl.dzbarCLM ((ContinuousLinearMap.precompR ℂ
              (ContinuousLinearMap.lsmul ℝ ℝ).flip (f t)) (fderiv ℝ ρ (z - t))) :=
        (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (E := ℂ →L[ℝ] ℂ)
          Work.MRMT.Weyl.dzbarCLM hint).symm
      rw [key]
      apply integral_congr_ae
      filter_upwards with t
      rw [Work.MRMT.Weyl.dzbarCLM_apply]
      simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.lsmul_apply, RCLike.real_smul_eq_coe_mul]
      rw [div_mul_eq_mul_div, add_mul, mul_assoc]
      rfl
    rw [hdz]
    have hcongr : (fun t => ((((fderiv ℝ ρ (z - t) 1 : ℝ) : ℂ) +
          Complex.I * ((fderiv ℝ ρ (z - t) Complex.I : ℝ) : ℂ)) / 2) * f t)
        = fun t => - (Work.MRMT.dzbar (TF : ℂ → ℂ) t * f t) := by
      funext t; rw [hTF_deriv t, neg_mul, neg_neg]
    rw [hcongr, integral_neg]
    rw [show (∫ t, Work.MRMT.dzbar (TF : ℂ → ℂ) t * f t)
          = ∫ t, f t * Work.MRMT.dzbar (TF : ℂ → ℂ) t from
        integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _), hweak, neg_zero]
  have hd1 : Work.MRMT.IsDbarDeriv (Work.MRMT.Weyl.moll ρ f)
      (Work.MRMT.dzbar (Work.MRMT.Weyl.moll ρ f)) :=
    Work.MRMT.Weyl.isDbarDeriv_dzbar hmoll_smooth (by simp)
  exact Work.MRMT.Weyl.isDbarDeriv_congr hd1 (fun z => hzero z)

end

end Work.MRMT.Weyl
