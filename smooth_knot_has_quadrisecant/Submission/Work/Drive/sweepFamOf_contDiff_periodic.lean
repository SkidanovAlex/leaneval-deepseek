import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.contDiff_doubleBlur_scalar

/-!
# Smoothness and periodicity of the double bump-blur of a continuous loop family

`Work.Drive.sweepFamOf Γ δ₁ δ₂` is the double convolution of an arbitrary family `Γ` with the
smooth bump `sweepBump`, in the loop parameter (width `δ₁`) and in the sweep parameter (width
`δ₂`).  This file proves that, for **any jointly continuous, `period`-periodic family** `Γ`,

* the family is jointly `C^∞` (in particular `C¹`),
* it is `period`-periodic in the loop parameter, and
* every `s`-slice is `C^∞`.

The route is the same as in `Submission/Work/Drive/sweepFam_contDiff_periodic.lean` (where the
special case `Γ = sweepLoopChamfer r D lam` is treated): after the substitutions
`x = s - δ₂ v` and `y = t - δ₁ u` the double interval integral is the convolution of
`Φ = fun p => Γ p.1 p.2` with the smooth compactly supported kernel `sweepKernel δ₁ δ₂`, and
convolution with such a kernel maps *locally integrable* functions to `C^∞` functions
(`HasCompactSupport.contDiff_convolution_right`).  Joint continuity of `Γ` is all that is used:
it gives local integrability of `Φ`, and no differentiability of `Γ` is required.
-/

noncomputable section

namespace Work.Drive

open MeasureTheory

open LeanEval.KnotTheory.Quadrisecant in
theorem sweepFamOf_contDiff_periodic
    (Γ : ℝ → ℝ → Space) (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    (hper : ∀ s t : ℝ, Γ s (t + period) = Γ s t)
    (δ₁ δ₂ : ℝ) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => Work.Drive.sweepFamOf Γ δ₁ δ₂ p.1 p.2) ∧
    (∀ s t : ℝ, Work.Drive.sweepFamOf Γ δ₁ δ₂ s (t + period)
      = Work.Drive.sweepFamOf Γ δ₁ δ₂ s t) ∧
    (∀ s : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Work.Drive.sweepFamOf Γ δ₁ δ₂ s t)) := by
  -- `Φ` is the family as a function on `ℝ × ℝ`; its joint continuity gives local integrability.
  have hΦ : LocallyIntegrable (fun p : ℝ × ℝ => Γ p.1 p.2) volume := hΓ.locallyIntegrable
  -- ## `period`-periodicity in the loop parameter
  have hper' : ∀ s t : ℝ, sweepFamOf Γ δ₁ δ₂ s (t + period) = sweepFamOf Γ δ₁ δ₂ s t := by
    intro s t
    simp only [sweepFamOf]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    congr 1
    rw [show t + period - δ₁ * u = (t - δ₁ * u) + period by ring]
    exact hper (s - δ₂ * v) (t - δ₁ * u)
  -- ## the family is the convolution of `Φ` with the smooth kernel `sweepKernel`
  have hconv : ∀ p : ℝ × ℝ, sweepFamOf Γ δ₁ δ₂ p.1 p.2
      = ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
          (fun q : ℝ × ℝ => Γ q.1 q.2) y := by
    intro p
    rw [sweepKernel_convolution_eq_gen (fun q : ℝ × ℝ => Γ q.1 q.2) hΦ hδ₁ hδ₂ p.1 p.2]
    rfl
  -- ## joint smoothness
  have hmain : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
        (fun q : ℝ × ℝ => Γ q.1 q.2) y) := by
    have h := (hasCompactSupport_sweepKernel hδ₁ hδ₂).contDiff_convolution_right
      (n := (⊤ : ℕ∞)) (μ := volume)
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip : Space →L[ℝ] ℝ →L[ℝ] Space) hΦ
      (contDiff_sweepKernel δ₁ δ₂)
    have hfun : (MeasureTheory.convolution (fun q : ℝ × ℝ => Γ q.1 q.2) (sweepKernel δ₁ δ₂)
          ((ContinuousLinearMap.lsmul ℝ ℝ).flip : Space →L[ℝ] ℝ →L[ℝ] Space)
          MeasureTheory.volume)
        = (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
            (fun q : ℝ × ℝ => Γ q.1 q.2) y) := by
      funext p
      rw [MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [hfun] at h
    exact h
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => sweepFamOf Γ δ₁ δ₂ p.1 p.2) := by
    have hfun : (fun p : ℝ × ℝ => sweepFamOf Γ δ₁ δ₂ p.1 p.2)
        = (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
            (fun q : ℝ × ℝ => Γ q.1 q.2) y) := funext hconv
    simpa only [hfun] using hmain
  refine ⟨hF.of_le one_le_coe_top, hper', fun s => ?_⟩
  -- the `s`-slice is the composition of the joint family with `t ↦ (s, t)`
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    ((fun p : ℝ × ℝ => sweepFamOf Γ δ₁ δ₂ p.1 p.2) ∘ fun t : ℝ => (s, t))
  exact hF.comp (contDiff_prodMk_right s)

end Work.Drive
