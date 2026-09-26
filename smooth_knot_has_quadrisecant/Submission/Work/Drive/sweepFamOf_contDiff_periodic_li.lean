import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.sweepFamOf_contDiff_periodic

namespace Work.Drive

open MeasureTheory

open LeanEval.KnotTheory.Quadrisecant in
theorem sweepFamOf_contDiff_periodic_li (Γ : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space)
    (hΓ : MeasureTheory.LocallyIntegrable (fun p : ℝ × ℝ => Γ p.1 p.2) MeasureTheory.volume)
    (hper : ∀ s t : ℝ, Γ s (t + LeanEval.KnotTheory.Quadrisecant.period) = Γ s t)
    (δ₁ δ₂ : ℝ) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => Work.Drive.sweepFamOf Γ δ₁ δ₂ p.1 p.2) ∧
    (∀ s t : ℝ, Work.Drive.sweepFamOf Γ δ₁ δ₂ s (t + LeanEval.KnotTheory.Quadrisecant.period)
      = Work.Drive.sweepFamOf Γ δ₁ δ₂ s t) ∧
    (∀ s : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Work.Drive.sweepFamOf Γ δ₁ δ₂ s t)) := by
  -- `Φ` is the family as a function on `ℝ × ℝ`; local integrability is the hypothesis.
  have hΦ : LocallyIntegrable (fun p : ℝ × ℝ => Γ p.1 p.2) volume := hΓ
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
