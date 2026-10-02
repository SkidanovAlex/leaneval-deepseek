import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_unique
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll_contDiff

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

/-- **Weyl's lemma** (continuous form): a continuous function satisfying the weak Cauchy–Riemann
equation `∂̄ f = 0` distributionally is analytic (holomorphic).

Proof: mollify `f` by a sequence of bump functions with outer radii tending to `0`. Each
mollification is smooth and still satisfies the weak Cauchy–Riemann equation, hence has vanishing
`∂̄` everywhere by uniqueness of weak derivatives; it is therefore entire. By uniform convergence on
compacts, `f` is a locally uniform limit of entire functions, hence entire, hence analytic. -/
theorem analyticOn_of_continuous_isDbarDeriv_zero {f : ℂ → ℂ} (hc : Continuous f)
    (hd : IsDbarDeriv f (fun _ => 0)) : AnalyticOn ℂ f Set.univ := by
  have hloc : LocallyIntegrable f volume := hd.1
  have hne : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (moll ((bump n).normed volume) f) Set.univ := by
    refine Eventually.of_forall (fun n => ?_)
    have hρ : ContDiff ℝ (⊤ : ℕ∞) ((bump n).normed volume) :=
      (bump n).contDiff_normed (μ := volume) (n := ⊤)
    have hρcs : HasCompactSupport ((bump n).normed volume) := (bump n).hasCompactSupport_normed
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (moll ((bump n).normed volume) f) :=
      contDiff_moll hρ hρcs hloc
    have hd1 : IsDbarDeriv (moll ((bump n).normed volume) f) (fun _ => 0) :=
      Work.MRMT.Weyl.isDbarDeriv_moll_contDiff hd hρ hρcs
    have hd2 : IsDbarDeriv (moll ((bump n).normed volume) f)
        (dzbar (moll ((bump n).normed volume) f)) := isDbarDeriv_dzbar hcd hne
    have hae : ∀ᵐ z ∂(volume : Measure ℂ),
        dzbar (moll ((bump n).normed volume) f) z = 0 := by
      have h := Work.MRMT.Sobolev.is_dbar_deriv_unique hd1 hd2
      filter_upwards [h] with z hz
      exact hz.symm
    have heq : dzbar (moll ((bump n).normed volume) f) = 0 :=
      MeasureTheory.Measure.eq_of_ae_eq hae (continuous_dzbar_of_contDiff hcd hne) continuous_zero
    intro z _
    refine (differentiableAt_of_dzbar_eq_zero ((hcd.differentiable hne).differentiableAt) ?_).differentiableWithinAt
    rw [heq]; rfl
  have hdOn : DifferentiableOn ℂ f Set.univ :=
    (tendstoLocallyUniformlyOn_moll hc bump tendsto_rOut_bump).differentiableOn hdiff isOpen_univ
  exact hdOn.analyticOn isOpen_univ

/-- The requested statement. -/
theorem weyl_lemma_continuous {f : ℂ → ℂ} (hc : Continuous f) (h : IsWeaklyConformal f) :
    AnalyticOn ℂ f Set.univ := by
  obtain ⟨g, hg, hg0⟩ := h
  have hd0 : IsDbarDeriv f (fun _ => 0) := by
    refine ⟨hg.1, locallyIntegrable_zero, ?_⟩
    intro ψ
    obtain ⟨h1, h2, h3⟩ := hg.2.2 ψ
    refine ⟨h1, by simp, ?_⟩
    have hzero : ∫ z, g z * (ψ : ℂ → ℂ) z = 0 := by
      have hae : (fun z => g z * (ψ : ℂ → ℂ) z) =ᵐ[(volume : Measure ℂ)] (0 : ℂ → ℂ) := by
        filter_upwards [hg0] with z hz
        simp [hz]
      rw [integral_congr_ae hae]
      simp
    rw [h3, hzero]
    simp
  exact analyticOn_of_continuous_isDbarDeriv_zero hc hd0

end

end Work.MRMT.Weyl
