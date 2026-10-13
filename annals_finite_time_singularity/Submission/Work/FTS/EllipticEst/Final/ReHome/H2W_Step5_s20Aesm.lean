/-
Copied from `Submission.Work.FTS.EllipticEst.H2W.Step5.s20Aesm` for `Final/slot20_bound_fts`.
Only the `import` lines are redirected (see `Final/slot20_bound_fts.lean` for why):
the copy of `Mine/TopSlotTwo` (`Final/ReHome/TkKit.lean`) drops the `Mine/ShiftLevelOne`
import and the two declarations at the end of that file that use it, which cuts the
`RPFresh/excess_finite` dependency out of the closure.
-/

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

/-! ## A.e. strong measurability of the two dominating integrands of `slot20_bound`

The two integrands

`s20F4 α Ψ = 2 w² (∂_θ⁴Ψ)² σ₄`,   `s20F3 α Ψ = 8 w² (∂_θ³Ψ)² σ₂`

(with `σ₄ = sin(2θ)^{4-γ}`, `σ₂ = sin(2θ)^{2-γ}`) are continuous on the open quadrant
`(0,∞) × (0,π/2)`: the iterated angular derivatives `∂_θ^j Ψ` are continuous there
(`hsmooth` at finite orders, one `∂_θ` at a time via the `fderiv` description of `∂_θ` on an
open set), the radial weight `w(z) = (1+z)²/z²` is continuous for `z ≠ 0`, and
`sin(2θ)^{c}` is continuous where `sin(2θ) > 0`.  Since the open quadrant differs from
`Iz ×ˢ Iθ` by a null set, and the whole integrand vanishes identically at `z = 0` (because
`w 0 = 0`), continuity gives a.e. strong measurability of every `θ`-slice and of the joint
integrand; Fubini for Bochner integrals then transfers the joint measurability to the
parameter integrals `z ↦ ∫_θ …`. -/

/-- The open quadrant of the smoothness hypothesis. -/
private abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem s20Aesm (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.AEStronglyMeasurable
          (fun θ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.AEStronglyMeasurable
          (fun θ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hV : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo
  -- One angular derivative at a time: on an open set the partial `∂_θ` is the evaluation of
  -- the Fréchet derivative at `(0,1)`, so finite-order smoothness drops by one.
  have hstep : ∀ {H : ℝ → ℝ → ℝ} {m : ℕ},
      ContDiffOn ℝ (m + 1) (Function.uncurry H) Qd →
      ContDiffOn ℝ m (Function.uncurry (Work.Spaces.pth H)) Qd := by
    intro H m h
    have key : ∀ (z θ : ℝ), (z, θ) ∈ Qd →
        Work.Spaces.pth H z θ = fderiv ℝ (Function.uncurry H) (z, θ) (0, 1) :=
      fun z θ hzθ => Work.Spaces.pth_eq_fderiv
        ((h.differentiableOn (by norm_num : (m + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
          (hV.mem_nhds hzθ))
    have hfd : ContDiffOn ℝ m (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry H) p) Qd :=
      h.fderiv_of_isOpen hV (m := m) (by norm_num)
    have hcomp : ContDiffOn ℝ m
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry H) p) (0, 1)) Qd :=
      hfd.clm_apply contDiffOn_const
    refine hcomp.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    exact key z θ hp
  -- The uncurried angular derivatives `∂_θ^j Ψ` are continuous on the open quadrant.
  have hpth4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 4 Ψ p.1 p.2) Qd := by
    have h1 : ContDiffOn ℝ 4 (Function.uncurry Ψ) Qd := hsmooth 4
    have h2 : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.pth Ψ)) Qd := hstep (m := 3) h1
    have h3 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Ψ))) Qd :=
      hstep (m := 2) h2
    have h4 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pth Ψ)))) Qd :=
      hstep (m := 1) h3
    have h5 : ContDiffOn ℝ 0
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pth
          (Work.Spaces.pth Ψ))))) Qd :=
      hstep (m := 0) h4
    have h5c : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pthIter 4 Ψ)) Qd := by
      simpa only [Work.Spaces.pthIter] using h5
    exact h5c.continuousOn
  have hpth3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 3 Ψ p.1 p.2) Qd := by
    have h1 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Qd := hsmooth 3
    have h2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Qd := hstep (m := 2) h1
    have h3 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Ψ))) Qd :=
      hstep (m := 1) h2
    have h4 : ContDiffOn ℝ 0
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pth Ψ)))) Qd :=
      hstep (m := 0) h3
    have h4c : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pthIter 3 Ψ)) Qd := by
      simpa only [Work.Spaces.pthIter] using h4
    exact h4c.continuousOn
  -- The radial weight, the sine and the angular weights are continuous on the quadrant.
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hnum : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Qd :=
      (continuous_const.continuousOn.add continuous_fst.continuousOn).pow 2
    have hden : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) Qd := continuous_fst.continuousOn.pow 2
    have hne : ∀ p ∈ Qd, p.1 ^ 2 ≠ 0 := fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
    exact hnum.div hden hne
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinne : ∀ p ∈ Qd, Real.sin (2 * p.2) ≠ 0 := fun p hp =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2]))
  have hsig4 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) p.2) Qd :=
    hsin.rpow_const (p := 4 - Work.Spaces.gam α) (fun p hp => Or.inl (hsinne p hp))
  have hsig2 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) p.2) Qd :=
    hsin.rpow_const (p := 2 - Work.Spaces.gam α) (fun p hp => Or.inl (hsinne p hp))
  -- Hence the two integrands are continuous on the open quadrant.
  have hcont4 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ p.1 p.2) Qd := by
    have h : ContinuousOn (fun p : ℝ × ℝ =>
        2 * (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter 4 Ψ p.1 p.2) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) p.2)) Qd :=
      (continuousOn_const.mul (hw.pow 2)).mul ((hpth4.pow 2).mul hsig4)
    simpa only [Work.FTS.EllipticEst.H2W.s20F4] using h
  have hcont3 : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ p.1 p.2) Qd := by
    have h : ContinuousOn (fun p : ℝ × ℝ =>
        8 * (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter 3 Ψ p.1 p.2) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) p.2)) Qd :=
      (continuousOn_const.mul (hw.pow 2)).mul ((hpth3.pow 2).mul hsig2)
    simpa only [Work.FTS.EllipticEst.H2W.s20F3] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the `θ`-slices of `s20F4`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · -- at `z = 0` the integrand vanishes because `w 0 = 0`
      rw [← h]
      have hzero : (fun θ : ℝ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ 0 θ) =
          fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by simp [Work.FTS.EllipticEst.H2W.s20F4, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont4 h
  · -- the `θ`-slices of `s20F3`
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · rw [← h]
      have hzero : (fun θ : ℝ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ 0 θ) =
          fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => by simp [Work.FTS.EllipticEst.H2W.s20F3, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont3 h
  · -- the `z`-parameter integral of `s20F4`, by Fubini for Bochner integrals
    exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont4).integral_prod_right'
  · exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont3).integral_prod_right'

end Work.FTS.EllipticEst.H2W.Step5
