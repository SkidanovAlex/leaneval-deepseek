import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc
import Submission.Work.FTS.Apriori.Limit.TestQClosure
import Submission.Work.FTS.Apriori.Limit.SupportBox
import Submission.Work.FTS.Apriori.Limit.DerivVanish
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
namespace Work.FTS.Apriori.Limit
set_option autoImplicit false
open Work.FTS.LocData (SmoothQuad)

theorem integral_pth_eq_zero {W : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd)
    (hcomp : HasCompactSupport (Function.uncurry W)) (hsub : tsupport (Function.uncurry W) ⊆ Qd) :
    ∫ p, Work.Spaces.pth W p.1 p.2 ∂Qμ = 0 := by
  obtain ⟨A, B, C, D, hA, hAB, hC, hCD, hD, hvA, hvB, hvC, hvD⟩ := exists_box_vanish hcomp hsub
  have hC' : 0 < C / 2 := by linarith
  have hC'C : C / 2 < C := by linarith
  have hCD' : C / 2 ≤ (D + π / 2) / 2 := by linarith
  have hDD' : D < (D + π / 2) / 2 := by linarith
  have hD' : (D + π / 2) / 2 < π / 2 := by linarith
  have hint : Integrable (Function.uncurry (Work.Spaces.pth W)) Qμ :=
    integrable_of_continuousOn_of_support
      ((Work.FTS.LocData.contDiffOn_pth isOpen_Qd hsm).continuousOn)
      hcomp hsub (support_pth_subset_tsupport W)
  change ∫ p : ℝ × ℝ, Function.uncurry (Work.Spaces.pth W) p ∂Qμ = 0
  rw [Qμ]
  rw [MeasureTheory.integral_prod _ hint]
  have h0 : (fun z : ℝ => ∫ θ, Function.uncurry (Work.Spaces.pth W) (z, θ)
        ∂(volume.restrict Work.Spaces.Iθ)) = fun _ => (0 : ℝ) := by
    funext z
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth W z θ) = 0
    rw [Work.Spaces.Iθ]
    by_cases hz : 0 < z
    · have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => W z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.contDiffOn_slice_θ hsm (by rw [Set.mem_Ioi]; exact hz)
      have hpthslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun θ => Work.Spaces.pth W z θ) (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.contDiffOn_slice_θ
          (Work.FTS.LocData.contDiffOn_pth isOpen_Qd hsm) (by rw [Set.mem_Ioi]; exact hz)
      have hset : ∫ θ in Set.Icc (0 : ℝ) (π / 2), Work.Spaces.pth W z θ
          = ∫ θ in Set.Icc (C / 2) ((D + π / 2) / 2), Work.Spaces.pth W z θ := by
        refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
          (Set.Icc_subset_Icc (by linarith) (by linarith)) (fun θ hθ => ?_)
        have hlt_or : θ < C / 2 ∨ (D + π / 2) / 2 < θ := by
          by_contra hcon
          push_neg at hcon
          exact hθ.2 (Set.mem_Icc.mpr hcon)
        rcases hlt_or with hlt | hgt
        · exact pth_eq_zero_of_forall_theta_lt hvC z θ (by linarith)
        · exact pth_eq_zero_of_forall_theta_gt hvD z θ (by linarith)
      rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hCD']
      have hcont : ContinuousOn (fun θ => W z θ) (Set.Icc (C / 2) ((D + π / 2) / 2)) :=
        hslice.continuousOn.mono (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
      have hcont' : ContinuousOn (fun θ => Work.Spaces.pth W z θ)
          (Set.Icc (C / 2) ((D + π / 2) / 2)) :=
        hpthslice.continuousOn.mono (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
      have hderiv : ∀ x ∈ Set.Ioo (C / 2) ((D + π / 2) / 2),
          HasDerivAt (fun θ => W z θ) (Work.Spaces.pth W z x) x := by
        intro x hx
        have hxmem : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
          ⟨by linarith [hx.1], by linarith [hx.2]⟩
        exact ((hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
          (isOpen_Ioo.mem_nhds hxmem)).hasDerivAt
      have hint' : IntervalIntegrable (fun θ => Work.Spaces.pth W z θ) volume (C / 2)
          ((D + π / 2) / 2) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hCD']
        exact hcont'
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hCD' hcont hderiv hint',
        hvD z ((D + π / 2) / 2) hDD', hvC z (C / 2) hC'C]
      ring
    · have hz0 : ∀ θ, W z θ = 0 := by
        intro θ
        by_contra h
        have hmem : (z, θ) ∈ tsupport (Function.uncurry W) :=
          subset_tsupport _ (by simpa [Function.mem_support, Function.uncurry] using h)
        exact hz (mem_Qd_iff.mp (hsub hmem)).1
      rw [show (fun θ => Work.Spaces.pth W z θ) = fun _ => (0 : ℝ) from
        funext (fun θ => by simp [Work.Spaces.pth, funext hz0])]
      simp
  rw [h0, MeasureTheory.integral_zero]

end Work.FTS.Apriori.Limit
