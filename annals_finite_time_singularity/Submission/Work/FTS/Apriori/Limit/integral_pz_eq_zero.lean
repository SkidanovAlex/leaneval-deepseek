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

theorem integral_pz_eq_zero {W : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd)
    (hcomp : HasCompactSupport (Function.uncurry W)) (hsub : tsupport (Function.uncurry W) ⊆ Qd) :
    ∫ p, Work.Spaces.pz W p.1 p.2 ∂Qμ = 0 := by
  obtain ⟨A, B, C, D, hA, hAB, hC, hCD, hD, hvA, hvB, hvC, hvD⟩ := exists_box_vanish hcomp hsub
  have hA' : 0 < A / 2 := by linarith
  have hA'A : A / 2 < A := by linarith
  have hBB' : B < B + 1 := by linarith
  have hA'B' : A / 2 ≤ B + 1 := by linarith
  have hint : Integrable (Function.uncurry (Work.Spaces.pz W)) Qμ :=
    integrable_of_continuousOn_of_support ((Work.FTS.LocData.contDiffOn_pz isOpen_Qd hsm).continuousOn)
      hcomp hsub (support_pz_subset_tsupport W)
  change ∫ p : ℝ × ℝ, Function.uncurry (Work.Spaces.pz W) p ∂Qμ = 0
  rw [Qμ]
  rw [MeasureTheory.integral_prod_symm _ hint]
  have h0 : (fun θ : ℝ => ∫ z, Function.uncurry (Work.Spaces.pz W) (z, θ) ∂(volume.restrict Work.Spaces.Iz)) = fun _ => (0 : ℝ) := by
    funext θ
    show (∫ z, Work.Spaces.pz W z θ ∂(volume.restrict Work.Spaces.Iz)) = 0
    by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
    · have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => W z θ) (Set.Ioi 0) :=
        Work.FTS.LocData.contDiffOn_slice_z hsm hθ
      have hpzslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z => Work.Spaces.pz W z θ) (Set.Ioi 0) :=
        Work.FTS.LocData.contDiffOn_slice_z (Work.FTS.LocData.contDiffOn_pz isOpen_Qd hsm) hθ
      have hIz : ∫ z, Work.Spaces.pz W z θ ∂(volume.restrict Work.Spaces.Iz)
          = ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz W z θ := by
        rw [Work.Spaces.Iz]
        rw [← MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
      rw [hIz]
      have hset : ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz W z θ
          = ∫ z in Set.Icc (A / 2) (B + 1), Work.Spaces.pz W z θ := by
        refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (fun z hz => lt_of_lt_of_le hA' hz.1) (fun z hz => ?_)
        rw [Set.mem_sdiff, Set.mem_Icc, not_and_or] at hz
        rcases hz with ⟨hzpos, hz | hz⟩
        · exact pz_eq_zero_of_forall_lt hvA z θ (by linarith)
        · exact pz_eq_zero_of_forall_gt hvB z θ (by linarith)
      rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hA'B']
      have hcont : ContinuousOn (fun z => W z θ) (Set.Icc (A / 2) (B + 1)) :=
        hslice.continuousOn.mono (fun z hz => lt_of_lt_of_le hA' hz.1)
      have hcont' : ContinuousOn (fun z => Work.Spaces.pz W z θ)
          (Set.Icc (A / 2) (B + 1)) :=
        hpzslice.continuousOn.mono (fun z hz => lt_of_lt_of_le hA' hz.1)
      have hderiv : ∀ x ∈ Set.Ioo (A / 2) (B + 1),
          HasDerivAt (fun z => W z θ) (Work.Spaces.pz W x θ) x := by
        intro x hx
        have hx0 : x ∈ Set.Ioi (0 : ℝ) := by
          rw [Set.mem_Ioi]; linarith [hx.1]
        exact ((hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
          (isOpen_Ioi.mem_nhds hx0)).hasDerivAt
      have hint' : IntervalIntegrable (fun z => Work.Spaces.pz W z θ) volume (A / 2) (B + 1) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hA'B']
        exact hcont'
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hA'B' hcont hderiv hint',
        hvB (B + 1) θ hBB', hvA (A / 2) θ hA'A]
      ring
    · have hz0 : ∀ z, W z θ = 0 := by
        intro z
        by_contra h
        have hmem : (z, θ) ∈ tsupport (Function.uncurry W) :=
          subset_tsupport _ (by simpa [Function.mem_support, Function.uncurry] using h)
        exact hθ (mem_Qd_iff.mp (hsub hmem)).2
      rw [show (fun z => Work.Spaces.pz W z θ) = fun _ => (0 : ℝ) from
        funext (fun z => by simp [Work.Spaces.pz, funext hz0])]
      simp
  rw [h0, MeasureTheory.integral_zero]

end Work.FTS.Apriori.Limit
