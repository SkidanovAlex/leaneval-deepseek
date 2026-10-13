import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllSol.PkgK5.GroupCmpK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The per-slice comparison.**  For every `z ∈ Iz` the `ℋ^k`-integrand of the quotient
`Φ/sin 2θ` is honest on the angular slice and its `θ`-integral is bounded by a universal multiple
of the `θ`-integral of the `ℋ^k`-integrand of `∂_θΦ`. -/
theorem perSliceCmpK (k : ℕ) (hk : 1 ≤ k) : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (Φ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen Φ →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2))) →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.Spaces.HkMem α k (Work.Spaces.pth Φ) →
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k
          (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
            (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
          ≤ K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
              (Work.Spaces.pth Φ) z θ) := by
  obtain ⟨Kg, hKgpos, hgroup⟩ := groupCmpK k
  refine ⟨Kg, hKgpos, ?_⟩
  intro α Φ hα hα1 hSO hsl ht0 ht1 hmem z hz
  set U : ℝ → ℝ → ℝ := fun z' θ' => Φ z' θ' / Real.sin (2 * θ') with hUdef
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k U 0 θ) = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.Spaces.HkIntegrand]
      simp only [hUdef, Work.Spaces.Wt, Work.Spaces.w]
      simp
    refine ⟨?_, ?_⟩
    · rw [hzero]
      exact integrableOn_zero
    · rw [hzero, MeasureTheory.integral_zero]
      exact mul_nonneg hKgpos.le (MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth Φ) 0 θ)
  · -- the honest slice `z > 0`
    have hgrpInt : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α k j U z θ) Work.Spaces.Iθ :=
      fun j hj => (hgroup α Φ hα hα1 hSO hsl ht0 ht1 hmem z hzpos hz j hj).1
    have hgrpIntR : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ)
        Work.Spaces.Iθ := by
      intro j hj
      refine (Work.FTS.EllipticEst.integrableOn_zSummand α k hSO.pth hmem j hj hz).add ?_
      refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      exact Work.FTS.EllipticEst.integrableOn_mixedSummand α k hSO.pth hmem i j hi1
        (by omega) hz
    have hsumfun : (fun θ : ℝ => Work.Spaces.HkIntegrand α k U z θ)
        = fun θ : ℝ => ∑ j ∈ Finset.range (k + 1),
            Work.FTS.EllipticEst.sliceGroup α k j U z θ := by
      funext θ
      exact Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k U z θ
    have hsumfunR : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth Φ) z θ)
        = fun θ : ℝ => ∑ j ∈ Finset.range (k + 1),
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ := by
      funext θ
      exact Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pth Φ) z θ
    refine ⟨?_, ?_⟩
    · rw [MeasureTheory.IntegrableOn, hsumfun]
      exact MeasureTheory.integrable_finsetSum _
        (fun j hj => hgrpInt j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    · have hL : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
          = ∑ j ∈ Finset.range (k + 1),
              (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j U z θ) := by
        rw [hsumfun]
        exact MeasureTheory.integral_finset_sum _
          (fun j hj => hgrpInt j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      have hR : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth Φ) z θ)
          = ∑ j ∈ Finset.range (k + 1),
              (∫ θ in Work.Spaces.Iθ,
                Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ) := by
        rw [hsumfunR]
        exact MeasureTheory.integral_finset_sum _
          (fun j hj => hgrpIntR j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      rw [hL, hR, Finset.mul_sum]
      exact Finset.sum_le_sum (fun j hj =>
        (hgroup α Φ hα hα1 hSO hsl ht0 ht1 hmem z hzpos hz j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2)
end Work.FTS.EllSol.PkgK5
