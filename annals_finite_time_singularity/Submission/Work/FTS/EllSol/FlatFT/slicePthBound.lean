import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.FTS.EllSol.slice_zero_slot_finite
import Submission.Work.FTS.EllSol.FlatFT.sliceIntegralPointwise
import Submission.Work.FTS.EllSol.FlatFT.sliceCSMass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## The slice bound -/

theorem slicePthBound (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ₁ : ℝ} (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (2 * (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * (Work.Spaces.pth g z θ₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  -- The angular slice `F θ = g z θ` of the datum.
  set F : ℝ → ℝ := fun θ => g z θ with hF
  -- the weight is nonnegative on `Iθ`
  have hθI : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- ### smoothness of the slice
  have hF2 : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h := hg.comp hmap (fun θ hθ => ⟨Set.mem_univ θ, hθ⟩)
    simpa [hF, Function.comp_def, Function.uncurry] using h
  have hF1 : ContDiffOn ℝ 1 (deriv F) (Set.Ioo 0 (Real.pi / 2)) :=
    hF2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hF0 : ContinuousOn (deriv (deriv F)) (Set.Ioo 0 (Real.pi / 2)) :=
    (hF1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn
  -- ### the fundamental theorem of calculus on subintervals of `(0,π/2)`
  have hftc2 : ∀ {a b : ℝ}, a ∈ Set.Ioo 0 (Real.pi / 2) → b ∈ Set.Ioo 0 (Real.pi / 2) →
      a ≤ b → ∫ t in a..b, deriv (deriv F) t = deriv F b - deriv F a := by
    intro a b ha hb hab
    have hcd : ContDiffOn ℝ 1 (deriv F) (Set.Icc a b) :=
      hF1.mono (fun x hx => ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩)
    exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hab
  -- ### the mass of the second angular derivative
  set M : ℝ := ∫ t in Work.Spaces.Iθ,
      (deriv (deriv F) t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
    intro t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hθI t ht) _)
  have hintF : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (deriv (deriv F) t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pth, hF] using hint
  -- ### the pointwise bound on the slice
  have hpoint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv F θ) ^ 2 ≤ 2 * (Real.pi / 2) * M + 2 * (deriv F θ₁) ^ 2 := by
    intro θ hθ
    have hA : 0 ≤ (Real.pi / 2) * M := mul_nonneg (by positivity) hMnn
    have hdiff : |deriv F θ - deriv F θ₁| ≤ Real.sqrt ((Real.pi / 2) * M) := by
      rcases le_total θ₁ θ with hle | hle
      · have hftc := hftc2 hθ₁ hθ hle
        have hcs := sliceCSMass (u := fun t => deriv (deriv F) t) hθ₁ hθ hF0 hintF
        rw [hftc] at hcs
        have hcs' : (deriv F θ - deriv F θ₁) ^ 2 ≤ (Real.pi / 2) * M := hcs
        rw [← Real.sq_sqrt hA] at hcs'
        have := sq_le_sq.mp hcs'
        rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
      · have hftc := hftc2 hθ hθ₁ hle
        have hcs := sliceCSMass (u := fun t => deriv (deriv F) t) hθ hθ₁ hF0 hintF
        rw [hftc] at hcs
        have hsq : (deriv F θ - deriv F θ₁) ^ 2 = (deriv F θ₁ - deriv F θ) ^ 2 := by ring
        have hcs' : (deriv F θ - deriv F θ₁) ^ 2 ≤ (Real.pi / 2) * M := by
          rw [hsq]; exact hcs
        rw [← Real.sq_sqrt hA] at hcs'
        have := sq_le_sq.mp hcs'
        rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
    have hxsq : (deriv F θ - deriv F θ₁) ^ 2 ≤ (Real.pi / 2) * M := by
      calc (deriv F θ - deriv F θ₁) ^ 2 = |deriv F θ - deriv F θ₁| ^ 2 := by rw [sq_abs]
        _ ≤ (Real.sqrt ((Real.pi / 2) * M)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
        _ = (Real.pi / 2) * M := Real.sq_sqrt hA
    have h1 : (deriv F θ) ^ 2 ≤ 2 * (deriv F θ₁) ^ 2 + 2 * (deriv F θ - deriv F θ₁) ^ 2 := by
      nlinarith [sq_nonneg (deriv F θ - 2 * deriv F θ₁)]
    have h2 : 2 * (deriv F θ - deriv F θ₁) ^ 2 ≤ 2 * ((Real.pi / 2) * M) := by linarith
    linarith
  -- ### integration of the pointwise bound
  have hC : 0 ≤ 2 * (Real.pi / 2) * M + 2 * (deriv F θ₁) ^ 2 := by
    have h1 : 0 ≤ 2 * (Real.pi / 2) * M := mul_nonneg (by positivity) hMnn
    have h2 : 0 ≤ (deriv F θ₁) ^ 2 := sq_nonneg _
    linarith
  have hgm : MeasureTheory.AEStronglyMeasurable (deriv F)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllSol.aesm_of_continuousOn_Ioo hF1.continuousOn
  obtain ⟨hint', hineq⟩ :=
    sliceIntegralPointwise (u := fun t => deriv F t)
      (C := 2 * (Real.pi / 2) * M + 2 * (deriv F θ₁) ^ 2) hC hgm
      (fun θ hθ => hpoint θ hθ)
  refine ⟨?_, ?_⟩
  · simpa only [Work.Spaces.pth, hF] using hint'
  · simpa only [Work.Spaces.pth, hF, hM] using hineq

end Work.FTS.EllSol.FlatFT
