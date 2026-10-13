import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

set_option maxHeartbeats 1000000

/-- At an angular endpoint (`sin (2θ) = 0`) the weighted `∂_θ`-integrand vanishes, whatever the
value of the derivative. -/
private lemma sliceThetaHardy_zero (α : ℝ) (hα0 : 0 < α) {θ : ℝ}
    (h : Real.sin (2 * θ) = 0) (x : ℝ) :
    (Real.sin (2 * θ) * x) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) = 0 := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    have hg : Work.Spaces.gam α = 1 + α / 10 := rfl
    rw [hg]; linarith
  rw [h]
  simp [Real.zero_rpow (neg_ne_zero.mpr hgam)]

theorem sliceThetaHardy : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (j : ℕ),
    Work.FTS.EllipticEst.SmoothOpen f → j ≤ 5 →
      ∀ {z : ℝ}, 0 < z →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ →
        (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter j f z θ) ^ 2)
          ≤ C / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed j 1 f z θ) ^ 2)
              + (Work.Spaces.DzIter j f z (Real.pi / 4)) ^ 2) := by
  -- the sharp angular Hardy inequality of `thetaHardyA` supplies the constant
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
  refine ⟨C0, hC0pos, ?_⟩
  intro α hα f j hf hj z hz hint
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hgam : Work.Spaces.gam α ≠ 0 := by
    have hg : Work.Spaces.gam α = 1 + α / 10 := rfl
    rw [hg]; linarith
  -- the fixed positive radius `z` turns `f` into a one-variable function of the angle
  let g : ℝ → ℝ := fun θ => Work.Spaces.DzIter j f z θ
  have hgapp : ∀ θ : ℝ, g θ = Work.Spaces.DzIter j f z θ := fun θ => rfl
  have hgc1 : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi / 2)) :=
    ((hf.DzIter j).curry_θ hz).of_le (by norm_num [Work.Stability.smoothOrder])
  -- the hypothesis on `∂_θ (D_z^j f)` is the hypothesis on `deriv g`
  have hptEq : Set.EqOn
      (fun θ : ℝ => (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (fun θ : ℝ => (Real.sin (2 * θ) * deriv g θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
    intro θ hθ
    simp only []
    by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hd : deriv g θ = Work.Spaces.pth (Work.Spaces.DzIter j f) z θ := rfl
      rw [hd]
    · have hs := Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [sliceThetaHardy_zero α hα0 hs (Work.Spaces.pth (Work.Spaces.DzIter j f) z θ),
        sliceThetaHardy_zero α hα0 hs (deriv g θ)]
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ) * deriv g θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    hint.congr_fun hptEq measurableSet_Icc
  have hhardy := hC0 α hα g hgc1 hint2
  -- `sin (2θ) · deriv g = mixed j 1 f` (Clairaut + the Leibniz rule for the θ-only factor)
  have hmixed : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j 1 f z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ := by
    intro θ hθ
    rw [Work.FTS.EllSol.WeakSlice.pth_DzIter_Q0 hf j hz hθ, ← Work.FTS.H2.sin_mul_dzIter_pth]
  have hJ : (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ) * deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j 1 f z θ) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hd : deriv g θ = Work.Spaces.pth (Work.Spaces.DzIter j f) z θ := rfl
      rw [hd, ← hmixed θ hθi]
      exact mul_comm _ _
    · have hs := Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [sliceThetaHardy_zero α hα0 hs (deriv g θ), hs,
        Real.zero_rpow (neg_ne_zero.mpr hgam)]
      ring
  -- the left-hand side has its factors written in the other order
  have hLHS : (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(1 - α / 10)) * (Work.Spaces.DzIter j f z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [hgapp]
    exact mul_comm _ _
  -- the constant: `C0 / α ≤ C0 / α ^ 2` because `α ≤ 1`
  have hQnn : (0 : ℝ) ≤ (g (Real.pi / 4)) ^ 2 := sq_nonneg _
  have hαle : C0 / α ≤ C0 / α ^ 2 := by
    have h1 : (1 : ℝ) / α ≤ 1 / α ^ 2 :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < α ^ 2) (by nlinarith [hα0, hα1])
    calc C0 / α = C0 * (1 / α) := div_eq_mul_one_div C0 α
      _ ≤ C0 * (1 / α ^ 2) := mul_le_mul_of_nonneg_left h1 hC0pos.le
      _ = C0 / α ^ 2 := (div_eq_mul_one_div C0 (α ^ 2)).symm
  have hstep : C0 / α * (g (Real.pi / 4)) ^ 2 ≤ C0 / α ^ 2 * (g (Real.pi / 4)) ^ 2 :=
    mul_le_mul_of_nonneg_right hαle hQnn
  have hmain : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
      ≤ C0 / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed j 1 f z θ) ^ 2)
          + (g (Real.pi / 4)) ^ 2) := by
    calc (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10)))
        ≤ C0 / α ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ) * deriv g θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            + C0 / α * (g (Real.pi / 4)) ^ 2 := hhardy
      _ = C0 / α ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed j 1 f z θ) ^ 2)
            + C0 / α * (g (Real.pi / 4)) ^ 2 := by rw [hJ]
      _ ≤ C0 / α ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed j 1 f z θ) ^ 2)
            + C0 / α ^ 2 * (g (Real.pi / 4)) ^ 2 := by linarith [hstep]
      _ = C0 / α ^ 2 * ((∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed j 1 f z θ) ^ 2)
            + (g (Real.pi / 4)) ^ 2) := by ring
  rw [hLHS]
  simpa only [hgapp] using hmain

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
