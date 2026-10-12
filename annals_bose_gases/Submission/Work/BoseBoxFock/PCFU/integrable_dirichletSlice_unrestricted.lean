import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.dirichletPeel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-- The one-slot windowed Dirichlet energy of a smooth state is integrable as a function of the
remaining `n` coordinates, against the *unrestricted* slot integral (contrast
`Work.BoseBoxFock.PCFU.integrable_dirichletSlice`, whose slot integral is restricted to the
one-particle cube).  (`Work.BoseBoxFock.PCFU.integrable_dirichletSlice_unrestricted`.) -/
theorem integrable_dirichletSlice_unrestricted {n : ℕ} (i : Fin (n + 1)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        ∫ y : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
          ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale ℓ z
              * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
  classical
  -- The integrand is the same function of the pair `(y, r)` as in `integrable_dirichletSlice`,
  -- which is integrable for the product of the two restricted measures.
  have hGint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      ∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, p.2))) p.1
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    integrable_dirichletSlice i hℓ hΦ
  -- Fubini (one direction) turns this into integrability of the `r`-slice against the
  -- restricted slot measure on the one-particle cube.
  have hslice := hGint.integral_prod_right
  -- `χ_ℓ` is supported in the cube, so the *unrestricted* slot integral coincides with the
  -- cube-restricted one, pointwise in `r`.
  refine hslice.congr (Filter.Eventually.of_forall fun r => ?_)
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Submission.BoseGases.acube ℓ)
    (f := fun y : EuclideanSpace ℝ (Fin 3) => ∑ k : Fin 3,
          ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale ℓ z
              * Φ (Submission.BoseGases.kcInsN n i (z, r))) y
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ?_
  intro y hy
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [fderiv_dirichletSlice_eq_zero_of_notMem_acube i hℓ hy r]
  simp

end Work.BoseBoxFock.PCFU
