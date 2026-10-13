import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` is *not* pre-bound as `Real.pi` here (`autoImplicit = false`); the `Real` scope is what
-- makes the notation in the statement below resolve to `Real.pi`.
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR.SourceSide

/-- **The residual of the truncation of the mode series is a.e. strongly measurable on the
closed quadrant.**  The point is that the target measure `volume.restrict (Ioi 0 ×ˢ Icc 0 (π/2))`
agrees with `volume.restrict Q0` (they differ by the null set `Ioi 0 ×ˢ {0, π/2}`), where:

* `F` itself is continuous, hence a.e. strongly measurable (`SmoothOpen F`);
* each mode coefficient `z ↦ cmode m F z` is a.e. strongly measurable in `z` (the
  parameter-dependent-integral lemma `aesm_cmode` of `cmode_memLp`), and pulling it back along
  the projection `Prod.fst` preserves a.e. strong measurability because that projection is
  quasi-measure-preserving for the product measure;
* each `θ ↦ eFam m θ` is continuous.

Only finitely many mode functions enter, so the partial sum, and then the difference with `F`,
are a.e. strongly measurable. -/
theorem joint_aesm_partialSum_residual {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (N : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        - F p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Icc 0 (π / 2))) := by
  -- Replace the closed domain by the `Iθ`-form used throughout the API.
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  rw [← hIθ]
  -- The two domains differ only by the null set `Ioi 0 ×ˢ {0, π/2}`.
  rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
  -- `volume.restrict Q0` is a product measure, so `Prod.fst` is quasi-measure-preserving.
  have hQ0prod : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        Work.FTS.EllipticEst.Q0
      = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi 0)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
    rw [Work.FTS.EllipticEst.Q0, MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact (MeasureTheory.Measure.prod_restrict (Set.Ioi 0) (Set.Ioo 0 (π / 2))).symm
  -- The source datum itself.
  have hF : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        Work.FTS.EllipticEst.Q0) :=
    hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- The truncated mode sum.
  have hS : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        Work.FTS.EllipticEst.Q0) := by
    have hsum : MeasureTheory.AEStronglyMeasurable
        (∑ m ∈ Finset.range (N + 1), fun p : ℝ × ℝ =>
          Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          Work.FTS.EllipticEst.Q0) :=
      Finset.aestronglyMeasurable_sum (Finset.range (N + 1)) (fun m _ => by
        -- The `z`-dependent factor, pulled back along the first projection.
        have hcm : MeasureTheory.AEStronglyMeasurable
            (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi 0)) :=
          Work.EllipticEst.ModalSolution.aesm_cmode hsm m
        have hcm1 : MeasureTheory.AEStronglyMeasurable
            (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.cmode m F p.1)
            ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
              Work.FTS.EllipticEst.Q0) := by
          rw [hQ0prod]
          exact hcm.comp_quasiMeasurePreserving
            MeasureTheory.Measure.quasiMeasurePreserving_fst
        -- The angular factor is continuous, hence a.e. strongly measurable.
        have he : MeasureTheory.AEStronglyMeasurable
            (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
            ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
              Work.FTS.EllipticEst.Q0) :=
          ((Work.EllipticEst.ModalSolution.continuous_eFam m).measurable.comp
            measurable_snd).aestronglyMeasurable
        exact hcm1.mul he)
    refine hsum.congr ?_
    filter_upwards with p
    simp only [Finset.sum_apply]
  exact hS.sub hF

end Work.FTS.H2.ModalSolR.SourceSide
