import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.moment_two_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the kinetic momentum functionals of a smooth compactly supported state

For `g : ℝ³ → ℂ` smooth with compact support, the `p`-convention Fourier transform
`kinFT g p = ∫_y e^{−i⟪p,y⟫}g(y)dy` is a Schwartz-type object, so all three momentum integrals
needed by the box/continuum bridge are finite:

* `p ↦ ‖kinFT g p‖²` is integrable — this is `L¹∩L²` Plancherel (`kinFT_sq_of_memLp`);
* `p ↦ ‖p‖²‖kinFT g p‖²` is integrable — via the pointwise identity
  `‖p‖²‖kinFT g p‖² = Σ_i ‖kinFT (∂_i g) p‖²` (`normSq_kinFT_eq_sum_normSq_fderiv`) applied to
  the three directional derivatives, each of which is again smooth of compact support;
* `p ↦ e^{−t‖p‖²}‖kinFT g p‖²` is integrable for `t > 0` — the Gaussian weight is `≤ 1`, so it
  is dominated by the first integrand.
-/

open MeasureTheory

namespace Work.BoseBoxFock

/-- Integrability of the momentum weight `p ↦ e^{−t‖p‖²}·‖kinFT g p‖²` for `t > 0`, by
domination against `‖kinFT g p‖²` (the Gaussian factor is `≤ 1`). -/
theorem integrable_exp_mul_kinFT_sq {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Real.exp (-t * ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hgint : MeasureTheory.Integrable g :=
    hg.continuous.integrable_of_hasCompactSupport hgc
  have hgL1 : MeasureTheory.MemLp g 1 MeasureTheory.volume :=
    MeasureTheory.memLp_one_iff_integrable.mpr hgint
  have hgL2 : MeasureTheory.MemLp g 2 MeasureTheory.volume :=
    hg.continuous.memLp_of_hasCompactSupport hgc
  have h1 : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hgL1 hgL2).1
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2) :=
    continuous_norm.pow 2
  refine MeasureTheory.Integrable.mono' h1 ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul hcont)).aestronglyMeasurable).mul
      (((Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hgint).norm.pow 2).aestronglyMeasurable)
  · filter_upwards with p
    have hexp : Real.exp (-t * ‖p‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (‖p‖ : ℝ), ht]
    have hnonneg : 0 ≤ Real.exp (-t * ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnonneg]
    exact mul_le_of_le_one_left (sq_nonneg _) hexp

/-- The momentum second moment `p ↦ ‖p‖²·‖kinFT g p‖²` is integrable for smooth compactly
supported `g`, by trading `‖p‖²` for the three directional derivatives. -/
theorem integrable_mom_sq_mul_kinFT_sq
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hcd : ∀ i : Fin 3, ContDiff ℝ (⊤ : ENat)
      (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) := by
    intro i
    have hf' : ContDiff ℝ (⊤ : ENat) (fderiv ℝ g) :=
      ContDiff.fderiv_right (f := g) (m := (⊤ : ENat)) (n := (⊤ : ENat)) hg (by simp)
    exact hf'.clm_apply contDiff_const
  have hcs : ∀ i : Fin 3, HasCompactSupport
      (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) :=
    fun i => hgc.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis i)
  have hInt : ∀ i : Fin 3, MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2) := by
    intro i
    have h1 : MeasureTheory.MemLp
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) 1 MeasureTheory.volume :=
      MeasureTheory.memLp_one_iff_integrable.mpr
        ((hcd i).continuous.integrable_of_hasCompactSupport (hcs i))
    have h2 : MeasureTheory.MemLp
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) 2 MeasureTheory.volume :=
      (hcd i).continuous.memLp_of_hasCompactSupport (hcs i)
    exact (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp h1 h2).1
  have hsum : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2) := by
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun (i : Fin 3) (p : EuclideanSpace ℝ (Fin 3)) => ‖Submission.BoseGases.kinFT
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2)
      (fun i _ => hInt i)
  refine hsum.congr (Filter.Eventually.of_forall (fun p => ?_))
  exact (normSq_kinFT_eq_sum_normSq_fderiv hg hgc p).symm

theorem integrable_kinFT_mom_triple {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT g p‖^2) ∧
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖^2 * ‖Submission.BoseGases.kinFT g p‖^2) ∧
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Real.exp (-t * ‖p‖^2) * ‖Submission.BoseGases.kinFT g p‖^2) := by
  have hgint : MeasureTheory.Integrable g :=
    hg.continuous.integrable_of_hasCompactSupport hgc
  have hgL1 : MeasureTheory.MemLp g 1 MeasureTheory.volume :=
    MeasureTheory.memLp_one_iff_integrable.mpr hgint
  have hgL2 : MeasureTheory.MemLp g 2 MeasureTheory.volume :=
    hg.continuous.memLp_of_hasCompactSupport hgc
  exact ⟨(Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hgL1 hgL2).1,
    integrable_mom_sq_mul_kinFT_sq hg hgc,
    integrable_exp_mul_kinFT_sq ht hg hgc⟩

end Work.BoseBoxFock
