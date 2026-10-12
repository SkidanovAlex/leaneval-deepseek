import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.SectorAux.sectorPiece_word_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weighted (`H¹`) Plancherel identity for the `p`-convention Fourier transform

For `F : ℝ³ → ℂ` of class `C¹` with compact support, the `p`-convention Fourier transform
`kinFT F p = ∫_y e^{−i⟪p,y⟫}F(y)dy` satisfies the **weighted Plancherel identity**

`∫_p (1 + ‖p‖²)‖kinFT F p‖² = (2π)³ (∫_z ‖F z‖² + ∑_k ∫_z ‖∂_k F z‖²)`,

i.e. the Fourier transform exchanges multiplication by `p` with differentiation, so that the
`H¹`-norm of `F` (the right-hand side) becomes the `L²`-norm of `kinFT F` with weight
`1 + ‖p‖²`.  Both functions appearing are integrable.

The ingredients are

* the pointwise chain rule `‖p‖²‖kinFT F p‖² = Σ_k ‖kinFT (∂_k F) p‖²`
  (`Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one`, from Mathlib's
  `Real.fourier_fderiv` and `Σ_k ⟪p,e_k⟫² = ‖p‖²`);
* the unweighted `L¹ ∩ L²` Plancherel identity `(2π)⁻³∫_p ‖kinFT g p‖² = ∫_x ‖g x‖²`
  (`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`), applied to `F` and to each of the three
  directional derivatives `∂_k F` (which are continuous with compact support, hence in
  `L¹ ∩ L²`);
* the `Fin 3`-bookkeeping (`integral_finsetSum`, `integral_add`) allowed by those integrability
  statements.
-/

open MeasureTheory

namespace Work.BoseFixB1S

theorem weightedPlancherelKinFT {F : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hF1 : ContDiff ℝ 1 F) (hFcs : HasCompactSupport F) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      ∧ (∫ p : EuclideanSpace ℝ (Fin 3), (1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
          ((∫ z : EuclideanSpace ℝ (Fin 3), ‖F z‖ ^ 2)
            + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
                ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by
  -- the three directional derivatives `∂_k F`, as functions
  set gk : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun k z => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k) with hgk
  have hFint : Integrable F := hF1.continuous.integrable_of_hasCompactSupport hFcs
  have hFmem1 : MemLp F 1 volume := memLp_one_iff_integrable.mpr hFint
  have hFmem2 : MemLp F 2 volume := hF1.continuous.memLp_of_hasCompactSupport hFcs
  -- the unweighted Plancherel identity for `F`
  have hbase := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hFmem1 hFmem2
  -- each `∂_k F` is continuous with compact support, hence `L¹ ∩ L²`
  have hcont : ∀ k : Fin 3, Continuous (gk k) := by
    intro k
    exact (hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs : ∀ k : Fin 3, HasCompactSupport (gk k) := fun k => hFcs.fderiv_apply ℝ _
  have hmem1 : ∀ k : Fin 3, MemLp (gk k) 1 volume :=
    fun k => memLp_one_iff_integrable.mpr ((hcont k).integrable_of_hasCompactSupport (hcs k))
  have hmem2 : ∀ k : Fin 3, MemLp (gk k) 2 volume :=
    fun k => (hcont k).memLp_of_hasCompactSupport (hcs k)
  have hIntD : ∀ k : Fin 3, Integrable (fun p => ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2) :=
    fun k => (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp (hmem1 k) (hmem2 k)).1
  -- unweighted Plancherel for each `kinFT (∂_k F)`, solved for the momentum integral
  have hplanch : ∀ k : Fin 3,
      (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), ‖gk k z‖ ^ 2 := by
    intro k
    have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
    calc (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
            (((2 * Real.pi) ^ 3)⁻¹ *
              ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      _ = (2 * Real.pi) ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), ‖gk k z‖ ^ 2 := by
          rw [(Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp (hmem1 k) (hmem2 k)).2]
  -- the pointwise chain rule: the second moment of `kinFT F` is the sum of the transforms
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2
        = ∑ k : Fin 3, ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2 := fun p =>
    Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one hF1 hFcs p
  have hsumInt : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ∑ k : Fin 3, ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2) := by
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun (k : Fin 3) (p : EuclideanSpace ℝ (Fin 3)) =>
        ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2) (fun k _ => hIntD k)
  have hmomInt : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2) :=
    hsumInt.congr (Filter.Eventually.of_forall (fun p => (hpt p).symm))
  -- integrability of the weighted integrand
  have hIntW : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT F p‖ ^ 2) :=
    (hbase.1.add hmomInt).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.add_apply]; ring))
  -- unweighted Plancherel for `F`, solved for the momentum integral
  have hbaseEq : (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), ‖F z‖ ^ 2 := by
    have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
    calc (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT F p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
            (((2 * Real.pi) ^ 3)⁻¹ *
              ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT F p‖ ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      _ = (2 * Real.pi) ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), ‖F z‖ ^ 2 := by rw [hbase.2]
  -- the momentum second moment, integrated
  have hmomIntEq : (∫ p : EuclideanSpace ℝ (Fin 3),
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
                ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
    calc (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
        = ∫ p : EuclideanSpace ℝ (Fin 3),
            ∑ k : Fin 3, ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          exact hpt p
      _ = ∑ k : Fin 3, ∫ p : EuclideanSpace ℝ (Fin 3),
            ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2 := by
          simpa using integral_finsetSum (Finset.univ : Finset (Fin 3))
            (f := fun (k : Fin 3) (p : EuclideanSpace ℝ (Fin 3)) =>
              ‖Submission.BoseGases.kinFT (gk k) p‖ ^ 2) (fun k _ => hIntD k)
      _ = ∑ k : Fin 3, (2 * Real.pi) ^ 3 *
            ∫ z : EuclideanSpace ℝ (Fin 3), ‖gk k z‖ ^ 2 :=
          Finset.sum_congr rfl (fun k _ => hplanch k)
      _ = (2 * Real.pi) ^ 3 * ∑ k : Fin 3,
            ∫ z : EuclideanSpace ℝ (Fin 3), ‖gk k z‖ ^ 2 := by rw [Finset.mul_sum]
  refine ⟨hIntW, ?_⟩
  calc (∫ p : EuclideanSpace ℝ (Fin 3), (1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          (‖Submission.BoseGases.kinFT F p‖ ^ 2
            + ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        ring
    _ = (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT F p‖ ^ 2)
          + ∫ p : EuclideanSpace ℝ (Fin 3),
              ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2 :=
        integral_add hbase.1 hmomInt
    _ = ((2 * Real.pi) ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), ‖F z‖ ^ 2)
          + (2 * Real.pi) ^ 3 * ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
                ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
        rw [hbaseEq, hmomIntEq]
    _ = (2 * Real.pi) ^ 3 *
          ((∫ z : EuclideanSpace ℝ (Fin 3), ‖F z‖ ^ 2)
            + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
                ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by ring

end Work.BoseFixB1S
