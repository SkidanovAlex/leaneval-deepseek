import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.Defs
import Submission.Work.BoseFixB1.SectorAux.sectorPiece_word_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Momentum second-moment (derivative) Plancherel at `C¹` regularity

For `f : ℝ³ → ℂ` of class `C¹` with compact support,

`(2π)⁻³ ∫_p ‖p‖²‖kinFT f p‖² = Σ_j ∫_z ‖∂_{e_j} f z‖²`   (`e_j = kcStdBasis j`),

where `kinFT f p = ∫_y e^{−i⟪p,y⟫}f(y)dy` is the corpus's `p`-convention Fourier transform.

The identity is the standard Fourier expression of the Dirichlet energy: Plancherel applied to
each of the three directional derivatives `∂_{e_j} f` (which are continuous with compact support,
hence `L¹ ∩ L²`, so `Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp` applies), together with the
pointwise Fourier-derivative identity
`kinFT (∂_{e_j} f) p = i ⟨p,e_j⟩ · kinFT f p`
(`Work.BoseFixB1.SectorAux.kinFT_fderiv_applyC_one`, i.e. Mathlib's `Real.fourier_fderiv`) and
`Σ_j ⟨p,e_j⟩² = ‖p‖²`.

This is the `C¹` counterpart of the proved `C^∞` lemmas
`Work.BoseBoxFock.L1Tails.kinFT_secondMomentPlancherel` and
`Work.BoseBoxFock.kinFT_secondMomentPlancherel_aux`; the only hypothesis actually used is
`ContDiff ℝ 1` (`hf.continuous_fderiv`), which is what the pointwise identity
`Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one` provides.
-/

noncomputable section

open MeasureTheory Filter

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- The unweighted `L¹ ∩ L²` Plancherel identity in the `p`-convention, solved for the
unnormalised momentum integral: for a continuous compactly supported `G`,

`∫_p ‖kinFT G p‖² = (2π)³ ∫_z ‖G z‖²`,

and `p ↦ ‖kinFT G p‖²` is integrable. -/
private theorem kinFT_sq_plancherel_one {G : E3 → ℂ} (hG : Continuous G)
    (hGc : HasCompactSupport G) :
    MeasureTheory.Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT G p‖ ^ 2) ∧
      (∫ p : E3, ‖Submission.BoseGases.kinFT G p‖ ^ 2)
        = (2 * Real.pi) ^ 3 * ∫ z : E3, ‖G z‖ ^ 2 := by
  have h1 : MemLp G 1 := memLp_one_iff_integrable.mpr (hG.integrable_of_hasCompactSupport hGc)
  have h2 : MemLp G 2 := hG.memLp_of_hasCompactSupport hGc
  have hbase := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp h1 h2
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  refine ⟨hbase.1, ?_⟩
  calc (∫ p : E3, ‖Submission.BoseGases.kinFT G p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : E3, ‖Submission.BoseGases.kinFT G p‖ ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = (2 * Real.pi) ^ 3 * ∫ z : E3, ‖G z‖ ^ 2 := by rw [hbase.2]

/-- **Momentum second-moment (derivative) Plancherel, unnormalised form.**  For `f` of class `C¹`
with compact support,

`∫_p ‖p‖²‖kinFT f p‖² = (2π)³ Σ_j ∫_z ‖∂_{e_j} f z‖²`. -/
theorem kinFTSecondMomentPlancherelOne {f : E3 → ℂ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∑ j : Fin 3, ∫ z : E3,
          ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
  have hcont : ∀ k : Fin 3,
      Continuous (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcsk : ∀ k : Fin 3,
      HasCompactSupport (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) :=
    fun k => hfc.fderiv_apply ℝ _
  have hkey : ∀ k : Fin 3,
      MeasureTheory.Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2)
        ∧ (∫ p : E3, ‖Submission.BoseGases.kinFT
              (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2)
          = (2 * Real.pi) ^ 3 *
              ∫ z : E3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 :=
    fun k => kinFT_sq_plancherel_one (hcont k) (hcsk k)
  have hpt : ∀ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2
      = ∑ k : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 :=
    fun p => Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one hf hfc p
  calc (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2)
      = ∫ p : E3, ∑ k : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ∑ k : Fin 3, ∫ p : E3, ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 := by
        simpa using integral_finsetSum (Finset.univ : Finset (Fin 3))
          (f := fun (k : Fin 3) (p : E3) => ‖Submission.BoseGases.kinFT
            (fun z : E3 => fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2)
          (fun k _ => (hkey k).1)
    _ = ∑ k : Fin 3, (2 * Real.pi) ^ 3 *
          ∫ z : E3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 :=
        Finset.sum_congr rfl (fun k _ => (hkey k).2)
    _ = (2 * Real.pi) ^ 3 * ∑ k : Fin 3,
          ∫ z : E3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
        rw [Finset.mul_sum]

theorem secondMomentPlancherelOne {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2)
      = ∑ j : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
          ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  rw [kinFTSecondMomentPlancherelOne hf hfc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Work.BoseBoxFock.L1Tails
