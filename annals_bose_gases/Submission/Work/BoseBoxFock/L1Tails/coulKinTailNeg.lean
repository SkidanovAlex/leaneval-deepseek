import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.SectorAux.sectorPiece_word_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Filter

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- The unweighted `L¹ ∩ L²` Plancherel identity in the shape used below, together with the
integrability of the momentum-side integrand, for a continuous compactly supported `G`. -/
private theorem kinFT_sq_plancherel {G : E3 → ℂ} (hG : Continuous G) (hGc : HasCompactSupport G) :
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

/-- **Momentum second-moment (Dirichlet) Plancherel**, with integrability: for `F` of class
`C^∞` with compact support,
`∫_p ‖p‖²‖kinFT F p‖² = (2π)³ Σ_k ∫_z ‖∂_{e_k} F z‖²` (`e_k = kcStdBasis k`). -/
theorem kinFT_secondMomentPlancherel {F : E3 → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) :
    MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2) ∧
      (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
        = (2 * Real.pi) ^ 3 * ∑ k : Fin 3, ∫ z : E3,
            ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hcont : ∀ k : Fin 3,
      Continuous (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcsk : ∀ k : Fin 3,
      HasCompactSupport (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) :=
    fun k => hFc.fderiv_apply ℝ _
  have hkey : ∀ k : Fin 3,
      Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2)
        ∧ (∫ p : E3, ‖Submission.BoseGases.kinFT
              (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2)
          = (2 * Real.pi) ^ 3 *
              ∫ z : E3, ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 :=
    fun k => kinFT_sq_plancherel (hcont k) (hcsk k)
  have hpt : ∀ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2
      = ∑ k : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 :=
    fun p => Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one hF1 hFc p
  have hIntSum : Integrable (fun p : E3 => ∑ k : Fin 3, ‖Submission.BoseGases.kinFT
      (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2) := by
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun (k : Fin 3) (p : E3) => ‖Submission.BoseGases.kinFT
        (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2)
      (fun k _ => (hkey k).1)
  refine ⟨hIntSum.congr (Eventually.of_forall (fun p => (hpt p).symm)), ?_⟩
  calc (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
      = ∫ p : E3, ∑ k : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ∑ k : Fin 3, ∫ p : E3, ‖Submission.BoseGases.kinFT
          (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 := by
        simpa using integral_finsetSum (Finset.univ : Finset (Fin 3))
          (f := fun (k : Fin 3) (p : E3) => ‖Submission.BoseGases.kinFT
            (fun z : E3 => fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2)
          (fun k _ => (hkey k).1)
    _ = ∑ k : Fin 3, (2 * Real.pi) ^ 3 *
          ∫ z : E3, ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 :=
        Finset.sum_congr rfl (fun k _ => (hkey k).2)
    _ = (2 * Real.pi) ^ 3 * ∑ k : Fin 3,
          ∫ z : E3, ‖fderiv ℝ F z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
        rw [Finset.mul_sum]

theorem coulKinTailNeg {ψ : EuclideanSpace ℝ (Fin 3) → ℂ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ (-p)‖ ^ 2) ∧
    (∫⁻ p, ENNReal.ofReal (‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ (-p)‖ ^ 2))
      = ENNReal.ofReal ((2 * Real.pi) ^ 3 *
          ∑ j : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
            ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  obtain ⟨hInt, hEq⟩ := kinFT_secondMomentPlancherel hψ hψc
  -- integrability of the reflected integrand
  have hIntNeg : MeasureTheory.Integrable (fun p : E3 =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ (-p)‖ ^ 2) := by
    have h := hInt.comp_neg
    refine h.congr (Eventually.of_forall (fun t => ?_))
    simp only [norm_neg]
  refine ⟨hIntNeg, ?_⟩
  -- the reflection `p ↦ −p` does not change the integral
  have hneg : (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ (-p)‖ ^ 2)
      = ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ p‖ ^ 2 := by
    rw [← MeasureTheory.integral_neg_eq_self
      (fun q : E3 => ‖q‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ q‖ ^ 2) MeasureTheory.volume]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [norm_neg]
  -- the standard basis is the coordinate basis of the statement
  have hsum : (∑ k : Fin 3, ∫ z : E3,
        ‖fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = ∑ j : Fin 3, ∫ x : E3,
          ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [Submission.BoseGases.kcStdBasis]
  have hIntEq : (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ (-p)‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∑ j : Fin 3, ∫ x : E3,
          ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    rw [hneg, hEq, hsum]
  calc ∫⁻ p, ENNReal.ofReal (‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ (-p)‖ ^ 2)
      = ENNReal.ofReal (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT ψ (-p)‖ ^ 2) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntNeg
          (Eventually.of_forall (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).symm
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * ∑ j : Fin 3, ∫ x : E3,
          ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by rw [hIntEq]

end Work.BoseBoxFock.L1Tails
