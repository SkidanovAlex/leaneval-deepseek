import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftDefs
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.BoseFixB1S

-- NB: `ℝ³` is the *global* notation `EuclideanSpace ℝ (Fin 3)` of
-- `Submission.Work.BoseKinLoc.Defs` (already in scope here); declaring a `local notation`
-- for it makes every occurrence ambiguous.

set_option maxHeartbeats 1000000

/-- **Per-box Plancherel.**  For `0 < ℓ`, `0 < d`, smooth `w` and every `u`, the `p`-space
mass of the cut state `z ↦ χ_{B(u)}(z)·w(z)` is `(2π)³` times its `x`-space `L²` mass:

`∫_p ‖bsPsi (χ_{B(u)}·w) p‖² = (2π)³ ∫_z χ_{B(u)}(z)²·w(z)²`.

Both sides exist as (nonnegative) `∫`-conventions: `χ_{B(u)}·w` is smooth with compact
support (`contDiff_chiB`, `hasCompactSupport_chiB`, `hw`), so
`Work.BSKinetic.plancherel_pconv` applies at every `u`. -/
lemma integral_bsPsi_chiB_mul_sq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {w : ℝ³ → ℝ}
    (hw : ContDiff ℝ (⊤ : ENat) w) (u : ℝ³) :
    (∫ p : ℝ³, ‖Work.BSKinetic.Decomp.bsPsi (fun z : ℝ³ =>
        Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (∫ z : ℝ³,
          (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2) := by
  have hcu : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => Submission.BoseGases.chiB ℓ d u z * w z) :=
    (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).mul hw
  have hsu : HasCompactSupport (fun z : ℝ³ => Submission.BoseGases.chiB ℓ d u z * w z) :=
    (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u).mul_right
  have hp := Work.BSKinetic.plancherel_pconv
    (fun z : ℝ³ => Submission.BoseGases.chiB ℓ d u z * w z) hcu hsu
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 (by positivity)
  have hsix : (∫ p : ℝ³, ‖Work.BSKinetic.Decomp.bsPsi (fun z : ℝ³ =>
        Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (∫ z : ℝ³,
          (Submission.BoseGases.chiB ℓ d u z * w z) ^ 2) := by
    have key := congrArg (fun t : ℝ => (2 * Real.pi) ^ 3 * t) hp
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at key
    simpa only [Work.BSKinetic.Decomp.bsPsi] using key
  rw [hsix]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))

theorem corrPlanchMarg {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : ContDiff ℝ (⊤ : ENat) w)
    (hint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      ∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2))
    (heq : (∫ u : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2)
      = ∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ p : EuclideanSpace ℝ (Fin 3), ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
      ∧ (∫ u : EuclideanSpace ℝ (Fin 3), ∫ p : EuclideanSpace ℝ (Fin 3),
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
            (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2) := by
  have hpoint : ∀ u : ℝ³, (∫ p : ℝ³, ‖Work.BSKinetic.Decomp.bsPsi (fun z : ℝ³ =>
        Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (∫ z : ℝ³,
          (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2) :=
    fun u => integral_bsPsi_chiB_mul_sq hℓ hd hw u
  refine ⟨?_, ?_⟩
  · exact (hint.const_mul ((2 * Real.pi) ^ 3)).congr
      (Filter.Eventually.of_forall fun u => (hpoint u).symm)
  · have hfuneq : (fun u : ℝ³ => ∫ p : ℝ³, ‖Work.BSKinetic.Decomp.bsPsi (fun z : ℝ³ =>
          Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
        = fun u : ℝ³ => (2 * Real.pi) ^ 3 * (∫ z : ℝ³,
            (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2) := funext hpoint
    rw [hfuneq, MeasureTheory.integral_const_mul, heq]

end Work.BoseFixB1S
