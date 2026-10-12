import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.Strat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PerSector

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-- **The localised potential word is slot-additive.**  `qLHSword` is a *multiplication form*
(`Work.FockBridge.qLHSword_eq_mul_integral`), so it only sees the state through its density `Φ²`; the
slot pieces are disjointly supported, so `(Σ_S slotPiece B S Φ)² = Σ_S (slotPiece B S Φ)²`
pointwise, and the integral splits over the finite sum.  (No kernel is used: the slot pieces
partition the configuration space for *every* box `B`.) -/
theorem qLHSword_eq_sum_slotPiece {ℓ μ : ℝ} {B : Set ℝ³} (w w1 : ℝ³ → ℝ³ → ℝ) {Φ : X N → ℝ}
    (hint : ∀ S : Finset (Fin N),
      MeasureTheory.IntegrableOn (fun x => qLHSden N ℓ μ w w1 x * (slotPiece B S Φ x) ^ 2)
        (abox N ℓ)) :
    qLHSword (N := N) ℓ μ w w1 Φ
      = ∑ S : Finset (Fin N), qLHSword (N := N) ℓ μ w w1 (slotPiece B S Φ) := by
  rw [Work.FockBridge.qLHSword_eq_mul_integral (μ := μ) (ℓ := ℓ) w w1 Φ]
  -- `Φ²` is the sum of the slot-piece squares, so the integrand decomposes into a finite sum of
  -- disjointly supported contributions.
  have h1 : (∫ x in abox N ℓ, qLHSden N ℓ μ w w1 x * (Φ x) ^ 2)
      = ∫ x in abox N ℓ, ∑ S : Finset (Fin N),
          qLHSden N ℓ μ w w1 x * (slotPiece B S Φ x) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    have hpt : ∑ S : Finset (Fin N), (slotPiece B S Φ x) ^ 2 = (Φ x) ^ 2 := by
      rw [Finset.sum_congr rfl (fun S _ => slotPiece_sq B S Φ x)]
      exact sum_indicator_slotSet B (fun y => (Φ y) ^ 2) x
    rw [← Finset.mul_sum, hpt]
  rw [h1, integral_finsetSum _ (fun S _ => hint S)]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Work.FockBridge.qLHSword_eq_mul_integral (μ := μ) (ℓ := ℓ) w w1 (slotPiece B S Φ)]

end Work.PerSector

open Submission.BoseGases

variable {N : ℕ}

/-- **The localised potential word is slot-additive** (`qLHSword`'s density `Φ²` is the sum of the
slot-piece squares and the integral splits over the disjoint pieces), re-exported at the chapter's
outer namespace `Work.PerSector`. -/
theorem qLHSword_eq_sum_slotPiece {ℓ μ : ℝ} {B : Set (EuclideanSpace ℝ (Fin 3))}
    (w w1 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) {Φ : X N → ℝ}
    (hint : ∀ S : Finset (Fin N),
      MeasureTheory.IntegrableOn (fun x => qLHSden N ℓ μ w w1 x * (slotPiece B S Φ x) ^ 2)
        (abox N ℓ)) :
    qLHSword (N := N) ℓ μ w w1 Φ
      = ∑ S : Finset (Fin N), qLHSword (N := N) ℓ μ w w1 (slotPiece B S Φ) :=
  Work.PerSector.Work.PerSector.qLHSword_eq_sum_slotPiece w w1 hint

end Work.PerSector
