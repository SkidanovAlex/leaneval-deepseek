import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Sliding
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

theorem hcmp_of_tBword {N : ℕ} {ℓ d μ b : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) {M : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (eBf : EuclideanSpace ℝ (Fin 3) → ℝ) (eps c : ℝ) (hbox : ∀ u : EuclideanSpace ℝ (Fin 3), eBf u ≤ Work.SmallBoxTBWord.tBwordB N ℓ d eps c u Φ + Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ) (hbs : (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ Φ + (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxTBWord.tBwordB N ℓ d eps c u Φ) ≤ Submission.BoseGases.kinWord N ℓ Φ) (hpot : (∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ) ≤ Submission.BoseGases.qLHSword (N := N) ℓ μ (Submission.BoseGases.wPairC ℓ v) (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ) (hintbox : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => eBf u)) (hintt : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.SmallBoxTBWord.tBwordB N ℓ d eps c u Φ)) (hintq : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ)) : (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ Φ + (∫ u : EuclideanSpace ℝ (Fin 3), eBf u) ≤ Submission.BoseGases.kinWord N ℓ Φ + Submission.BoseGases.qLHSword (N := N) ℓ μ (Submission.BoseGases.wPairC ℓ v) (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ := by
  -- Integrability of the pointwise dominating function.
  have hsum : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.SmallBoxTBWord.tBwordB N ℓ d eps c u Φ + Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ) :=
    hintt.add hintq
  -- Integrate the pointwise bound `hbox`.
  have hmono : (∫ u : EuclideanSpace ℝ (Fin 3), eBf u) ≤ ∫ u : EuclideanSpace ℝ (Fin 3), (Work.SmallBoxTBWord.tBwordB N ℓ d eps c u Φ + Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ) :=
    MeasureTheory.integral_mono hintbox hsum hbox
  -- Split the integral of the sum.
  rw [MeasureTheory.integral_add hintt hintq] at hmono
  -- Combine the three bounds by linear arithmetic.
  linarith

end Work.SmallBoxTBWord
