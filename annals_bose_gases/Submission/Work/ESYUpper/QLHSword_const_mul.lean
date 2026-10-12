import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ESYUpper.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
namespace Work.ESYUpper

theorem QLHSword_const_mul {N : ℕ} (ℓ μ s : ℝ)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.qLHSword ℓ μ w w1 (fun x => s * Φ x)
      = s ^ 2 * Submission.BoseGases.qLHSword ℓ μ w w1 Φ := by
  rw [Submission.BoseGases.qLHSword, Submission.BoseGases.qLHSword]
  have : (fun x => (s * Φ x) ^ 2 *
        (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)) +
          (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))
      = fun x => s ^ 2 * ((Φ x) ^ 2 *
        (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)) +
          (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))) := by
    funext x; ring
  rw [this]
  rw [MeasureTheory.integral_const_mul]

end Work.ESYUpper
