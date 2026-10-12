import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Word

theorem boxFormB_eq_parts_of_integrable {m : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {ℓ μ d s εT b : ℝ} (Φ : Submission.BoseGases.X m → ℝ)
    (hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X m => (Φ x) ^ 2 *
      (-μ * (∑ i : Fin m, ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc ℓ g 0 (x i) y)))
      (Submission.BoseGases.abox m ℓ))
    (hB : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X m => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin m × Fin m | ij.1 < ij.2},
        Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox m ℓ)) :
    Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Φ =
      Work.BoseKinLoc.kinFormB m ℓ d s εT b Φ + Work.BoseKinLoc.chemPartB m g ℓ μ Φ
        + Work.BoseKinLoc.pairPartB m v ℓ Φ := by
  -- Unfold the definitions of the form and of the multiplicative potential word: both sides are
  -- now `kinFormB + ∫_{abox} (Φ x)^2 * (A x + B x)` versus `kinFormB + ∫ A + ∫ B`, where the two
  -- pieces `A`, `B` of the integrand are exactly the ones whose integrability is hypothesised.
  simp only [Work.BoseKinLoc.boxFormB, Work.BoseKinLoc.kinFormB, Work.BoseKinLoc.chemPartB,
    Work.BoseKinLoc.pairPartB, Work.BoseKinLoc.potWordU, mul_add]
  rw [MeasureTheory.integral_add hA hB]
  ring

end Work.BoseKinLoc.Word
