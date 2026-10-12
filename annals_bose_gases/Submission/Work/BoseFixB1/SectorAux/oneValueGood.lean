import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPIndFibreMassB1
import Submission.Work.BoseFixB1.boxQ0SlackIntegrable
import Submission.Work.BoseFixB1.oneValueAnyB1
import Submission.Work.BoseFixB1S.Gen.boxQIndAesm
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.boxPInd_fib_collapse
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorAux

/-- The one-body (`w₁`) line of the box-potential words at the FS-faithful box projection
`P_{B,i}` (`Work.UBBInputs8.boxPInd`), restricted to the `GoodState` class.

This is the `GoodState`-hypothesis instance of the unconditional identity
`Work.BoseFixB1.oneValueAnyB1` (`Submission/Work/BoseFixB1/oneValueAnyB1.lean`), whose proof
factors the integrand into a function of the slot `i` alone times a function of the remaining
slots, peels slot `i` out of the product box, and evaluates the two one-slot marginals as
`∫_{acube ℓ} 1_A = volA` and `∫_{acube ℓ} 1_A · w₁fibre = boxM1 ℓ A w1`.

The hypotheses `hw1` (integrability of the `w₁`-fibre on `A`) and `hΦ` (that `Φ` is measurable
and bounded on `abox N ℓ`) are not needed for the identity; they are kept because the callers
of this lemma work inside the `GoodState` regime. -/
theorem oneValueGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N)
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw1 : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = (Work.BoseFixB1S.boxM1 ℓ A w1 / volA)
        * (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
  exact Work.BoseFixB1.oneValueAnyB1 hℓ hvol hA hvolA hAc (i := i) (w1 := w1) (Ψ := Φ)

end Work.BoseFixB1.SectorAux
