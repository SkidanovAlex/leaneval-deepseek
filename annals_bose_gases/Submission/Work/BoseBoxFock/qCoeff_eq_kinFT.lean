import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.qCoeff_eq_ft
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

/-- **The `qVec`-coefficient is the Fourier coefficient of the windowed mean-free state.**  For
smooth `ψ` supported in the box `boxL ℓ`, the corpus's localised-plane-wave coefficient against
`qVec ℓ (kmomInt ℓ n)` is literally the `p`-convention transform, at the lattice momentum
`kmomInt ℓ n`, of `g := χ_Λ·(ψ − m)` with `m := ℓ⁻³∫_{acube ℓ}ψ`:
`qCoeff ℓ (kmomInt ℓ n) ψ = kinFT g (kmomInt ℓ n)`.  This is `FINDING_kinRow_lattice.md` §1
(Reduction 1), and it converts `firstMomentSum ℓ ψ` into the lattice first moment `S1` of `g`. -/
theorem qCoeff_eq_kinFT {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) (n : Fin 3 → ℤ) :
    Work.BoseBoxFock.qCoeff ℓ (Work.BoseBoxFock.kmomInt ℓ n) ψ
      = Submission.BoseGases.kinFT
          (fun z => ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ) *
            ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt ℓ n) := by
  -- `qCoeff_eq_ft` (Reduction 1) identifies the `qVec`-coefficient with the integral of the
  -- windowed mean-free state against the conjugate plane wave; unfolding the `p`-convention
  -- transform `kinFT` turns the right-hand side into the same integral.
  rw [qCoeff_eq_ft hℓ hψ hψsupp (kmomInt ℓ n)]
  simp only [Submission.BoseGases.kinFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

end Work.BoseBoxFock
