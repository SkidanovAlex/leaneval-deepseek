import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

-- `hui` is part of the requested statement but the identity holds unconditionally
-- (`integral_conj` carries no integrability hypothesis); silence the unused-variable linter.
set_option linter.unusedVariables false

/-- Reflection in the momentum variable acts on the `p`-convention Fourier transform by complex
conjugation, for a self-conjugate integrable `u`:  `kinFT u (-p) = conj (kinFT u p)`.

Indeed `kinFT u (-p) = ∫_y e^{i⟪p,y⟫}u(y)dy`, while
`conj (kinFT u p) = ∫_y conj (e^{-i⟪p,y⟫}u(y))dy = ∫_y e^{i⟪p,y⟫}conj (u(y))dy`, and
`conj (u y) = u y`. -/
theorem kinFT_neg_eq_conj {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : ∀ x : EuclideanSpace ℝ (Fin 3), starRingEnd ℂ (u x) = u x)
    (hui : MeasureTheory.Integrable u (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT u (-p) = starRingEnd ℂ (Submission.BoseGases.kinFT u p) := by
  simp only [Submission.BoseGases.kinFT, inner_neg_left]
  rw [← integral_conj]
  congr 1
  funext y
  rw [map_mul, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, hu y,
    Complex.ofReal_neg]
  congr 1
  ring_nf

end Work.BoseBoxFock
