import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

/-- **The windowed exponential amplitude is the `p`-Fourier transform of the
windowed slot fibre.**  `tBamp χ p Ψ i x` is the integral of
`χ(z)e^{−i⟪p,z⟫}Ψ(x_{i←z})` over `z`, i.e. exactly the Bridge's `p`-convention
Fourier transform `kinFT` of the function `z ↦ χ(z)·Ψ(x_{i←z})`.  The two
definitions differ only in the bracketing and the order of the three factors,
which is immaterial over the commutative field `ℂ`. -/
theorem tBamp_eq_kinFT {N : ℕ} (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) (Ψ : Submission.BoseGases.X N → ℝ) (i : Fin N) (x : Submission.BoseGases.X N) : Work.SmallBoxTBWord.tBamp χ p Ψ i x = Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ) * ((Ψ (Function.update x i z) : ℝ) : ℂ)) p := by
  rw [tBamp, Submission.BoseGases.kinFT]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  ring

end Work.SmallBoxTBWord
