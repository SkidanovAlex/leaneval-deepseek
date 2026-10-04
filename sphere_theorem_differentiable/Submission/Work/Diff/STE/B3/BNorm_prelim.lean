import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3, the `B3Data.J` norm estimate: shared vocabulary

This module only fixes the *vocabulary* used by the pieces of the proof of
`Work.Diff.STE.B3.BNorm_J_le` (the bound `D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h`), so that the
auxiliary lemmas can be stated in it.

The Friedrichs truncation of a **real** function `f` on the flat space is, as a complex-valued
function,

`STruncC ρ ε f z = ofReal (re (seriesFun (trunc ρ ε (fourierCoeff (per f))) z))`,

i.e. the complex lift of `Work.Diff.STE.B3Data.STruncR ρ ε f` (which is only defined for the index
type `Fin (Module.finrank ℝ E)`); `STruncC` is stated for a general finite index `ι` so that the
Fourier analysis on the flat space can be phrased independently of the manifold.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE

/-- **The (complex lift of the) Friedrichs truncation `S_ε` of a real flat function**, i.e. the
`1`-periodic function whose Fourier coefficients are `ρ (ε • m)` times those of the periodisation
of `f`, with the real part taken. -/
def STruncC {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) (ε : ℝ)
    (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℂ :=
  fun z => Complex.ofReal (Complex.re (seriesFun (trunc ρ ε
    (fourierCoeff (fun y => ∑' m : ι → ℤ, Complex.ofReal (f (y + iVec m))))) z))

@[simp] lemma STruncC_apply {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) (ε : ℝ)
    (f : (ι → ℝ) → ℝ) (z : ι → ℝ) :
    STruncC ρ ε f z = Complex.ofReal (Complex.re (seriesFun (trunc ρ ε
      (fourierCoeff (fun y => ∑' m : ι → ℤ, Complex.ofReal (f (y + iVec m))))) z)) := rfl

end Work.Diff.STE
