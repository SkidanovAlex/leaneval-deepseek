import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs

namespace Work.Drive.Final

/-- The parametrisation `par ψ` of the challenge's surface is periodic under the lattice
`(2πℤ)²`: translating a parameter of the `(θ, φ)`-plane by integer multiples of `2π` in each
variable does not move the corresponding point of `ℝ³`.

This is the two-variable form of `Work.BoxShrink.Pinch.par_period` (which is itself proved from the
`2π`-periodicity of `Work.Core.torusMap` and the identity `par ψ (x, y) = ψ (torusMap x y)`);
it is recorded here in the parameter form in which the sweep and the pinch chart consume it. -/
theorem param_add_int_mul_two_pi (ψ : Submission.Diffeo) (q : ℝ × ℝ) (k m : ℤ) :
    Work.BoxShrink.Pinch.par ψ
        (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (m : ℝ) * (2 * Real.pi)) =
      Work.BoxShrink.Pinch.par ψ q :=
  Work.BoxShrink.Pinch.par_period ψ q k m

end Work.Drive.Final
