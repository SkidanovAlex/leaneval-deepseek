import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Probability.Bernoulli

/-- The Bernoulli measure `Ber(x, y, p)` is pushed forward by an affine map
`t ↦ a * t + b` (with `a ≠ 0`) to the Bernoulli measure with the image atoms. -/
theorem map_affine {x y a b : ℝ} {p : unitInterval} (ha : a ≠ 0) :
    (ProbabilityTheory.bernoulliMeasure x y p).map (fun t : ℝ => a * t + b)
      = ProbabilityTheory.bernoulliMeasure (a * x + b) (a * y + b) p := by
  rw [ProbabilityTheory.map_bernoulliMeasure]

end Commons.Probability.Bernoulli