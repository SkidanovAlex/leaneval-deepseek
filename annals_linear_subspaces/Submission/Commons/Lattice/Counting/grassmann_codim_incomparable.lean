import Mathlib.Algebra.Order.Star.Real

namespace Commons.Lattice.Counting

/-- Submodularity-counting inequality used in Lemma 3 (submodularity of
`φ(W) = log‖W‖ + A·dim W·(d − dim W)`) of de Saxcé, *Rational approximations to linear
subspaces*: if `m + 1 ≤ x` and `m + 1 ≤ y` (dims of two incomparable subspaces and of their
intersection: `x = dim V`, `y = dim W`, `m = dim(V∩W)`), then with `n := x + y − m =
dim(V+W)`, `f(m) + f(n) + 2 ≤ f(x) + f(y)` for `f(t) = t·(d − t)`.  Suggested proof: first
prove in this file the pure-ring identity
`x*(d-x) + y*(d-y) - (m*(d-m) + (x+y-m)*(d-(x+y-m))) = 2*(x-m)*(y-m)` (`by ring`), then use
`1 ≤ x-m`, `1 ≤ y-m` from the hypotheses. -/
theorem grassmann_codim_incomparable (x y m d : ℝ) (hx : m + 1 ≤ x) (hy : m + 1 ≤ y) :
    m * (d - m) + (x + y - m) * (d - (x + y - m)) + 2 ≤ x * (d - x) + y * (d - y) := by
  have hxm : (1 : ℝ) ≤ x - m := by linarith
  have hym : (1 : ℝ) ≤ y - m := by linarith
  have htwo : (2 : ℝ) ≤ 2 * ((x - m) * (y - m)) := by
    have hprod : (1 : ℝ) ≤ (x - m) * (y - m) := by nlinarith
    nlinarith
  nlinarith [htwo, show
    x * (d - x) + y * (d - y) -
        (m * (d - m) + (x + y - m) * (d - (x + y - m))) = 2 * ((x - m) * (y - m)) by
      ring]

end Commons.Lattice.Counting