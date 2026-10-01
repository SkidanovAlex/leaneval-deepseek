import Mathlib.Data.Real.Basic

namespace Commons.NumberTheory.Linnik

/-- The tent-shaped weight of Heath-Brown (1992), §13: supported on the interval
`(L - 2*K, L]`, rising linearly from `0` (at `x = L - 2*K`) to `K`
(at `x = L - K`), then falling back to `0` (at `x = L`), and `0` outside.
Here `L` and `K` are the constants of §13, satisfying `0 < 2*K < L`. -/
noncomputable def tentWeight (L K x : ℝ) : ℝ :=
  if x ≤ L - 2 * K then 0
  else if x ≤ L - K then x - (L - 2 * K)
  else if x ≤ L then L - x
  else 0

theorem tentWeight_spec (L K x : ℝ) :
    tentWeight L K x =
      if x ≤ L - 2 * K then 0
      else if x ≤ L - K then x - (L - 2 * K)
      else if x ≤ L then L - x
      else 0 := by
  rw [tentWeight]

end Commons.NumberTheory.Linnik