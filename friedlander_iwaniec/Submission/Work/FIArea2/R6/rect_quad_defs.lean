import Mathlib

namespace Work.FIArea2.R6
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The integer box `[-N,N]` with the origin removed. -/
def nzB (N : ℕ) : Finset ℤ := (Finset.Icc (-(N:ℤ)) (N:ℤ)).filter (fun x => x ≠ 0)

/-- The unweighted rectangular count (left-hand side of `rect_quad_count_unweighted`). -/
def UL (D S X Y : ℕ) : ℝ :=
  ∑ v1 ∈ Finset.Icc (-(S:ℤ)) (S:ℤ), ∑ v2 ∈ Finset.Icc (-(S:ℤ)) (S:ℤ),
    ∑ h1 ∈ Finset.Icc (-(X:ℤ)) (X:ℤ), ∑ h2 ∈ Finset.Icc (-(Y:ℤ)) (Y:ℤ),
      (if v1 ≠ 0 ∧ v2 ≠ 0 ∧ h1 ≠ 0 ∧ h2 ≠ 0 ∧ (D:ℤ) ∣ h1^2 * v1 - h2^2 * v2
          ∧ h1^2 * v1 - h2^2 * v2 ≠ 0 then (1:ℝ) else 0)

/-- The primitive-direction `star` sum: for each `(h₁,h₂)` we collect, over primitive directions
`(w₁,w₂)`, the `1/max`-weighted gcd of `D` with `w₁h₁² - w₂h₂²`. -/
def Star (D S X Y : ℕ) : ℝ :=
  ∑ h1 ∈ nzB X, ∑ h2 ∈ nzB Y, ∑ w1 ∈ nzB S, ∑ w2 ∈ nzB S,
    (if Nat.gcd w1.natAbs w2.natAbs = 1 ∧ w1 * h1^2 - w2 * h2^2 ≠ 0
      then (1:ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ)
        * (Nat.gcd D (w1 * h1^2 - w2 * h2^2).natAbs : ℝ)
      else 0)

end
end Work.FIArea2.R6
