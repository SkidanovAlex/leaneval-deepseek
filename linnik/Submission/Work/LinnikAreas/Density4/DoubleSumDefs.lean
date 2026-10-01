import Mathlib

/-!
# Shared definitions for the double-sum error bound

These are the quantities appearing in `Work.LinnikAreas.Density4.double_sum_error_bound`.

For a modulus `r`, `Q ≥ 1` and `1 ≤ b ∣ r`:

* `dsebG r a = [a ⟂ r] · μ(a)/a²` — the summand of the infinite sum,
* `dsebF Q r a b = [a ⟂ r] · μ(a) μ(b) · ⌊Q/(a²b)⌋` — the summand of the double sum,
* `dsebM Q r a b = [a ⟂ r] · μ(a) μ(b) · (Q/(a²b))` — the corresponding "main term"
  summand, in which the floor has been removed.
-/

namespace Work.LinnikAreas.Density4

open Finset

noncomputable section

/-- `dsebG r a = [a ⟂ r] · μ(a)/a²`. -/
def dsebG (r a : ℕ) : ℝ :=
  if Nat.Coprime a r then (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2 else 0

/-- The summand of the double sum in `double_sum_error_bound`. -/
def dsebF (Q r a b : ℕ) : ℝ :=
  if Nat.Coprime a r then
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ)
      * ((Q / (a ^ 2 * b) : ℕ) : ℝ)
  else 0

/-- The "main term" summand, with the floor removed. -/
def dsebM (Q r a b : ℕ) : ℝ :=
  if Nat.Coprime a r then
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ)
      * ((Q : ℝ) / ((a : ℝ) ^ 2 * (b : ℝ)))
  else 0

/-- `Bsum r = ∑_{b ∣ r} μ(b)/b`. -/
def Bsum (r : ℕ) : ℝ :=
  ∑ b ∈ r.divisors, (ArithmeticFunction.moebius b : ℝ) / (b : ℝ)

/-- `SigHalf r = ∑_{d ∣ r} 1/√d`, the error-scale weight. -/
def SigHalf (r : ℕ) : ℝ :=
  ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)

end

end Work.LinnikAreas.Density4
