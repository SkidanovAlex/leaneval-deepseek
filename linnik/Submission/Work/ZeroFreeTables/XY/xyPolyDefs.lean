/-
# ZeroFreeTables — xyPolyDefs

The explicit polynomial form of HB Lemma 7.2's test function with `λ = 4/3`
(support `[0, 3/2]`) and the closed form of its moments
`xyM j = ∫_0^{3/2} t^j · xyP t`.

These two definitions are the vocabulary of the numerical core of the order-2
`λ₁`-estimate (`Work.ZeroFreeTables.XY.xyMainLt`): on `[0, 3/2]` the test function
`xyT.f` coincides with `xyP`, and the integrals of `xyP` against the Taylor
polynomials of `exp` are rational combinations of the `xyM j`.
-/
import Mathlib

noncomputable section
namespace Work.ZeroFreeTables.XY

/-- On `[0, 3/2]`, HB Lemma 7.2's test function with `λ = 4/3` equals this quintic:
the expansion of `(λ/30)(2-λt)³(4+6λt+λ²t²)` at `λ = 4/3`. -/
def xyP (t : ℝ) : ℝ := 64/45 - (256/81)*t^2 + (512/243)*t^3 - (2048/10935)*t^5

/-- The `j`-th moment `∫_0^{3/2} t^j · xyP t`, in closed form. -/
def xyM (j : ℕ) : ℝ :=
  (64/45)*(3/2)^(j+1)/(j+1) - (256/81)*(3/2)^(j+3)/(j+3)
    + (512/243)*(3/2)^(j+4)/(j+4) - (2048/10935)*(3/2)^(j+6)/(j+6)

end Work.ZeroFreeTables.XY
