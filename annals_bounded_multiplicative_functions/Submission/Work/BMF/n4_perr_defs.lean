import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # N4, Case B: the numerical parameters `Perr`, `E`, `R_m(q)`

The three numerical quantities of the N4/Case-B ("analytic range `q ≤ (log P)^{ℓ+4}`")
argument, for the *reachable* error exponent `1/12` of the Vinogradov–Korobov route
(see `Submission/Work/BMF/DESIGN.md`, "Addendum: V0 exponent": the twisted PNT is available
with error `x exp(−c (log x)^{1/12})`).

* `n4Perr C₁ c₁ P q = C₁ P exp(−c₁ (log P)^{1/12}) + C₁ ω(q)` is the error term of the
  pointwise prime-character bound (`n4_psum_of_window`).
* `n4Eee C₁ c₁ P = exp(c₁ (log P)^{1/12})/(C₁ log P)` is the crossover height
  (`C₁ π₀(P)/(1+|t|) ≤ n4Perr` for `|t| ≥ n4Eee`).
* `n4Rc m q = (2m)^{ω(q)}` is the number of characters `ψ` modulo `q` with `ψ^m = 1`,
  which governs the torsion contribution `n4Rc m q / φ(q)`.
-/

namespace Work.BMF

/-- The N4/Case-B error term `C₁ P exp(−c₁ (log P)^{1/12}) + C₁ ω(q)`. -/
noncomputable def n4Perr (C₁ c₁ P : ℝ) (q : ℕ) : ℝ :=
  C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ)) + C₁ * (q.primeFactors.card : ℝ)

/-- The N4/Case-B crossover height `E = exp(c₁ (log P)^{1/12})/(C₁ log P)`. -/
noncomputable def n4Eee (C₁ c₁ P : ℝ) : ℝ :=
  Real.exp (c₁ * Real.log P ^ (1 / 12 : ℝ)) / (C₁ * Real.log P)

/-- `R_m(q) = (2m)^{ω(q)}`, the number of characters `ψ` mod `q` with `ψ^m = 1`. -/
noncomputable def n4Rc (m : ℕ) (q : ℕ) : ℝ := ((2 * m : ℕ) : ℝ) ^ q.primeFactors.card

end Work.BMF
