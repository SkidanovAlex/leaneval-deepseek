import Mathlib
import Submission.CDTPlan.Interfaces

/-! # Theta series used in Area M (`Submission.CDTPlan.HauptFacts`)

In the *nome* variable `x` (with `‖x‖ < 1`) we introduce

* `T3 x = θ₃(x) = ∑' n : ℤ, x ^ (n^2)`,
* `T4 x = θ₄(x) = ∑' n : ℤ, (-1)^n x ^ (n^2)`,
* `T2 x = θ₂(x)/x^{1/4} = ∑' n : ℤ, x ^ (n(n+1))`,

together with the products

* `T2prod x = 2 ∏'_{n≥1}(1-x^{2n})(1+x^{2n})^2`,
* `T4prod x = ∏'_{n≥1}(1-x^{2n})(1-x^{2n-1})^2`,

and `U x = θ₃(x)^4 + θ₄(x)^4`.
-/

namespace Work.Haupt

noncomputable section

/-- `θ₃` at the nome `x`: `∑' n : ℤ, x ^ (n^2)`. -/
noncomputable def T3 (x : ℂ) : ℂ := ∑' n : ℤ, x ^ (n ^ 2)

/-- `θ₄` at the nome `x`: `∑' n : ℤ, (-1)^n x ^ (n^2)`. -/
noncomputable def T4 (x : ℂ) : ℂ := ∑' n : ℤ, (-1 : ℂ) ^ n * x ^ (n ^ 2)

/-- `∑' n : ℤ, x ^ (n(n+1))`; equals `θ₂(x)/x^{1/4}`. -/
noncomputable def T2 (x : ℂ) : ℂ := ∑' n : ℤ, x ^ (n * (n + 1))

/-- `U x = θ₃(x)^4 + θ₄(x)^4`, an even function of `x`. -/
noncomputable def U (x : ℂ) : ℂ := T3 x ^ 4 + T4 x ^ 4

/-- `2 ∏'_{n≥1} (1-x^{2n})(1+x^{2n})^2`, the product formula for `θ₂`. -/
noncomputable def T2prod (x : ℂ) : ℂ :=
  2 * ∏' n : ℕ, (1 - x ^ (2 * (n + 1))) * (1 + x ^ (2 * (n + 1))) ^ 2

/-- `∏'_{n≥1} (1-x^{2n})(1-x^{2n-1})^2`, the product formula for `θ₄`. -/
noncomputable def T4prod (x : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - x ^ (2 * (n + 1))) * (1 - x ^ (2 * n + 1)) ^ 2

/-- `∑' n : ℤ, Q ^ (n(n+1)/2)`; this is `T2 (√Q)`, i.e. `θ₂` of the nome `x = √Q` divided by `x^{1/4}`. -/
noncomputable def T2h (Q : ℂ) : ℂ := ∑' n : ℤ, Q ^ (n * (n + 1) / 2)

/-- The product `2 ∏'_{n≥1}(1-Q^n)(1+Q^n)^2`, the product formula for `T2h`. -/
noncomputable def T2hprod (Q : ℂ) : ℂ :=
  2 * ∏' n : ℕ, (1 - Q ^ (n + 1)) * (1 + Q ^ (n + 1)) ^ 2

/-- `UQ Q = U x` for `x^2 = Q`, i.e. `2 θ₃(Q)^4 + 2 Q θ₂(Q/·)^4` in the "quartic" normalisation. -/
noncomputable def UQ (Q : ℂ) : ℂ := 2 * T3 Q ^ 4 + 2 * Q * T2 Q ^ 4

end

end Work.Haupt
