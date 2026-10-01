import Mathlib

/-!
# Definitions for the weighted Turán power-sum lemma

The Fejér polynomial `P(r,θ) = Σ_{j=1}^{J} (1 - j/(J+1)) r^j cos(jθ)` and its analytic
incarnation `Q(z) = Σ_{j=1}^{J} (1 - j/(J+1)) Re(z^j)` (so `Q(r e^{iθ}) = P(r,θ)`).
`fejerK J z u` is the combination `Q z + Q(zu)/2 + Q(z ū)/2` that appears when expanding
`Σ_j (1-j/(J+1)) (1 + cos(jθ₀)) Re s_j`.
-/

namespace Work.LinnikAreas.DhK

/-- Fejér weight `1 - j/(J+1)`. -/
noncomputable def fejerW (J j : ℕ) : ℝ := 1 - (j : ℝ) / (J + 1)

/-- `fejerQ J z = Σ_{j=1}^{J} (1 - j/(J+1)) Re(z^j)`. -/
noncomputable def fejerQ (J : ℕ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J, fejerW J j * (z ^ j).re

/-- The combination `Q z + Q(zu)/2 + Q(zū)/2`. -/
noncomputable def fejerK (J : ℕ) (z u : ℂ) : ℝ :=
  fejerQ J z + (1 / 2) * fejerQ J (z * u) + (1 / 2) * fejerQ J (z * star u)

end Work.LinnikAreas.DhK
