import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Tools

namespace Work.Engulf.E4Aux


/-- An affine equivalence `E n ≃ᵃ[ℝ] Pr (n - q - 1) q` forces `q + 1 ≤ n`.

Indeed, `Φ.linear` is a *linear* equivalence from the direction space `E n` onto the direction
space `Pr (n - q - 1) q`, so the two have the same `Module.finrank`, namely `n` on the left and
`(n - q - 1) + q + 1` on the right.  From `n = (n - q - 1) + (q + 1)` the inequality
`q + 1 ≤ n` is immediate (the truncated subtraction `n - q - 1` can only make the right side
smaller).  In particular there are no affine equivalences between a cube and a prism whose
"base dimension" `q` is too large. -/
theorem le_of_affineEquiv_prism {n q : ℕ}
    (Φ : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q) : q + 1 ≤ n := by
  have h : Module.finrank ℝ (PL.E n) = Module.finrank ℝ (Work.Engulf.Pr (n - q - 1) q) :=
    LinearEquiv.finrank_eq Φ.linear
  have h1 : Module.finrank ℝ (PL.E n) = n := by
    simp [PL.E]
  have h2 : Module.finrank ℝ (Work.Engulf.Pr (n - q - 1) q) = (n - q - 1) + q + 1 := by
    simp only [Work.Engulf.Pr, Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  omega

end Work.Engulf.E4Aux
