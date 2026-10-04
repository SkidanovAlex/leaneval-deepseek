import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

/-- The two polarization (multilinearity-in-polarised-form) identities for `R4`. Both are
consequences of the four-fold multilinearity `R4_addᵢ` of `R4`; no curvature symmetry is used. -/
theorem R4_polarize (n : ℕ) (R : Curv4 n) (a b c d : Fin n → ℝ) :
    (R4 R a (b + c) d (b + c) = R4 R a b d b + R4 R a c d c + R4 R a b d c + R4 R a c d b) ∧
    (R4 R (a + c) b (a + c) d = R4 R a b a d + R4 R c b c d + R4 R a b c d + R4 R c b a d) := by
  constructor
  · simp only [R4_add₂, R4_add₄]
    ring
  · simp only [R4_add₁, R4_add₃]
    ring

end Work.Diff.Alg.PA
