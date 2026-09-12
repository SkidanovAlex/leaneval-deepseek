import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv
import Submission.Sec3H_lbounds
import Submission.Sec3H_origin
import Submission.Sec3H_intervals
import Submission.Sec3_c_bridge
import Submission.Sec3_c_expand
import Submission.ArcFamily
import Submission.Sec3Base
import Submission.RunFamily

/-! Section 3, Theorem 2.3 of the paper (quadrant family for the cosine polynomial). -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3

/-- Theorem 2.3 (quadrant).  Existence of the suitable family with coverage. -/
theorem cosine_family (t q : ℕ) (ht : Odd t)
    (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) (hhi : q ≤ 2 ^ (t + 60)) :
    ∃ (N : ℕ) (F : Family.Quad q N),
      (N : ℝ) ≤ (q : ℝ) / 2 ^ 41 ∧
      (∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) →
        θ ∈ F.union ∨ goodCellBound t q ≤ |c t θ|) := by
  exact family_core t q ht hq0 hlo

end Sec3
end Submission
