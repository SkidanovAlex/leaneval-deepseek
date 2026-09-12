import ChallengeDeps
import Submission.Lorentzian.Port

open LorentzianPolynomials
open Finsupp Matrix MvPolynomial UpperHalfPlane

set_option autoImplicit false

namespace Submission

theorem theorem_2_25 (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) = L n d := by
  exact Submission.Lorentzian.theorem_2_25 n d hn

end Submission
